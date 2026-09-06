"""Bias-audit for the M15 LSTM-RV run (issue #12734).

Reads the checkpoint.jsonl written by m15_lstm_rv.py (which persists raw
forecast errors + OOS bias since #12745) and decomposes MSE = bias^2 +
variance per model, then runs the centered DM (`bias_metrics._dm_centered_mse`,
the precision jambe). The question it answers: does the raw-mse "BEATS"
survive the bias, or is it carried by it?

The centered DM annihilates each model's own bias, so its statistic measures
only the variance (precision) differential. If the centered DM says the LSTM
is BEATEN by the baseline while the raw mse_reduction said the LSTM wins, then
the edge is bias-carried (exactly the #10938 / #10961 case class). That is the
verdict this audit makes explicit.

Reuses scripts/bias_metrics.py (shared torch-free module, #14363/#14456).
"""
from __future__ import annotations

import json
import sys
from collections import OrderedDict
from pathlib import Path

import numpy as np

import bias_metrics  # noqa: E402


def _series(r: dict, key: str) -> np.ndarray:
    v = r.get(key, [])
    if not isinstance(v, list) or not v:
        return np.array([], dtype=float)
    return np.asarray([float(x) for x in v if np.isfinite(float(x))], dtype=float)


def _raw_verdict(r: dict) -> str:
    return r.get("dm_verdict", "N/A")


def _precision_verdict(
    pvalues: list[float], stats: list[float], edge_pct: float, edge_std_pct: float
) -> tuple[str, float, float, str]:
    """§C/#12734 cross-seed decision on the centered (precision) DM jambe.

    The decision variable is the cross-seed median per-seed p-value -- not a
    single significant seed (a 1/4 BEATEN must not flip the horizon) and not
    the pooled concat (which repeats the same HAR series across seeds and
    understates uncertainty). Direction is the sign of the median centered DM
    statistic: positive means the LSTM's precision is worse once each model's
    own bias is annihilated, i.e. the raw-mse edge is bias-carried.

    Returns (verdict, dm_cen_p_median, dm_cen_median_stat, direction).
    """
    dm_cen_p_median = float(np.nanmedian(pvalues)) if pvalues else float("nan")
    dm_cen_median_stat = float(np.nanmedian(stats)) if stats else float("nan")
    direction = "lstm_worse" if dm_cen_median_stat > 0 else "lstm_better"
    if np.isfinite(dm_cen_p_median) and dm_cen_p_median < 0.05:
        if direction == "lstm_worse":
            verdict = "NO BEATS"  # precision jambe significant against LSTM -> bias-carried
        elif np.isfinite(edge_pct) and edge_pct >= 2.0 * edge_std_pct:
            verdict = "BEATS"
        else:
            verdict = "INCONCLUSIVE"
    else:
        verdict = "INCONCLUSIVE"
    return verdict, dm_cen_p_median, dm_cen_median_stat, direction


def _aggregate_horizon(
    rows_h: list[dict], raw_grp: list[dict], coin: str, h: int
) -> dict:
    n_seeds = len(rows_h)
    reduction_pcts = [r["mse_reduction_pct"] for r in rows_h if np.isfinite(r["mse_reduction_pct"])]
    mean_reduction = float(np.mean(reduction_pcts)) if reduction_pcts else float("nan")
    edge_std_pct = float(np.nanstd(reduction_pcts)) if len(reduction_pcts) > 1 else 0.0
    edge_pct = -mean_reduction if np.isfinite(mean_reduction) else float("nan")
    pvalues = [r["dm_cen_pvalue"] for r in rows_h if np.isfinite(r["dm_cen_pvalue"])]
    stats = [r["dm_cen_stat"] for r in rows_h if np.isfinite(r["dm_cen_stat"])]
    verdicts = [r["dm_cen_verdict"] for r in rows_h]
    n_beaten = sum(1 for v in verdicts if "BEATEN" in v)
    n_beats = sum(1 for v in verdicts if "BEATS" in v and "BEATEN" not in v)
    n_inconclusive = sum(1 for v in verdicts if v == "INCONCLUSIVE")
    verdict, dm_cen_p_median, dm_cen_median_stat, direction = _precision_verdict(
        pvalues, stats, edge_pct, edge_std_pct,
    )
    # Pooled centered DM across seeds: DIAGNOSTIC ONLY (not decision). It
    # concatenates the same HAR series, so it is not four independent
    # observations and must not carry the verdict.
    all_el = np.concatenate([_series(r, "lstm_errors") for r in raw_grp])
    all_eh = np.concatenate([_series(r, "har_errors") for r in raw_grp])
    if len(all_el) >= 10 and len(all_eh) >= 10:
        dm_pooled = bias_metrics._dm_centered_mse(all_el, all_eh, h)
    else:
        dm_pooled = {"dm_stat": float("nan"), "dm_pvalue": float("nan"),
                     "dm_verdict": "insufficient"}
    return {
        "coin": coin,
        "horizon": h,
        "n_seeds": n_seeds,
        "mean_reduction_pct": mean_reduction,
        "edge_pct": edge_pct,
        "edge_std_pct": edge_std_pct,
        "dm_cen_p_median": dm_cen_p_median,
        "dm_cen_median_stat": dm_cen_median_stat,
        "dm_cen_direction": direction,
        "n_beaten_cen": n_beaten,
        "n_beats_cen": n_beats,
        "n_inconclusive_cen": n_inconclusive,
        "dm_cen_pooled_stat": dm_pooled["dm_stat"],
        "dm_cen_pooled_pvalue": dm_pooled["dm_pvalue"],
        "dm_cen_pooled_verdict": dm_pooled["dm_verdict"],
        "verdict": verdict,
    }


def main(results_dir: str) -> int:
    rdir = Path(results_dir)
    ckpt = rdir / "checkpoint.jsonl"
    if not ckpt.exists():
        print(f"[no checkpoint] {ckpt}")
        return 1
    rows = [json.loads(l) for l in ckpt.read_text().splitlines() if l.strip()]
    if not rows:
        print("[no rows] empty checkpoint")
        return 1

    groups: dict[tuple, list[dict]] = OrderedDict()
    for r in rows:
        groups.setdefault((r["coin"], r["horizon"]), []).append(r)

    audit_rows: list[dict] = []
    for (coin, h), grp in groups.items():
        for r in grp:
            el = _series(r, "lstm_errors")
            eh = _series(r, "har_errors")
            d_l = bias_metrics._mse_decomposition(el)
            d_h = bias_metrics._mse_decomposition(eh)
            dm_cen = bias_metrics._dm_centered_mse(el, eh, h)
            audit_rows.append({
                "coin": coin,
                "horizon": h,
                "seed": r["seed"],
                "mse_lstm": d_l["mse"],
                "mse_har": d_h["mse"],
                "mse_reduction_pct": r.get("mse_reduction_pct", float("nan")),
                "lstm_bias_oos": r.get("lstm_bias_oos", float("nan")),
                "lstm_variance": d_l["variance"],
                "har_bias_oos": r.get("har_bias_oos", float("nan")),
                "har_variance": d_h["variance"],
                "dm_cen_stat": dm_cen["dm_stat"],
                "dm_cen_pvalue": dm_cen["dm_pvalue"],
                "dm_cen_verdict": dm_cen["dm_verdict"],
                "raw_dm_verdict": _raw_verdict(r),
                "n_obs": len(el),
            })

    # Aggregate per horizon (cross-seed). Decision jambe = dm_cen_p_median
    # (see _precision_verdict); pooled DM is diagnostic only.
    aggregated: list[dict] = []
    for (coin, h), grp in groups.items():
        rows_h = [r for r in audit_rows if r["coin"] == coin and r["horizon"] == h]
        if not rows_h:
            continue
        aggregated.append(_aggregate_horizon(rows_h, grp, coin, h))

    results = {
        "model": "Log-LSTM RV vs HAR Classic (BTC-USD, hidden=64, refit=110)",
        "audit": "MSE = bias^2 + variance; centered DM (precision jambe)",
        "loss_fn": "mse",
        "seeds": [r["seed"] for r in audit_rows],
        "rows": audit_rows,
        "aggregated": aggregated,
        "verdict_note": (
            "The raw mse_reduction_pct is negative (LSTM lowers MSE), but the "
            "centered DM annihilates each model's own bias. The decision jambe "
            "is the cross-seed median per-seed centered-DM p-value "
            "(dm_cen_p_median, §C/#12734): only a significant precision jambe "
            "against the LSTM (p<0.05, direction lstm_worse) yields NO BEATS. "
            "The pooled DM is reported as diagnostic only: it concatenates the "
            "same HAR series across seeds and is not four independent temporal "
            "observations. A single significant seed (1/4 BEATEN) never flips "
            "the horizon verdict."
        ),
    }
    out_path = rdir / "results_audit.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"[audit] wrote {out_path}")
    for a in aggregated:
        print(f"  h={a['horizon']}: mean_red={a['mean_reduction_pct']:+.1f}% "
              f"edge={a['edge_pct']:+.1f}% (sigma={a['edge_std_pct']:.2f}) "
              f"DMcen_p_median={a['dm_cen_p_median']:.4f} "
              f"(dir={a['dm_cen_direction']}, beaten={a['n_beaten_cen']}/{a['n_seeds']}) "
              f"DMcen_pooled(nd)={a['dm_cen_pooled_pvalue']:.4f} -> {a['verdict']}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else
                  "MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/results/m15_lstm_rv_h64_bias"))
