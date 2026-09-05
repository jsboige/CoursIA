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

    # Aggregate per horizon (cross-seed).
    aggregated: list[dict] = []
    for (coin, h), grp in groups.items():
        rows_h = [r for r in audit_rows if r["coin"] == coin and r["horizon"] == h]
        if not rows_h:
            continue
        all_el = np.concatenate([_series(r, "lstm_errors") for r in grp])
        all_eh = np.concatenate([_series(r, "har_errors") for r in grp])
        reduction_pcts = [r["mse_reduction_pct"] for r in rows_h if np.isfinite(r["mse_reduction_pct"])]
        mean_reduction = float(np.mean(reduction_pcts)) if reduction_pcts else float("nan")
        edge_std_pct = float(np.nanstd(reduction_pcts)) if len(reduction_pcts) > 1 else 0.0
        edge_pct = -mean_reduction if np.isfinite(mean_reduction) else float("nan")
        n_beaten_cen = sum(1 for r in rows_h if r["dm_cen_verdict"] == "BEATEN BY baseline")
        n_rows = len(rows_h)
        # Pooled centered DM across seeds for a coarse read.
        if len(all_el) >= 10 and len(all_eh) >= 10:
            dm_pooled = bias_metrics._dm_centered_mse(all_el, all_eh, h)
        else:
            dm_pooled = {"dm_stat": float("nan"), "dm_pvalue": float("nan"),
                         "dm_verdict": "insufficient"}
        # Verdict: raw edge may look like a BEATS, but if any centered DM says
        # BEATEN (or the pooled centered DM is BEATEN at p<0.05), the raw BEATS
        # is bias-carried -> NO BEATS on precision.
        if n_beaten_cen > 0:
            verdict = "BIAS-CARRIED (NO BEATS on precision)"
        elif (np.isfinite(dm_pooled["dm_pvalue"]) and dm_pooled["dm_pvalue"] < 0.05
              and dm_pooled["dm_stat"] > 0):
            verdict = "BIAS-CARRIED (NO BEATS on precision)"
        elif np.isfinite(edge_pct) and edge_pct >= 2.0 * edge_std_pct:
            verdict = "BEATS"
        else:
            verdict = "INCONCLUSIVE"
        aggregated.append({
            "coin": coin,
            "horizon": h,
            "n_seeds": n_rows,
            "mean_reduction_pct": mean_reduction,
            "edge_pct": edge_pct,
            "edge_std_pct": edge_std_pct,
            "dm_cen_pooled_stat": dm_pooled["dm_stat"],
            "dm_cen_pooled_pvalue": dm_pooled["dm_pvalue"],
            "dm_cen_pooled_verdict": dm_pooled["dm_verdict"],
            "n_beaten_cen": n_beaten_cen,
            "verdict": verdict,
        })

    results = {
        "model": "Log-LSTM RV vs HAR Classic (BTC-USD, hidden=64, refit=110)",
        "audit": "MSE = bias^2 + variance; centered DM (precision jambe)",
        "loss_fn": "mse",
        "seeds": [r["seed"] for r in audit_rows],
        "rows": audit_rows,
        "aggregated": aggregated,
        "verdict_note": (
            "The raw mse_reduction_pct is negative (LSTM lowers MSE), but the "
            "centered DM annihilates each model's own bias. A positive centered "
            "DM statistic means the LSTM has WORSE precision (higher variance) "
            "than HAR once the HAR bias is removed."
        ),
    }
    out_path = rdir / "results_audit.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"[audit] wrote {out_path}")
    for a in aggregated:
        print(f"  h={a['horizon']}: mean_red={a['mean_reduction_pct']:+.1f}% "
              f"edge={a['edge_pct']:+.1f}% (sigma={a['edge_std_pct']:.2f}) "
              f"DMcen_pooled={a['dm_cen_pooled_stat']:+.3f} p={a['dm_cen_pooled_pvalue']:.4f} "
              f"{a['dm_cen_pooled_verdict']} beaten_cen={a['n_beaten_cen']}/{a['n_seeds']} -> {a['verdict']}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else
                  "MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/results/m15_lstm_rv_h64_bias"))
