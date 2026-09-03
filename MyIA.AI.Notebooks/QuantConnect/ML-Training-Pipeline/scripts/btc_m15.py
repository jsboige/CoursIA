"""BTC-only wrapper for M15 LSTM-RV: HAR-debiased + DM-on-centered-errors (issue #12734).

Slice 2/2 of #12734. Companion to btc_vol.py (slice 1/2 — M4 DLinear-vol).

Strategy: M15 BTC cannot be run post-hoc (the legacy m15_lstm_rv.py sweep
sweep the verdict only, never persisted har_bias_oos nor the raw
predictions). To make a HAR-debiased + DM-on-centered-errors re-validation
possible without re-fitting the LSTM, we patch m15_lstm_rv.py so the
JSON contains har_bias_oos + the raw har/lstm errors per combo (see
`evaluate_one_combo` patch in PR #12743).

The full M15 BTC sweep is heavy (~50 min/combo, 12 combos ~10 h). This
wrapper runs the SHAPE of the analysis — single combo (1 horizon × 1
seed) — to validate the pipeline end-to-end. The full re-run is
dispatched to the next cycle (see PR body for the command + acceptance).

Helpers `_mse_decomposition` and `_dm_centered_mse` now live in
`bias_metrics.py`, extracted from `btc_vol.py` (issue #14363).
"""
from __future__ import annotations

import json
import math
import subprocess
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd

from bias_metrics import _dm_centered_mse, _mse_decomposition  # noqa: E402


# --- main analysis --------------------------------------------------------


def analyze_one_combo(row: dict) -> dict:
    """Apply the HAR-debiased + DM-on-centered-errors analysis to one combo row.

    The row must carry `har_preds`, `lstm_preds`, `target`, `har_errors`,
    `lstm_errors`, `har_bias_oos`. If `har_preds`/`lstm_preds` are not
    persisted (legacy JSON), the wrapper falls back to computing errors
    from `mse_har`, `mse_lstm`, `har_bias_oos` and the `mse_reduction_pct`
    approximation -- which is degenerate for the variance ratio. The
    patched run (PR #12743) populates all required fields.
    """
    h = int(row["horizon"])
    seed = int(row["seed"])
    har_bias_oos = float(row.get("har_bias_oos", float("nan")))
    mse_har_raw = float(row.get("mse_har", float("nan")))
    mse_lstm = float(row.get("mse_lstm", float("nan")))

    # If raw errors are persisted (PR #12743 patch), use them.
    if "har_errors" in row and "lstm_errors" in row:
        har_errors = np.asarray(row["har_errors"], dtype=float)
        lstm_errors = np.asarray(row["lstm_errors"], dtype=float)
    else:
        # Legacy JSON: cannot reconstruct the per-day error series from
        # aggregates. We mark the combo as non-analyzable; the next-cycle
        # rerun will populate the persisted fields.
        return {
            "horizon": h,
            "seed": seed,
            "analyzable": False,
            "reason": "har_errors/lstm_errors not persisted (legacy JSON)",
            "har_bias_oos": har_bias_oos,
            "mse_har_raw": mse_har_raw,
            "mse_lstm": mse_lstm,
        }

    # Centered DM: pure variance comparison
    dm_centered = _dm_centered_mse(lstm_errors, har_errors - har_bias_oos, horizon=h)

    # MSE decomposition
    har_errors_debiased = har_errors - har_bias_oos
    lstm_decomp = _mse_decomposition(lstm_errors)
    har_decomp_raw = _mse_decomposition(har_errors)
    har_decomp_debiased = _mse_decomposition(har_errors_debiased)

    # Bias-share diagnostic (the same one btc_vol.py publishes for M4).
    var_ratio = float(lstm_decomp["variance"] / har_decomp_debiased["variance"]) \
        if har_decomp_debiased["variance"] > 0 else float("nan")
    har_bias_share = float(har_decomp_debiased["bias_sq"] / har_decomp_debiased["mse"]) \
        if har_decomp_debiased["mse"] > 0 else float("nan")

    return {
        "horizon": h,
        "seed": seed,
        "analyzable": True,
        "har_bias_oos": har_bias_oos,
        "mse_lstm_raw": mse_lstm,
        "mse_har_raw": mse_har_raw,
        "mse_har_debiased": float(np.mean(har_errors_debiased ** 2)),
        "mse_reduction_pct_vs_debiased_har": float(
            (float(np.mean(har_errors_debiased ** 2)) - mse_lstm)
            / float(np.mean(har_errors_debiased ** 2)) * 100
        ) if float(np.mean(har_errors_debiased ** 2)) > 0 else float("nan"),
        "dm_centered": dm_centered,
        "lstm_decomp": lstm_decomp,
        "har_decomp_raw": har_decomp_raw,
        "har_decomp_debiased": har_decomp_debiased,
        "var_ratio_lstm_over_har_debiased": var_ratio,
        "har_bias_share_of_mse_debiased": har_bias_share,
    }


def aggregate_verdicts(analyzed: list[dict]) -> list[dict]:
    """Per-horizon verdict using §C conjunction on the centered DM."""
    by_h: dict[int, list[dict]] = {}
    for a in analyzed:
        if not a.get("analyzable", False):
            continue
        by_h.setdefault(int(a["horizon"]), []).append(a)

    aggregated = []
    for h, rows in sorted(by_h.items()):
        edges = np.array([r["mse_reduction_pct_vs_debiased_har"] for r in rows], dtype=float)
        dm_ps = np.array([r["dm_centered"]["dm_pvalue"] for r in rows], dtype=float)
        edge_mean = float(np.nanmean(edges))
        edge_std = float(np.nanstd(edges)) if len(edges) > 1 else 0.0
        dm_p_med = float(np.nanmedian(dm_ps))
        # Dominance guard: any "BEATEN BY baseline" -> NO BEATS
        n_beaten = sum(
            1 for r in rows if "BEATEN" in r["dm_centered"]["dm_verdict"]
        )
        if n_beaten > 0:
            verdict = "NO BEATS"
        elif (
            np.isfinite(edge_mean)
            and np.isfinite(edge_std)
            and edge_std > 0
            and edge_mean >= 2.0 * edge_std
            and dm_p_med < 0.05
        ):
            verdict = "BEATS"
        else:
            verdict = "INCONCLUSIVE"
        aggregated.append({
            "horizon": h,
            "n_seeds": len(rows),
            "edge_reduction_pct": edge_mean,
            "edge_std_pct": edge_std,
            "dm_centered_p_median": dm_p_med,
            "n_beaten": n_beaten,
            "var_ratio_lstm_over_har_debiased": float(np.nanmean([
                r["var_ratio_lstm_over_har_debiased"] for r in rows
            ])),
            "har_bias_share_of_mse_debiased": float(np.nanmean([
                r["har_bias_share_of_mse_debiased"] for r in rows
            ])),
            "verdict_sc": verdict,
        })
    return aggregated


def run_smoke(
    coin: str = "BTC-USD",
    horizon: int = 1,
    seed: int = 0,
    refit_every: int = 110,
    hidden_size: int = 32,
    loss_fn: str = "mse",
    out_json: Path = Path(
        "scripts/results/m15_lstm_rv_btc_sc_debiased_recentered_smoke.json"
    ),
) -> dict:
    """Run a single M15 BTC combo and apply the HAR-debiased + DM-centered analysis.

    `refit_every=110` is the §C-cadence used for M4 (5 retrains/combo instead
    of the default 22d → 85 retrains). On RTX 3070 8GB, h=1 seed=0 at h=32
    fits in ~30-50 min. The full 12-combo sweep is dispatched next cycle.
    """
    t0 = time.time()
    cmd = [
        sys.executable,
        "scripts/m15_lstm_rv.py",
        "--coins", coin,
        "--horizons", str(horizon),
        "--seeds", str(seed),
        "--refit-every", str(refit_every),
        "--hidden-size", str(hidden_size),
        "--loss-fn", loss_fn,
    ]
    print(f"[btc_m15] running: {' '.join(cmd)}")
    proc = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
    print(proc.stdout[-2000:] if proc.stdout else "")
    if proc.returncode != 0:
        print(f"[btc_m15] FAILED (rc={proc.returncode}): {proc.stderr[-1000:]}")
        return {"ok": False, "returncode": proc.returncode,
                "stderr_tail": proc.stderr[-500:]}

    # Locate the latest run results.json (m15 writes to results/<coin>/results.json)
    candidates = sorted(
        Path("scripts/results").rglob("results.json"),
        key=lambda p: p.stat().st_mtime,
        reverse=True,
    )
    if not candidates:
        return {"ok": False, "returncode": -1, "reason": "no results.json found"}
    latest = candidates[0]
    with open(latest, encoding="utf-8") as f:
        data = json.load(f)
    combos = data.get("combos", [])
    # Filter to the requested combo
    target = [c for c in combos
              if c["coin"] == coin and c["horizon"] == horizon and c["seed"] == seed]
    if not target:
        return {"ok": False, "returncode": -1, "reason": "no combo matching requested (coin, h, seed)"}
    row = target[0]

    # Check that the patch populated har_errors/lstm_errors.
    if "har_errors" not in row or "lstm_errors" not in row:
        # Persist what we have, mark non-analyzable, document.
        out = {
            "ok": True,
            "analyzable": False,
            "reason": "patch not active in the m15 run -- rerun after PR #12743 merge",
            "row": {k: v for k, v in row.items()
                    if k not in ("har_preds", "lstm_preds", "target")},
            "results_json": str(latest),
            "elapsed_s": time.time() - t0,
        }
        out_json.parent.mkdir(parents=True, exist_ok=True)
        with open(out_json, "w", encoding="utf-8") as f:
            json.dump(out, f, indent=2, default=str)
        print(f"[btc_m15] patch not active -> wrote diagnostic {out_json}")
        return out

    analyzed = analyze_one_combo(row)
    aggregated = aggregate_verdicts([analyzed])

    out = {
        "ok": True,
        "analyzable": True,
        "coin": coin,
        "horizon": horizon,
        "seed": seed,
        "refit_every": refit_every,
        "hidden_size": hidden_size,
        "loss_fn": loss_fn,
        "results_json": str(latest),
        "analyzed_rows": [analyzed],
        "aggregated": aggregated,
        "elapsed_s": time.time() - t0,
    }
    out_json.parent.mkdir(parents=True, exist_ok=True)
    with open(out_json, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, default=str)
    print(f"[btc_m15] wrote {out_json} (elapsed {out['elapsed_s']:.0f}s)")
    return out


def main():
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument("--coin", default="BTC-USD")
    p.add_argument("--horizon", type=int, default=1)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--refit-every", type=int, default=110)
    p.add_argument("--hidden-size", type=int, default=32)
    p.add_argument("--loss-fn", default="mse")
    p.add_argument(
        "--out-json",
        type=Path,
        default=Path("scripts/results/m15_lstm_rv_btc_sc_debiased_recentered_smoke.json"),
    )
    args = p.parse_args()
    out = run_smoke(
        coin=args.coin,
        horizon=args.horizon,
        seed=args.seed,
        refit_every=args.refit_every,
        hidden_size=args.hidden_size,
        loss_fn=args.loss_fn,
        out_json=args.out_json,
    )
    if not out.get("ok"):
        sys.exit(1)
    if out.get("analyzable"):
        for a in out.get("aggregated", []):
            print(
                f"[btc_m15] h={a['horizon']:>3} verdict={a['verdict_sc']} "
                f"edge={a['edge_reduction_pct']:+.2f}% (σ={a['edge_std_pct']:.2f}) "
                f"dm_p_med={a['dm_centered_p_median']:.2e} "
                f"var_ratio={a['var_ratio_lstm_over_har_debiased']:.4f}"
            )


if __name__ == "__main__":
    main()
