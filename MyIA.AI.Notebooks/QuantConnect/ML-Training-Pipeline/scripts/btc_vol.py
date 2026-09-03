"""BTC-only orchestrator for the M4 DLinear-vol keeper re-validation (#12734).

This script wraps `dlinear_vol.py` (which is the multi-coin core) with a BTC-only
scope and a HAR-debiased + error-recentered mode (#12734 acceptance):

  - **HAR baseline de-biased**: the OOS bias `har_bias_oos` measured on test
    is subtracted from HAR forecasts (`pred_hat - bias_oos`). This is the
    HAR-baseline adjustment #12684 would normalise; we apply it here on BTC
    specifically because the ticket asks for the **hors-biais** measure.
  - **Error-recentered DM**: the DM differential is computed on
    `e_a - mean(e_a)` and `e_b - mean(e_b)` (errors centered by mean per
    forecast), with `loss_fn="mse"`. Centering the errors annihilates the
    bias component (`mean(loss_fn=linear)` becomes zero), and the resulting
    `d_mean` measures the variance differential only -- the "DM on
    precision" that #10961/#10956 cite as the §C precision jambe.

The decomposition `MSE = bias^2 + variance` is reported per horizon for
both DLinear and HAR (debiased). This is the diagnostic #12695 documents
on ETF, applied to BTC here.

The script is BTC-only by design: the other coins in the original
`dlinear_vol.py` run lack the data depth (~2278 RV days for BTC vs ~725
for the yfinance coins) to sustain a §C verdict.

References: #12734, #12695 (ETF sibling), #10938 (HAR bias measure), #11010
(amended §C: mse jambe is the precision verdict), #10961 (DM on centered
errors = variance differential).
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

# Local imports (paths-relative so the script runs from ML-Training-Pipeline/).
sys.path.insert(0, str(Path(__file__).parent))

import numpy as np
import pandas as pd

from intraday_loader import load_bitstamp_btc, hourly_log_returns  # noqa: E402
from realized_variance import (  # noqa: E402
    daily_realized_variance,
    realized_variance_to_log,
)
from dlinear_vol import (  # noqa: E402
    walk_forward_har,
    walk_forward_dlinear,
)


def _mse_decomposition(errors: np.ndarray) -> dict:
    """Decompose MSE of a forecast into bias^2 + variance on the error support."""
    if errors is None or len(errors) == 0:
        return {"mse": float("nan"), "bias_sq": float("nan"), "variance": float("nan")}
    bias = float(np.mean(errors))
    variance = float(np.var(errors, ddof=0))
    return {
        "mse": float(np.mean(errors ** 2)),
        "bias_sq": bias ** 2,
        "variance": variance,
    }


def _dm_centered_mse(
    errors_a: np.ndarray, errors_b: np.ndarray, horizon: int
) -> dict:
    """DM test on errors centered by their own mean, with loss_fn='mse'.

    Centering annihilates the bias component (`mean(e_a - mean(e_a)) = 0`),
    so the resulting `d_mean` measures only the variance differential. The
    "DM on precision" jambe that #10961 documents is exactly this.
    """
    from dm_test import dm_verdict as dm_verdict_fn

    e_a = np.asarray(errors_a, dtype=float)
    e_b = np.asarray(errors_b, dtype=float)
    if e_a.shape != e_b.shape:
        return {"dm_stat": float("nan"), "dm_pvalue": float("nan"), "dm_verdict": "SHAPE_MISMATCH"}
    n = len(e_a)
    if n < 10:
        return {"dm_stat": float("nan"), "dm_pvalue": float("nan"), "dm_verdict": "INSUFFICIENT_DATA"}

    centered_a = e_a - np.mean(e_a)
    centered_b = e_b - np.mean(e_b)
    res = dm_verdict_fn(centered_a, centered_b, horizon=horizon, loss_fn="mse")
    return {
        "dm_stat": float(res["dm_statistic"]),
        "dm_pvalue": float(res["p_value"]),
        "dm_verdict": str(res["verdict"]),
        "mean_loss_diff": float(res["mean_loss_diff"]),
    }


def _dm_uncentered_mse(
    errors_a: np.ndarray, errors_b: np.ndarray, horizon: int
) -> dict:
    """DM test on RAW (non-centered) errors, with loss_fn='mse'.

    This is the sanity leg reproducing the #11011 keeper measure: the MSE
    differential on untouched errors, bias included. It is deliberately NOT
    `_dm_centered_mse`: centering subtracts each series' own mean, which
    annihilates any constant offset between two error series. Since the
    de-biased HAR errors differ from the raw ones by exactly the constant
    `har_bias_oos`, routing this leg through the centered helper makes it
    return the *same* statistic as the verdict leg -- a control that cannot
    go red (#14362). Same return shape as `_dm_centered_mse`.
    """
    from dm_test import dm_verdict as dm_verdict_fn

    e_a = np.asarray(errors_a, dtype=float)
    e_b = np.asarray(errors_b, dtype=float)
    if e_a.shape != e_b.shape:
        return {"dm_stat": float("nan"), "dm_pvalue": float("nan"), "dm_verdict": "SHAPE_MISMATCH"}
    n = len(e_a)
    if n < 10:
        return {"dm_stat": float("nan"), "dm_pvalue": float("nan"), "dm_verdict": "INSUFFICIENT_DATA"}

    res = dm_verdict_fn(e_a, e_b, horizon=horizon, loss_fn="mse")
    return {
        "dm_stat": float(res["dm_statistic"]),
        "dm_pvalue": float(res["p_value"]),
        "dm_verdict": str(res["verdict"]),
        "mean_loss_diff": float(res["mean_loss_diff"]),
    }


def run_btc_debiased_recentered(
    horizons: list[int],
    seeds: list[int],
    seq_len: int = 22,
    n_splits: int = 5,
    refit_every: int = 22,
    epochs: int = 100,
    decompose: bool = False,
    coin: str = "BTC-USD",
) -> dict:
    """Run the BTC keeper with HAR-debiased + error-recentered DM (#12734)."""
    btc = load_bitstamp_btc()
    rets = hourly_log_returns(btc)
    rv = daily_realized_variance(rets)
    log_rv = realized_variance_to_log(rv)
    log_rv_arr = log_rv.values.astype(float)
    rv_idx = rv.index

    print(f"[btc_vol] {coin}: {len(rv)} RV days, log_rv var={log_rv.var():.4f}")

    rows: list[dict] = []
    for h in horizons:
        # HAR baseline (deterministic), then de-bias.
        har_out = walk_forward_har(rv, horizon=h, n_splits=n_splits, refit_every=refit_every)
        har_mse_raw = har_out["aggregate_mse_logrv"]
        har_fc = har_out["forecasts"]
        har_tg = har_out["targets"]
        har_errors = (har_fc - har_tg).dropna().values
        har_bias_oos = float(np.mean(har_errors)) if len(har_errors) else float("nan")

        # HAR de-biased: subtract OOS bias from forecasts, recompute MSE.
        har_fc_debiased = har_fc - har_bias_oos
        # Align forecasts and targets on shared index (dropna after subtraction).
        df_h = pd.concat([har_fc_debiased.rename("fc"), har_tg.rename("tg")], axis=1).dropna()
        har_errors_debiased = (df_h["fc"] - df_h["tg"]).values
        har_mse_debiased = float(np.mean(har_errors_debiased ** 2)) if len(har_errors_debiased) else float("nan")

        har_decomp_raw = _mse_decomposition(har_errors)
        har_decomp_debiased = _mse_decomposition(har_errors_debiased)

        print(f"  h={h} HAR raw MSE={har_mse_raw:.5f} -> debiased MSE={har_mse_debiased:.5f} "
              f"(bias_oos={har_bias_oos:+.5f})")

        for seed in seeds:
            dl_out = walk_forward_dlinear(
                log_rv_arr, rv_idx,
                seq_len=seq_len,
                horizon=h,
                n_splits=n_splits,
                refit_every=refit_every,
                epochs=epochs,
                decompose=decompose,
                seed=seed,
                debias=False,  # we compare raw DLinear vs debiased HAR -- this is the §C interpretation
            )
            dl_mse = dl_out["aggregate_mse_logrv"]
            dl_fc = dl_out["forecasts"]
            dl_tg = dl_out["targets"]
            dl_errors = (dl_fc - dl_tg).dropna().values

            dl_decomp = _mse_decomposition(dl_errors)

            # Verdict leg: DM on CENTERED errors (variance differential),
            # DLinear raw vs HAR DEBIASED. This is the jambe that carries §C.
            min_len = min(len(dl_errors), len(har_errors_debiased))
            dm_centered = _dm_centered_mse(
                dl_errors[:min_len], har_errors_debiased[:min_len], horizon=h
            )
            # Sanity leg: DM NON centered, DLinear raw vs HAR RAW -- the #11011
            # keeper measure. It must NOT be routed through `_dm_centered_mse`:
            # `har_errors_debiased = har_errors - har_bias_oos` differs from
            # `har_errors` by a constant, and centering annihilates exactly that
            # constant, so both legs would return the same statistic (see #14362).
            dm_uncentered = _dm_uncentered_mse(
                dl_errors[:min_len], har_errors[:min_len], horizon=h
            )

            print(f"  h={h} seed={seed} DL MSE={dl_mse:.5f} "
                  f"DM-centered(debiased HAR) dm_stat={dm_centered['dm_stat']:.3f} "
                  f"p={dm_centered['dm_pvalue']:.4f} -> {dm_centered['dm_verdict']}")

            rows.append({
                "coin": coin,
                "horizon": h,
                "seed": seed,
                "seq_len": seq_len,
                "decompose": decompose,
                "har_mse_logrv_raw": float(har_mse_raw),
                "har_mse_logrv_debiased": float(har_mse_debiased),
                "har_bias_oos": har_bias_oos,
                "har_bias_sq_raw": float(har_decomp_raw["bias_sq"]),
                "har_variance_raw": float(har_decomp_raw["variance"]),
                "har_bias_sq_debiased": float(har_decomp_debiased["bias_sq"]),
                "har_variance_debiased": float(har_decomp_debiased["variance"]),
                "dlinear_mse_logrv": float(dl_mse),
                "dlinear_bias_sq": float(dl_decomp["bias_sq"]),
                "dlinear_variance": float(dl_decomp["variance"]),
                "mse_reduction_pct_vs_debiased_har": float((har_mse_debiased - dl_mse) / har_mse_debiased * 100) if har_mse_debiased > 0 else float("nan"),
                "dm_centered_stat": dm_centered["dm_stat"],
                "dm_centered_pvalue": dm_centered["dm_pvalue"],
                "dm_centered_verdict": dm_centered["dm_verdict"],
                "dm_centered_mean_loss_diff": dm_centered.get("mean_loss_diff", float("nan")),
                "dm_uncentered_vs_har_raw_stat": dm_uncentered["dm_stat"],
                "dm_uncentered_vs_har_raw_pvalue": dm_uncentered["dm_pvalue"],
                "dm_uncentered_vs_har_raw_verdict": dm_uncentered["dm_verdict"],
                "dm_uncentered_vs_har_raw_mean_loss_diff": dm_uncentered.get(
                    "mean_loss_diff", float("nan")
                ),
                "n_predictions": int(dl_out["n_total_preds"]),
                "n_rv_days": int(len(rv)),
            })

    return {"rows": rows}


def aggregate_verdicts_recentered(rows: list[dict]) -> list[dict]:
    """Aggregate the BTC re-centered run with the §C conjunction on the centered DM.

    The §C conjunction here uses:
      - edge = mean(mse_reduction_pct_vs_debiased_har) across seeds
      - sigma = std(mse_reduction_pct_vs_debiased_har) across seeds
      - dm_p_median = median(dm_centered_pvalue) across seeds
    Verdict "BEATS" iff edge >= 2*sigma AND dm_p_median < 0.05.

    The re-centered DM measures the variance differential (biases annihilated
    by centering), so this is the **precision** jambe that the §C amended
    bareme (#11010) requires for the BEATS verdict.
    """
    from collections import defaultdict

    grouped: dict[int, list[dict]] = defaultdict(list)
    for r in rows:
        if "skipped" in r:
            continue
        grouped[r["horizon"]].append(r)

    results = []
    for h, sub in sorted(grouped.items()):
        reductions = np.array([r["mse_reduction_pct_vs_debiased_har"] for r in sub])
        dl_vars = np.array([r["dlinear_variance"] for r in sub])
        har_vars_debiased = np.array([r["har_variance_debiased"] for r in sub])
        har_biases = np.array([r["har_bias_oos"] for r in sub])
        dm_pvals = np.array([r["dm_centered_pvalue"] for r in sub])
        verdicts = [r["dm_centered_verdict"] for r in sub]

        edge = float(np.mean(reductions))
        sigma = float(np.std(reductions)) if len(reductions) > 1 else 0.0
        dm_p_med = float(np.median(dm_pvals))

        # Variance ratio: var_DL / var_HAR_debiased < 1 means DLinear is more precise.
        var_ratio = float(np.mean(dl_vars) / np.mean(har_vars_debiased)) if np.mean(har_vars_debiased) > 0 else float("nan")
        bias_share = float(np.mean(np.abs(har_biases) ** 2) / np.mean(har_biases ** 2 + har_vars_debiased)) \
            if np.all(np.isfinite(har_biases)) else float("nan")

        n_beaten = sum(1 for v in verdicts if "BEATEN" in v)
        if n_beaten > 0:
            verdict_sc = "NO BEATS"
        elif edge >= 2.0 * sigma and dm_p_med < 0.05:
            verdict_sc = "BEATS"
        else:
            verdict_sc = "INCONCLUSIVE"

        results.append({
            "horizon": h,
            "n_seeds": len(sub),
            "edge_reduction_pct": edge,
            "edge_std_pct": sigma,
            "dm_centered_p_median": dm_p_med,
            "var_ratio_dl_over_har_debiased": var_ratio,
            "har_bias_share_of_mse_debiased": bias_share,
            "mean_dl_mse": float(np.mean([r["dlinear_mse_logrv"] for r in sub])),
            "mean_har_mse_raw": float(np.mean([r["har_mse_logrv_raw"] for r in sub])),
            "mean_har_mse_debiased": float(np.mean([r["har_mse_logrv_debiased"] for r in sub])),
            "n_beaten": n_beaten,
            "n_beats": sum(1 for v in verdicts if v == "BEATS baseline"),
            "n_inconclusive": sum(1 for v in verdicts if v == "INCONCLUSIVE"),
            "verdict_sc": verdict_sc,
        })
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description="BTC DLinear-vol re-validation (#12734)")
    parser.add_argument("--horizons", type=int, nargs="+", default=[1, 5, 10])
    parser.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 7, 42, 99])
    parser.add_argument("--seq-len", type=int, default=22)
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--refit-every", type=int, default=22)
    parser.add_argument("--epochs", type=int, default=100)
    parser.add_argument("--decompose", action="store_true")
    parser.add_argument("--out-json", type=str,
                        default="results/m4_dlinear_vol_btc_sc_debiased_recentered.json")
    args = parser.parse_args()

    t0 = time.time()
    payload = run_btc_debiased_recentered(
        horizons=args.horizons,
        seeds=args.seeds,
        seq_len=args.seq_len,
        n_splits=args.n_splits,
        refit_every=args.refit_every,
        epochs=args.epochs,
        decompose=args.decompose,
    )
    rows = payload["rows"]
    aggregated = aggregate_verdicts_recentered(rows)
    elapsed = time.time() - t0

    print("\n=== BTC DLinear-vol (HAR debiased + DM on centered errors) ===")
    if aggregated:
        print(pd.DataFrame(aggregated).to_string(index=False))

    n_beats = sum(1 for r in aggregated if r["verdict_sc"] == "BEATS")
    n_no = sum(1 for r in aggregated if r["verdict_sc"] == "NO BEATS")
    n_inc = sum(1 for r in aggregated if r["verdict_sc"] == "INCONCLUSIVE")
    print(f"\nSummary: {n_beats} BEATS / {n_no} NO BEATS / {n_inc} INCONCLUSIVE")

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({
        "rows": rows,
        "aggregated": aggregated,
        "elapsed_s": elapsed,
        "config": {
            "horizons": args.horizons,
            "seeds": args.seeds,
            "seq_len": args.seq_len,
            "n_splits": args.n_splits,
            "refit_every": args.refit_every,
            "epochs": args.epochs,
            "decompose": args.decompose,
            "har_debiased": True,
            "dm_centered_errors": True,
            "loss_fn": "mse",
        },
    }, indent=2))
    print(f"\n[done] {elapsed:.1f}s -- wrote {out_path}")


if __name__ == "__main__":
    main()