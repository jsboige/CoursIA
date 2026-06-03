"""M11f Transaction cost sensitivity sweep for `kelly_har_mu60`.

Question
--------
At what transaction cost does the `kelly_har_mu60` edge over `buy_hold`
disappear ?

Method
------
Re-run the same 7-coin × 5-horizon (35-combo) panel as M11a/M11b/M11c, but
sweep `fee_bps ∈ {5, 10, 20, 50, 100}` (5 levels). For each fee level:

- Per-combo raw Δ Sharpe (annualised) vs `buy_hold`
- Per-combo LW2008 paired Sharpe-diff p-value (one-sided)
- BEATS counts: Δ Sharpe > 0, p < 0.10, p < 0.05
- Median Δ Sharpe across the panel
- Sign-test p-value (binomial vs null=½)

The HAR forecasts are deterministic (OLS) so they're computed **once** per
(coin, horizon) and re-used across all 5 fee levels — only the fee-drag term
changes. This keeps wall-clock under 5 minutes.

Output
------
- `results/m11f_tx_cost_sweep/results.json` — full per-(combo, fee) rows + agg
- `results/m11f_tx_cost_sweep/results.csv` — flat table
- stdout summary with the fee-sensitivity curve

Usage
-----
    python -u scripts/m11f_tx_cost_sweep.py \\
        --fee-bps-grid 5 10 20 50 100

Env : `coursia-ml-training` (numpy 2, pandas 3, scipy 1.17). No extra deps.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from har_model import walk_forward_har  # noqa: E402
from intraday_loader import (  # noqa: E402
    hourly_log_returns,
    load_binance_eth,
    load_bitstamp_btc,
    load_yf_intraday,
)
from m11c_sharpe_test import ledoit_wolf_sharpe_diff_se  # noqa: E402
from realized_variance import daily_realized_variance  # noqa: E402


def _load_one_coin(coin: str) -> pd.Series:
    if coin == "BTC-USD":
        return hourly_log_returns(load_bitstamp_btc())
    if coin == "ETH-USD":
        return hourly_log_returns(load_binance_eth())
    return hourly_log_returns(load_yf_intraday(coin))


def _kelly_weights_and_returns(
    daily_returns: pd.Series,
    forecast_log_rv: pd.Series,
    mu_window: int,
    kelly_cap: float,
) -> tuple[np.ndarray, np.ndarray] | None:
    """Returns (weights, raw_daily_returns) aligned, pre-fees."""
    aligned = pd.concat(
        [daily_returns.rename("r"), forecast_log_rv.rename("logrv")], axis=1
    ).dropna()
    if len(aligned) < mu_window + 30:
        return None
    mu_hat = aligned["r"].rolling(mu_window).mean().shift(1)
    sigma2_daily = np.exp(aligned["logrv"].values)
    f_kelly = mu_hat.values / np.clip(sigma2_daily, 1e-12, None)
    f_kelly = np.nan_to_num(f_kelly, nan=0.0, posinf=kelly_cap, neginf=0.0)
    f_kelly = np.clip(f_kelly, 0.0, kelly_cap)
    return f_kelly, aligned["r"].values


def _net_at_fee(weights: np.ndarray, r: np.ndarray, fee_bps: float) -> np.ndarray:
    pnl = weights * r
    turnover = np.abs(np.diff(weights, prepend=weights[0]))
    fee_drag = (fee_bps / 10000.0) * turnover
    return pnl - fee_drag


def _binomial_pvalue_one_sided(k: int, n: int, p_null: float = 0.5) -> float:
    if n <= 0:
        return float("nan")
    from scipy.stats import binomtest
    return float(binomtest(k, n, p=p_null, alternative="greater").pvalue)


def evaluate_coin_horizon(
    coin: str, horizon: int, mu_window: int, kelly_cap: float,
    fee_bps_grid: list[float], n_splits: int, refit_every: int,
) -> list[dict]:
    """For a single (coin, horizon), produce one row per fee-bps level."""
    hourly_rets = _load_one_coin(coin)
    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 300:
        return [{"coin": coin, "horizon": horizon, "skipped": "rv<300"}]

    print(f"\n[{coin} h={horizon}] RV days={len(rv)}", flush=True)

    har_out = walk_forward_har(rv, horizon=horizon, n_splits=n_splits, refit_every=refit_every)
    har_forecasts = har_out["forecasts"]
    daily_close_rets = (
        hourly_rets.groupby(hourly_rets.index.normalize()).sum().rename("r_daily")
    )
    daily_close_rets.index = pd.DatetimeIndex(daily_close_rets.index).normalize()
    daily_close_rets = daily_close_rets.reindex(har_forecasts.index).dropna()
    har_forecasts = har_forecasts.reindex(daily_close_rets.index)

    pair = _kelly_weights_and_returns(
        daily_close_rets, har_forecasts, mu_window, kelly_cap
    )
    if pair is None:
        return [{"coin": coin, "horizon": horizon, "skipped": "insufficient"}]

    weights, r = pair
    t = len(r)
    if t < 50:
        return [{"coin": coin, "horizon": horizon, "skipped": "T<50"}]

    rows = []
    for fee in fee_bps_grid:
        net_kelly = _net_at_fee(weights, r, fee)
        # Buy-and-hold fee is 0 turnover (already in position).
        net_bh = r.copy()

        sa, sb, diff_daily, se_daily = ledoit_wolf_sharpe_diff_se(net_kelly, net_bh)
        if not np.isfinite(se_daily) or se_daily <= 0:
            t_stat = float("nan")
            p_one = float("nan")
        else:
            t_stat = diff_daily / se_daily
            from scipy.stats import norm
            p_one = float(1.0 - norm.cdf(t_stat))

        sharpe_diff_ann = (sa - sb) * np.sqrt(252.0)
        sharpe_active_ann = sa * np.sqrt(252.0)
        sharpe_bh_ann = sb * np.sqrt(252.0)

        rows.append({
            "coin": coin,
            "horizon": horizon,
            "fee_bps": fee,
            "n_periods": int(t),
            "sharpe_active_ann": round(sharpe_active_ann, 4),
            "sharpe_baseline_ann": round(sharpe_bh_ann, 4),
            "delta_sharpe_ann": round(sharpe_diff_ann, 4),
            "t_stat": float(t_stat) if np.isfinite(t_stat) else None,
            "p_value_one_sided": float(p_one) if np.isfinite(p_one) else None,
            "BEATS_p005": bool(np.isfinite(p_one) and p_one < 0.05),
            "BEATS_p010": bool(np.isfinite(p_one) and p_one < 0.10),
            "BEATS_delta_sharpe": bool(sharpe_diff_ann > 0),
        })

    for r_row in rows:
        flag = "**" if r_row["BEATS_p005"] else ("+" if r_row["BEATS_delta_sharpe"] else "-")
        print(
            f"  fee={r_row['fee_bps']:>4.0f}bps  Δ Sharpe={r_row['delta_sharpe_ann']:+.3f}  "
            f"t={r_row['t_stat'] if r_row['t_stat'] is not None else float('nan'):+.3f}  "
            f"p={r_row['p_value_one_sided']:.4f}  {flag}",
            flush=True,
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--coins", type=str, nargs="+",
        default=["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"],
    )
    parser.add_argument("--horizons", type=int, nargs="+", default=[1, 5, 10, 15, 20])
    parser.add_argument("--mu-window", type=int, default=60,
                        help="Kelly rolling-mu window (kelly_har_mu60 by default)")
    parser.add_argument("--kelly-cap", type=float, default=1.0)
    parser.add_argument(
        "--fee-bps-grid", type=float, nargs="+",
        default=[5.0, 10.0, 20.0, 50.0, 100.0],
    )
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--refit-every", type=int, default=22)
    parser.add_argument(
        "--out-dir", type=str,
        default="MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/results/m11f_tx_cost_sweep",
    )
    args = parser.parse_args()

    t0 = time.time()
    print(f"[setup] mu_window={args.mu_window}  fee_grid={args.fee_bps_grid}  "
          f"coins={len(args.coins)} horizons={len(args.horizons)}", flush=True)

    all_rows: list[dict] = []
    for coin in args.coins:
        for h in args.horizons:
            try:
                rows = evaluate_coin_horizon(
                    coin=coin, horizon=h, mu_window=args.mu_window,
                    kelly_cap=args.kelly_cap, fee_bps_grid=args.fee_bps_grid,
                    n_splits=args.n_splits, refit_every=args.refit_every,
                )
                all_rows.extend(rows)
            except Exception as exc:
                print(f"[ERROR] {coin} h={h}: {type(exc).__name__}: {exc}", flush=True)
                all_rows.append({
                    "coin": coin, "horizon": h, "error": f"{type(exc).__name__}: {exc}",
                })

    # --- Aggregate per-fee curve --------------------------------------------
    print("\n=== M11f Fee-Sensitivity Curve (kelly_har_mu60 vs buy_hold) ===", flush=True)
    print(f"{'fee_bps':>8s}  {'BEATS_Δ':>10s}  {'BEATS_p010':>11s}  {'BEATS_p005':>11s}  "
          f"{'med Δ Sharpe':>14s}  {'sign-test p':>12s}", flush=True)
    fee_curve = []
    for fee in args.fee_bps_grid:
        rows_fee = [r for r in all_rows if r.get("fee_bps") == fee and r.get("p_value_one_sided") is not None]
        n = len(rows_fee)
        b_delta = sum(1 for r in rows_fee if r["BEATS_delta_sharpe"])
        b_010 = sum(1 for r in rows_fee if r["BEATS_p010"])
        b_005 = sum(1 for r in rows_fee if r["BEATS_p005"])
        med_delta = float(np.median([r["delta_sharpe_ann"] for r in rows_fee])) if rows_fee else float("nan")
        p_signtest = _binomial_pvalue_one_sided(b_delta, n)
        fee_curve.append({
            "fee_bps": fee,
            "n_combos": n,
            "count_delta_positive": b_delta,
            "count_p010": b_010,
            "count_p005": b_005,
            "median_delta_sharpe": med_delta,
            "signtest_p_value": p_signtest,
        })
        print(
            f"{fee:>8.0f}  {b_delta:>3d}/{n:<3d}    {b_010:>3d}/{n:<3d}      {b_005:>3d}/{n:<3d}      "
            f"{med_delta:>+12.4f}    {p_signtest:>12.4f}",
            flush=True,
        )

    # --- Break-even fee detection -------------------------------------------
    breakeven_p005 = None
    breakeven_delta = None
    for i, point in enumerate(fee_curve):
        if breakeven_p005 is None and point["count_p005"] == 0:
            breakeven_p005 = point["fee_bps"]
        if breakeven_delta is None and point["count_delta_positive"] <= point["n_combos"] / 2:
            breakeven_delta = point["fee_bps"]

    print("\n--- Break-even points ---", flush=True)
    print(f"  fee_bps at which BEATS_p005 first drops to 0       : {breakeven_p005}", flush=True)
    print(f"  fee_bps at which Δ Sharpe>0 count drops <= n/2     : {breakeven_delta}", flush=True)

    # --- Verdict ------------------------------------------------------------
    if breakeven_p005 is None:
        # No fee level eliminates all p005 BEATS
        verdict = "kelly_har_mu60 retains p<0.05 BEATS across all tested fee levels"
    elif breakeven_p005 <= 10:
        verdict = "kelly_har_mu60 edge is fragile (no p005 BEATS even at 10bps)"
    elif breakeven_p005 <= 50:
        verdict = f"kelly_har_mu60 edge survives up to ~{int(breakeven_p005)}bps (retail-friendly threshold)"
    else:
        verdict = f"kelly_har_mu60 edge is robust up to ~{int(breakeven_p005)}bps"

    print(f"\n  VERDICT: {verdict}", flush=True)

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "results.json").write_text(json.dumps({
        "rows": all_rows,
        "fee_curve": fee_curve,
        "breakeven_p005_bps": breakeven_p005,
        "breakeven_delta_majority_bps": breakeven_delta,
        "verdict": verdict,
        "config": {
            "coins": args.coins,
            "horizons": args.horizons,
            "mu_window": args.mu_window,
            "kelly_cap": args.kelly_cap,
            "fee_bps_grid": args.fee_bps_grid,
            "n_splits": args.n_splits,
            "refit_every": args.refit_every,
            "test": "Ledoit-Wolf 2008 paired Sharpe-diff (one-sided, normal asymp)",
        },
        "elapsed_s": time.time() - t0,
    }, indent=2))

    csv_cols = [
        "coin", "horizon", "fee_bps", "n_periods",
        "sharpe_active_ann", "sharpe_baseline_ann", "delta_sharpe_ann",
        "t_stat", "p_value_one_sided",
        "BEATS_p005", "BEATS_p010", "BEATS_delta_sharpe",
    ]
    with open(out_dir / "results.csv", "w", newline="") as fh:
        wr = csv.DictWriter(fh, fieldnames=csv_cols)
        wr.writeheader()
        for r in all_rows:
            if "error" in r or "skipped" in r:
                continue
            wr.writerow({k: r.get(k) for k in csv_cols})

    print(f"\n[done] {time.time() - t0:.1f}s — wrote {out_dir}/results.{{json,csv}}", flush=True)


if __name__ == "__main__":
    main()
