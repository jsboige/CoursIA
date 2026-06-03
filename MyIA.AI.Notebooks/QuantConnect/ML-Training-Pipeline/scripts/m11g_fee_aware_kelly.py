"""M11g Fee-aware Kelly threshold — does no-trade band push break-even past 100bps?

Question
--------
Per the M11f fee-sweep verdict, kelly_har_mu60's edge over buy_hold dies between
50 and 100 bps (sign-test p=0.045 at 50bps, p=0.155 at 100bps). The hypothesis
tested here: if we suppress small rebalances (|Δw| below a threshold), turnover
drops, fee-drag shrinks, and the break-even may shift right.

For each (coin, horizon, fee_bps, threshold):
- Compute Kelly weights as in M11c/f (mu_60d HAR-forecast Kelly fraction, capped 1.0)
- Apply NO-TRADE band: if |w_t - w_{t-1}| < threshold, hold w_{t-1} unchanged
- Net daily returns with fee_bps × actual turnover (turnover SHRINKS with threshold)
- Per-combo LW2008 paired Sharpe-diff p-value vs buy_hold
- Aggregate: BEATS counts, median Δ Sharpe, sign-test (binomial vs ½)

Sweep
-----
- threshold ∈ {0.00, 0.025, 0.05, 0.10, 0.20} (5 levels, 0.00 = M11f baseline)
- fee_bps   ∈ {10, 50, 100}                   (3 levels — focus on break-even region)
- 7 coins × 5 horizons × 5 thresholds × 3 fees = 525 rows.

Output
------
- `results/m11g_fee_aware_kelly/results.{json,csv}`
- stdout 3-D summary (rows = thresholds, columns = fees)

Env: coursia-ml-training. Reuses HAR + LW2008 from m11c_sharpe_test.
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


def _apply_threshold_band(weights: np.ndarray, threshold: float) -> np.ndarray:
    """Suppress trades whose absolute Δw is below `threshold`. Carry forward."""
    if threshold <= 0:
        return weights.copy()
    out = weights.copy()
    for t in range(1, len(out)):
        if abs(out[t] - out[t - 1]) < threshold:
            out[t] = out[t - 1]
    return out


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
    fee_bps_grid: list[float], threshold_grid: list[float],
    n_splits: int, refit_every: int,
) -> list[dict]:
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

    base_weights, r = pair
    t = len(r)
    if t < 50:
        return [{"coin": coin, "horizon": horizon, "skipped": "T<50"}]

    rows = []
    bh = r.copy()  # buy-hold baseline
    for thr in threshold_grid:
        weights_thr = _apply_threshold_band(base_weights, thr)
        # Turnover drop after band:
        raw_turnover = float(np.sum(np.abs(np.diff(base_weights, prepend=base_weights[0]))))
        thr_turnover = float(np.sum(np.abs(np.diff(weights_thr, prepend=weights_thr[0]))))
        turnover_ratio = (thr_turnover / raw_turnover) if raw_turnover > 0 else float("nan")

        for fee in fee_bps_grid:
            net_kelly = _net_at_fee(weights_thr, r, fee)
            sa, sb, diff_daily, se_daily = ledoit_wolf_sharpe_diff_se(net_kelly, bh)
            if not np.isfinite(se_daily) or se_daily <= 0:
                t_stat = float("nan")
                p_one = float("nan")
            else:
                t_stat = diff_daily / se_daily
                from scipy.stats import norm
                p_one = float(1.0 - norm.cdf(t_stat))

            sharpe_diff_ann = (sa - sb) * np.sqrt(252.0)
            rows.append({
                "coin": coin,
                "horizon": horizon,
                "threshold": thr,
                "fee_bps": fee,
                "turnover_total": round(thr_turnover, 4),
                "turnover_ratio_vs_raw": round(turnover_ratio, 4) if np.isfinite(turnover_ratio) else None,
                "n_periods": int(t),
                "sharpe_active_ann": round(sa * np.sqrt(252.0), 4),
                "sharpe_baseline_ann": round(sb * np.sqrt(252.0), 4),
                "delta_sharpe_ann": round(sharpe_diff_ann, 4),
                "t_stat": float(t_stat) if np.isfinite(t_stat) else None,
                "p_value_one_sided": float(p_one) if np.isfinite(p_one) else None,
                "BEATS_p005": bool(np.isfinite(p_one) and p_one < 0.05),
                "BEATS_p010": bool(np.isfinite(p_one) and p_one < 0.10),
                "BEATS_delta_sharpe": bool(sharpe_diff_ann > 0),
            })
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--coins", type=str, nargs="+",
        default=["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"],
    )
    parser.add_argument("--horizons", type=int, nargs="+", default=[1, 5, 10, 15, 20])
    parser.add_argument("--mu-window", type=int, default=60)
    parser.add_argument("--kelly-cap", type=float, default=1.0)
    parser.add_argument(
        "--fee-bps-grid", type=float, nargs="+",
        default=[10.0, 50.0, 100.0],
    )
    parser.add_argument(
        "--threshold-grid", type=float, nargs="+",
        default=[0.00, 0.025, 0.05, 0.10, 0.20],
    )
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--refit-every", type=int, default=22)
    parser.add_argument(
        "--out-dir", type=str,
        default="MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/results/m11g_fee_aware_kelly",
    )
    args = parser.parse_args()

    t0 = time.time()
    print(
        f"[setup] mu_window={args.mu_window}  fee_grid={args.fee_bps_grid}  "
        f"threshold_grid={args.threshold_grid}  "
        f"coins={len(args.coins)} horizons={len(args.horizons)}",
        flush=True,
    )

    all_rows: list[dict] = []
    for coin in args.coins:
        for h in args.horizons:
            try:
                rows = evaluate_coin_horizon(
                    coin=coin, horizon=h, mu_window=args.mu_window,
                    kelly_cap=args.kelly_cap, fee_bps_grid=args.fee_bps_grid,
                    threshold_grid=args.threshold_grid,
                    n_splits=args.n_splits, refit_every=args.refit_every,
                )
                all_rows.extend(rows)
            except Exception as exc:
                print(f"[ERROR] {coin} h={h}: {type(exc).__name__}: {exc}", flush=True)
                all_rows.append({
                    "coin": coin, "horizon": h, "error": f"{type(exc).__name__}: {exc}",
                })

    # --- Aggregate (threshold × fee) grid ----------------------------------
    print("\n=== M11g Fee-Aware Kelly: BEATS_p005 grid (rows=threshold, cols=fee) ===", flush=True)
    header = "  thr/fee  " + "  ".join(f"{f:>10.0f}bps" for f in args.fee_bps_grid)
    print(header, flush=True)
    grid_rows = []
    for thr in args.threshold_grid:
        cells = []
        line_parts = [f"  {thr:>6.3f}  "]
        for fee in args.fee_bps_grid:
            sel = [r for r in all_rows
                   if r.get("threshold") == thr and r.get("fee_bps") == fee
                   and r.get("p_value_one_sided") is not None]
            n = len(sel)
            b_delta = sum(1 for r in sel if r["BEATS_delta_sharpe"])
            b_005 = sum(1 for r in sel if r["BEATS_p005"])
            med = float(np.median([r["delta_sharpe_ann"] for r in sel])) if sel else float("nan")
            p_st = _binomial_pvalue_one_sided(b_delta, n)
            line_parts.append(f"  Δ>0={b_delta:>2d}/{n} p={p_st:.3f} med={med:+.3f}")
            cells.append({
                "threshold": thr, "fee_bps": fee, "n_combos": n,
                "count_delta_positive": b_delta, "count_p005": b_005,
                "median_delta_sharpe": med, "signtest_p_value": p_st,
            })
        print("  ".join(line_parts), flush=True)
        grid_rows.extend(cells)

    # --- Persist results ---------------------------------------------------
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    json_path = out_dir / "results.json"
    with open(json_path, "w", encoding="utf-8") as f:
        json.dump(
            {
                "experiment": "M11g_FEE_AWARE_KELLY_THRESHOLD_BAND",
                "args": vars(args),
                "wallclock_s": round(time.time() - t0, 1),
                "per_combo": all_rows,
                "grid": grid_rows,
            },
            f, indent=2, default=str,
        )

    csv_path = out_dir / "results.csv"
    if all_rows:
        keys = sorted({k for r in all_rows for k in r.keys()})
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=keys)
            w.writeheader()
            for r in all_rows:
                w.writerow(r)

    print(f"\n[done] wallclock={time.time() - t0:.1f}s  out={out_dir}", flush=True)


if __name__ == "__main__":
    main()
