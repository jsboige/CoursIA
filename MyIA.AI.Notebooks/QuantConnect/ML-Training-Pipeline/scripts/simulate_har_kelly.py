"""M11a HAR-RV + Kelly + vol-targeting per-coin simulation.

Consumes HAR walk-forward forecasts (same pipeline as `train_har_baseline.py`)
and translates them into trading-relevant economic metrics:

1. **Vol-targeted Sharpe** (Fleming-Kirby-Ostdiek 2001): scale position size
   to achieve a target portfolio vol. Compares HAR forecast vs naive-30d
   forecast vs perfect-foresight RV.
2. **Kelly fraction** (Thorp 1969 / Kelly 1956): f* = mu / sigma^2 with capped
   leverage. Uses HAR sigma forecast + rolling realised mu estimator. Fee-aware.
3. **Equal-weight buy-and-hold** baseline.

Per-coin walk-forward simulation with the same expanding-window splits as the
HAR fits (n_splits=5, refit_every=22). Multi-seed not applicable (HAR is OLS,
deterministic). For Kelly mu estimation we run a small bootstrap robustness
check (4 mu-window settings) instead of seeds.

Usage:
    python -u simulate_har_kelly.py \\
        --horizons 5 \\
        --extra-coins LTC-USD XRP-USD ADA-USD DOT-USD SOL-USD \\
        --target-vol 0.15 \\
        --kelly-cap 1.0 \\
        --fee-bps 10 \\
        --out-json results/m11a_har_kelly_simulation/results.json

Output structure (one row per (coin, horizon, strategy)):
    coin, horizon, strategy, n_periods, sharpe, ann_return, ann_vol,
    max_drawdown, turnover, gross_pnl_per_year
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from garch_rolling_baseline import naive_constant_baseline
from har_model import walk_forward_har
from intraday_loader import (
    hourly_log_returns,
    load_binance_eth,
    load_bitstamp_btc,
    load_yf_intraday,
)
from realized_variance import daily_realized_variance


def _load_panel(skip_remote: bool, extra_coins: list[str] | None = None) -> dict[str, pd.Series]:
    out: dict[str, pd.Series] = {}
    print("[load] BTC Bitstamp 1h ...", flush=True)
    btc = load_bitstamp_btc()
    out["BTC-USD"] = hourly_log_returns(btc)
    print(f"  BTC hourly returns: {len(out['BTC-USD'])} obs", flush=True)
    print("[load] ETH Binance 1h ...", flush=True)
    eth = load_binance_eth()
    out["ETH-USD"] = hourly_log_returns(eth)
    print(f"  ETH hourly returns: {len(out['ETH-USD'])} obs", flush=True)
    if not skip_remote:
        for ticker in ["SOL-USD"] + (extra_coins or []):
            try:
                print(f"[load] {ticker} yfinance 1h (730d) ...", flush=True)
                ds = load_yf_intraday(ticker)
                out[ticker] = hourly_log_returns(ds)
                print(f"  {ticker} hourly returns: {len(out[ticker])} obs", flush=True)
            except Exception as exc:
                print(f"[WARN] {ticker} fetch skipped ({exc.__class__.__name__}: {exc})", flush=True)
    return out


def _equity_curve(returns: np.ndarray) -> tuple[float, float, float, float, float, float]:
    """Compute Sharpe, ann_return, ann_vol, max_drawdown, gross_pnl_per_year, hit_rate
    from a daily-return series."""
    n = len(returns)
    if n < 20:
        return (float("nan"),) * 6
    eq = np.cumprod(1.0 + returns)
    peaks = np.maximum.accumulate(eq)
    dd = (eq - peaks) / peaks
    max_dd = float(dd.min())
    mu = float(np.mean(returns))
    sd = float(np.std(returns, ddof=1))
    ann_ret = mu * 252.0
    ann_vol = sd * np.sqrt(252.0)
    sharpe = ann_ret / ann_vol if ann_vol > 1e-10 else 0.0
    gross_pnl_per_year = float(eq[-1] ** (252.0 / n) - 1.0) if eq[-1] > 0 else float("nan")
    hit_rate = float(np.mean(returns > 0))
    return sharpe, ann_ret, ann_vol, max_dd, gross_pnl_per_year, hit_rate


def _vol_target_strategy(
    daily_returns: pd.Series,
    forecast_log_rv: pd.Series,
    target_vol: float,
    fee_bps: float,
    max_leverage: float = 4.0,
) -> dict:
    """Vol-targeting: position weight = target_vol / forecast_vol_annual.

    Daily return: w * r_market - fee * |w_t - w_{t-1}|.
    """
    aligned = pd.concat([daily_returns.rename("r"), forecast_log_rv.rename("logrv")], axis=1).dropna()
    if len(aligned) < 30:
        return {"sharpe": float("nan"), "n_periods": 0}
    forecast_var_daily = np.exp(aligned["logrv"].values)
    forecast_vol_daily = np.sqrt(np.clip(forecast_var_daily, 1e-12, None))
    forecast_vol_annual = forecast_vol_daily * np.sqrt(252.0)
    weights = target_vol / np.clip(forecast_vol_annual, 0.01, None)
    weights = np.clip(weights, 0.0, max_leverage)
    r = aligned["r"].values
    pnl = weights * r
    turnover = np.abs(np.diff(weights, prepend=weights[0]))
    fee_drag = (fee_bps / 10000.0) * turnover
    net = pnl - fee_drag
    sharpe, ann_ret, ann_vol, max_dd, growth, hit = _equity_curve(net)
    return {
        "n_periods": int(len(net)),
        "sharpe": round(sharpe, 4),
        "ann_return": round(ann_ret, 6),
        "ann_vol": round(ann_vol, 6),
        "max_drawdown": round(max_dd, 6),
        "growth_pa": round(growth, 6),
        "hit_rate": round(hit, 4),
        "avg_weight": round(float(np.mean(weights)), 4),
        "avg_turnover": round(float(np.mean(turnover)), 6),
    }


def _kelly_strategy(
    daily_returns: pd.Series,
    forecast_log_rv: pd.Series,
    mu_window: int,
    kelly_cap: float,
    fee_bps: float,
) -> dict:
    """Fractional Kelly: f_t = clip(mu_hat_t / sigma2_t, 0, kelly_cap).

    mu_hat: trailing rolling mean of daily returns over `mu_window` days.
    sigma2: forecast (next-period log-RV from HAR -> exp -> daily variance).
    Long-only, fees deducted on weight changes.
    """
    aligned = pd.concat([daily_returns.rename("r"), forecast_log_rv.rename("logrv")], axis=1).dropna()
    if len(aligned) < mu_window + 30:
        return {"sharpe": float("nan"), "n_periods": 0}
    mu_hat = aligned["r"].rolling(mu_window).mean().shift(1)
    sigma2_daily = np.exp(aligned["logrv"].values)
    f_kelly = mu_hat.values / np.clip(sigma2_daily, 1e-12, None)
    f_kelly = np.nan_to_num(f_kelly, nan=0.0, posinf=kelly_cap, neginf=0.0)
    f_kelly = np.clip(f_kelly, 0.0, kelly_cap)
    r = aligned["r"].values
    pnl = f_kelly * r
    turnover = np.abs(np.diff(f_kelly, prepend=f_kelly[0]))
    fee_drag = (fee_bps / 10000.0) * turnover
    net = pnl - fee_drag
    sharpe, ann_ret, ann_vol, max_dd, growth, hit = _equity_curve(net)
    return {
        "n_periods": int(len(net)),
        "sharpe": round(sharpe, 4),
        "ann_return": round(ann_ret, 6),
        "ann_vol": round(ann_vol, 6),
        "max_drawdown": round(max_dd, 6),
        "growth_pa": round(growth, 6),
        "hit_rate": round(hit, 4),
        "avg_weight": round(float(np.mean(f_kelly)), 4),
        "avg_turnover": round(float(np.mean(turnover)), 6),
    }


def _buy_hold_strategy(daily_returns: pd.Series) -> dict:
    r = daily_returns.dropna().values
    if len(r) < 20:
        return {"sharpe": float("nan"), "n_periods": 0}
    sharpe, ann_ret, ann_vol, max_dd, growth, hit = _equity_curve(r)
    return {
        "n_periods": int(len(r)),
        "sharpe": round(sharpe, 4),
        "ann_return": round(ann_ret, 6),
        "ann_vol": round(ann_vol, 6),
        "max_drawdown": round(max_dd, 6),
        "growth_pa": round(growth, 6),
        "hit_rate": round(hit, 4),
        "avg_weight": 1.0,
        "avg_turnover": 0.0,
    }


def _evaluate_one(
    coin: str,
    hourly_rets: pd.Series,
    horizon: int,
    target_vol: float,
    kelly_cap: float,
    fee_bps: float,
    mu_windows: list[int],
    n_splits: int,
    refit_every: int,
    train_size: int,
) -> list[dict]:
    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 300:
        return [{"coin": coin, "horizon": horizon, "skipped": "rv<300"}]
    print(f"\n[{coin} h={horizon}] RV days: {len(rv)}", flush=True)

    har_out = walk_forward_har(rv, horizon=horizon, n_splits=n_splits, refit_every=refit_every)
    har_forecasts = har_out["forecasts"]  # log-RV mean-of-h prediction
    print(f"  HAR forecasts: {len(har_forecasts)} predictions", flush=True)

    # Daily returns aligned by trading-day index
    daily_close_rets = (
        hourly_rets.groupby(hourly_rets.index.normalize()).sum().rename("r_daily")
    )
    daily_close_rets.index = pd.DatetimeIndex(daily_close_rets.index).normalize()
    daily_close_rets = daily_close_rets.reindex(har_forecasts.index).dropna()
    har_forecasts = har_forecasts.reindex(daily_close_rets.index)

    # Naive-30d log-RV baseline (in same units)
    try:
        naive = naive_constant_baseline(rv, horizon=horizon, train_size=train_size, refit_every=refit_every)
        naive_log = np.log(naive.clip(lower=1e-12))
        naive_log = naive_log.reindex(daily_close_rets.index).dropna()
    except Exception as exc:
        print(f"  Naive baseline FAILED: {exc}", flush=True)
        naive_log = None

    # Perfect foresight: realised RV averaged over the next h days, on log scale
    realised_log_rv = (
        np.log(rv.clip(lower=1e-12)).rolling(horizon).mean().shift(-horizon)
    ).reindex(daily_close_rets.index)

    rows: list[dict] = []

    # 1. Buy-and-hold
    bh = _buy_hold_strategy(daily_close_rets)
    bh.update({"coin": coin, "horizon": horizon, "strategy": "buy_hold"})
    rows.append(bh)

    # 2. Vol-target with HAR forecast
    vt_har = _vol_target_strategy(daily_close_rets, har_forecasts, target_vol, fee_bps)
    vt_har.update({"coin": coin, "horizon": horizon, "strategy": "vol_target_har",
                   "target_vol": target_vol, "fee_bps": fee_bps})
    rows.append(vt_har)

    # 3. Vol-target with naive-30d forecast (baseline)
    if naive_log is not None and len(naive_log) >= 30:
        vt_naive = _vol_target_strategy(daily_close_rets, naive_log, target_vol, fee_bps)
        vt_naive.update({"coin": coin, "horizon": horizon, "strategy": "vol_target_naive30",
                         "target_vol": target_vol, "fee_bps": fee_bps})
        rows.append(vt_naive)

    # 4. Vol-target with perfect foresight (oracle upper bound)
    vt_oracle = _vol_target_strategy(daily_close_rets, realised_log_rv, target_vol, fee_bps)
    vt_oracle.update({"coin": coin, "horizon": horizon, "strategy": "vol_target_oracle",
                      "target_vol": target_vol, "fee_bps": fee_bps})
    rows.append(vt_oracle)

    # 5. Kelly with HAR sigma + multiple mu windows (robustness in lieu of seeds)
    for w in mu_windows:
        k_har = _kelly_strategy(daily_close_rets, har_forecasts, w, kelly_cap, fee_bps)
        k_har.update({"coin": coin, "horizon": horizon, "strategy": f"kelly_har_mu{w}",
                      "kelly_cap": kelly_cap, "fee_bps": fee_bps, "mu_window": w})
        rows.append(k_har)

    # 6. Kelly with naive-30d sigma (baseline) for the central mu window
    if naive_log is not None and len(naive_log) >= 30:
        w_central = mu_windows[len(mu_windows) // 2]
        k_naive = _kelly_strategy(daily_close_rets, naive_log, w_central, kelly_cap, fee_bps)
        k_naive.update({"coin": coin, "horizon": horizon, "strategy": f"kelly_naive30_mu{w_central}",
                        "kelly_cap": kelly_cap, "fee_bps": fee_bps, "mu_window": w_central})
        rows.append(k_naive)

    for row in rows:
        if row.get("sharpe") is not None and not (isinstance(row.get("sharpe"), float) and np.isnan(row["sharpe"])):
            print(f"  {row['strategy']:28s} Sharpe={row.get('sharpe',float('nan')):+.3f}  "
                  f"AnnRet={row.get('ann_return',float('nan')):+.4f}  "
                  f"MaxDD={row.get('max_drawdown',float('nan')):+.4f}  "
                  f"n={row.get('n_periods',0)}", flush=True)
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizons", type=int, nargs="+", default=[5])
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--train-size", type=int, default=250)
    parser.add_argument("--refit-every", type=int, default=22)
    parser.add_argument("--target-vol", type=float, default=0.15,
                        help="Target annualized portfolio vol for vol-targeting")
    parser.add_argument("--kelly-cap", type=float, default=1.0,
                        help="Maximum Kelly fraction (long-only, no short)")
    parser.add_argument("--fee-bps", type=float, default=10.0,
                        help="Per-side rebalance fee in bps (10bps = 0.10% per turnover unit)")
    parser.add_argument("--mu-windows", type=int, nargs="+", default=[60, 120, 250],
                        help="Rolling mu estimation windows (days) for Kelly robustness")
    parser.add_argument("--skip-remote", action="store_true")
    parser.add_argument("--extra-coins", type=str, nargs="*", default=None)
    parser.add_argument("--out-json", type=str, default="results/m11a_har_kelly_simulation/results.json")
    args = parser.parse_args()

    t0 = time.time()
    print(f"[setup] target_vol={args.target_vol}  kelly_cap={args.kelly_cap}  fee_bps={args.fee_bps}  "
          f"mu_windows={args.mu_windows}  horizons={args.horizons}", flush=True)
    panel = _load_panel(args.skip_remote, extra_coins=args.extra_coins)

    rows: list[dict] = []
    for coin, rets in panel.items():
        for h in args.horizons:
            try:
                rows.extend(_evaluate_one(
                    coin=coin,
                    hourly_rets=rets,
                    horizon=h,
                    target_vol=args.target_vol,
                    kelly_cap=args.kelly_cap,
                    fee_bps=args.fee_bps,
                    mu_windows=args.mu_windows,
                    n_splits=args.n_splits,
                    refit_every=args.refit_every,
                    train_size=args.train_size,
                ))
            except Exception as exc:
                print(f"[ERROR] {coin} h={h}: {exc.__class__.__name__}: {exc}", flush=True)
                rows.append({"coin": coin, "horizon": h, "error": f"{exc.__class__.__name__}: {exc}"})

    out_df = pd.DataFrame(rows)
    print("\n=== M11a HAR + Kelly + vol-target — full table ===", flush=True)
    if "sharpe" in out_df.columns:
        cols = ["coin", "horizon", "strategy", "sharpe", "ann_return", "ann_vol", "max_drawdown",
                "avg_weight", "avg_turnover", "n_periods"]
        cols = [c for c in cols if c in out_df.columns]
        print(out_df[cols].to_string(index=False), flush=True)

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({
        "rows": rows,
        "elapsed_s": time.time() - t0,
        "config": {
            "target_vol": args.target_vol,
            "kelly_cap": args.kelly_cap,
            "fee_bps": args.fee_bps,
            "mu_windows": args.mu_windows,
            "horizons": args.horizons,
            "n_splits": args.n_splits,
            "refit_every": args.refit_every,
            "train_size": args.train_size,
        },
    }, indent=2))
    print(f"\n[done] {time.time() - t0:.1f}s — wrote {out_path}", flush=True)


if __name__ == "__main__":
    main()
