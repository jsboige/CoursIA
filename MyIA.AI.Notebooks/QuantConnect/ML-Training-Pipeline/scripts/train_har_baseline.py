"""HAR vs GARCH-rolling vs daily-r² head-to-head on crypto Realized Variance.

Issue #834 M2 driver. Loads local hourly OHLCV (Bitstamp BTC + Binance ETH +
optional yfinance SOL), aggregates to daily Realized Variance, runs:

1. HAR(1d, 5d, 22d) walk-forward 5-fold (`har_model.walk_forward_har`)
2. GARCH(1,1) ROLLING refit walk-forward (`garch_rolling_baseline.garch_rolling_forecast`)
3. Naive trailing-30d mean baseline (`garch_rolling_baseline.naive_constant_baseline`)
4. Daily-r² target as a sanity check (very noisy, used by the broken pipeline)

Reports MSE on the log-RV scale (so all models are scored against the same
target — daily aggregated log-RV averaged over the next h days). Diebold-Mariano
HAC is computed in M4 (`diebold_mariano.py` to come).

Usage:
    python train_har_baseline.py --horizons 1 5 10 --skip-remote
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import numpy as np
import pandas as pd

from garch_rolling_baseline import garch_rolling_forecast, naive_constant_baseline
from har_model import HARModel, walk_forward_har
from intraday_loader import (
    hourly_log_returns,
    load_binance_eth,
    load_bitstamp_btc,
    load_yf_intraday,
)
from realized_variance import (
    daily_realized_variance,
    daily_squared_returns,
    realized_variance_to_log,
)


def _load_panel(skip_remote: bool, sol_ticker: str = "SOL-USD") -> dict[str, pd.Series]:
    out: dict[str, pd.Series] = {}
    print("[load] BTC Bitstamp 1h ...")
    btc = load_bitstamp_btc()
    out["BTC-USD"] = hourly_log_returns(btc)
    print(f"  BTC hourly returns: {len(out['BTC-USD'])} obs, "
          f"{out['BTC-USD'].index.min()} → {out['BTC-USD'].index.max()}")
    print("[load] ETH Binance 1h ...")
    eth = load_binance_eth()
    out["ETH-USD"] = hourly_log_returns(eth)
    print(f"  ETH hourly returns: {len(out['ETH-USD'])} obs, "
          f"{out['ETH-USD'].index.min()} → {out['ETH-USD'].index.max()}")
    if not skip_remote:
        try:
            print(f"[load] {sol_ticker} yfinance 1h (730d) ...")
            sol = load_yf_intraday(sol_ticker)
            out[sol_ticker] = hourly_log_returns(sol)
            print(f"  {sol_ticker} hourly returns: {len(out[sol_ticker])} obs, "
                  f"{out[sol_ticker].index.min()} → {out[sol_ticker].index.max()}")
        except Exception as exc:
            print(f"[WARN] {sol_ticker} fetch skipped ({exc.__class__.__name__}: {exc})")
    return out


def _eval_one(
    coin: str,
    hourly_rets: pd.Series,
    horizon: int,
    n_splits: int = 5,
    train_size: int = 250,
    refit_every: int = 22,
) -> dict:
    rv = daily_realized_variance(hourly_rets)
    if len(rv) < 300:
        return {"coin": coin, "horizon": horizon, "skipped": "rv<300"}
    log_rv = realized_variance_to_log(rv)
    print(f"\n[{coin} h={horizon}] RV days: {len(rv)}  log_rv var: {log_rv.var():.4f}")
    har_out = walk_forward_har(rv, horizon=horizon, n_splits=n_splits, refit_every=refit_every)
    har_mse = har_out["aggregate_mse_logrv"]
    print(f"  HAR             MSE(log-RV) = {har_mse:.5f}  (n_preds={har_out['n_total_preds']})")
    daily_close_rets = (
        hourly_rets.groupby(hourly_rets.index.normalize()).sum().rename("r_daily")
    )
    daily_close_rets.index = pd.DatetimeIndex(daily_close_rets.index).normalize()
    common = daily_close_rets.index.intersection(rv.index)
    daily_close_rets = daily_close_rets.loc[common]
    try:
        garch_var = garch_rolling_forecast(
            daily_close_rets,
            horizon=horizon,
            train_size=train_size,
            refit_every=refit_every,
            seed=0,
        )
        garch_aligned = garch_var.reindex(har_out["targets"].index).dropna()
        targets = har_out["targets"].reindex(garch_aligned.index)
        garch_log_pred = np.log(garch_aligned.clip(lower=1e-12))
        garch_mse = float(np.mean((garch_log_pred.values - targets.values) ** 2))
        print(f"  GARCH(1,1) roll MSE(log-RV) = {garch_mse:.5f}  (n_preds={len(garch_aligned)})")
    except Exception as exc:
        garch_mse = float("nan")
        print(f"  GARCH(1,1) roll FAILED: {exc.__class__.__name__}: {exc}")
    try:
        naive = naive_constant_baseline(
            rv, horizon=horizon, train_size=train_size, refit_every=refit_every,
        )
        naive_aligned = naive.reindex(har_out["targets"].index).dropna()
        targets = har_out["targets"].reindex(naive_aligned.index)
        naive_log = np.log(naive_aligned.clip(lower=1e-12))
        naive_mse = float(np.mean((naive_log.values - targets.values) ** 2))
        print(f"  Naive trail-30d MSE(log-RV) = {naive_mse:.5f}  (n_preds={len(naive_aligned)})")
    except Exception as exc:
        naive_mse = float("nan")
        print(f"  Naive trail-30d FAILED: {exc.__class__.__name__}: {exc}")
    r2_daily = daily_squared_returns(hourly_rets)
    r2_aligned = r2_daily.reindex(har_out["targets"].index).dropna()
    if len(r2_aligned) >= 50:
        targets = har_out["targets"].reindex(r2_aligned.index)
        r2_log = np.log(r2_aligned.clip(lower=1e-12))
        r2_mse = float(np.mean((r2_log.values - targets.values) ** 2))
        print(f"  r²-daily target MSE(log-RV) = {r2_mse:.5f}  (degenerate sanity check)")
    else:
        r2_mse = float("nan")
    return {
        "coin": coin,
        "horizon": horizon,
        "n_rv_days": int(len(rv)),
        "n_predictions": int(har_out["n_total_preds"]),
        "har_mse_logrv": float(har_mse),
        "garch_rolling_mse_logrv": float(garch_mse),
        "naive_30d_mse_logrv": float(naive_mse),
        "r2_daily_mse_logrv": float(r2_mse),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizons", type=int, nargs="+", default=[1, 5, 10])
    parser.add_argument("--n-splits", type=int, default=5)
    parser.add_argument("--train-size", type=int, default=250)
    parser.add_argument("--refit-every", type=int, default=22)
    parser.add_argument("--skip-remote", action="store_true")
    parser.add_argument("--out-json", type=str, default="results/m2_har_baseline.json")
    args = parser.parse_args()

    t0 = time.time()
    panel = _load_panel(args.skip_remote)
    rows: list[dict] = []
    for coin, rets in panel.items():
        for h in args.horizons:
            row = _eval_one(
                coin=coin,
                hourly_rets=rets,
                horizon=h,
                n_splits=args.n_splits,
                train_size=args.train_size,
                refit_every=args.refit_every,
            )
            rows.append(row)
    out_df = pd.DataFrame(rows)
    print("\n=== M2 HAR vs GARCH-rolling vs naive vs r²-daily ===")
    print(out_df.to_string(index=False))
    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({"rows": rows, "elapsed_s": time.time() - t0}, indent=2))
    print(f"\n[done] {time.time() - t0:.1f}s — wrote {out_path}")


if __name__ == "__main__":
    main()
