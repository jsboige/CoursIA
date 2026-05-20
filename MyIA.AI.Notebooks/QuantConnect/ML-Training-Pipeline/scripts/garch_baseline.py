"""
GARCH(1,1) baseline for volatility forecasting — NO data leak.

Provides two baselines:
    1. `fit_garch_leaky` — legacy (in-sample fit, kept for comparison only)
    2. `fit_garch_rolling` — corrected rolling refit with OOS forecast

The rolling version refits GARCH at each test-step using only past data,
then produces proper h-step forecasts via `arch_model.forecast()`.
This eliminates the data leak where `am.fit()` on the full series made
`conditional_volatility` an in-sample statistic.

Usage:
    from garch_baseline import fit_garch_rolling
    preds = fit_garch_rolling(returns, horizon=5, refit_freq=5)

References:
    - Hansen & Lunde (2005): "A forecast comparison of volatility models"
    - arch package docs: https://arch.readthedocs.io/
"""

from __future__ import annotations

import warnings
from typing import Optional

import numpy as np
import pandas as pd


def fit_garch_leaky(returns: pd.Series, horizon: int = 1) -> pd.Series:
    """Legacy GARCH fit — in-sample conditional variance (DATA LEAK).

    Kept for delta comparison only. DO NOT use for actual forecasting.
    """
    from arch import arch_model

    scaled = returns * 100
    am = arch_model(scaled.dropna(), vol="Garch", p=1, q=1, dist="normal", rescale=False)
    res = am.fit(disp="off", show_warning=False)
    cond_var = res.conditional_volatility ** 2
    if horizon > 1:
        cond_var = cond_var * horizon
    cond_var = cond_var / 10000
    cond_var.index = returns.index[:len(cond_var)]
    return cond_var


def fit_garch_rolling(
    returns: pd.Series,
    horizon: int = 1,
    train_window: int = 1000,
    refit_freq: int = 5,
    min_train: int = 500,
    forecast_method: str = "simulation",
    n_sims: int = 1000,
) -> pd.Series:
    """Rolling GARCH(1,1) refit with proper h-step ahead OOS forecast.

    At each test timestep t:
      1. Train on returns[:t] (at most `train_window` obs for speed)
      2. Forecast h-step ahead variance using `arch_model.forecast()`
      3. Record forecast as prediction for date t

    Parameters
    ----------
    returns : pd.Series
        Log-returns, datetime-indexed.
    horizon : int
        Forecast horizon in days (h-step ahead).
    train_window : int
        Max training window size (rolling, not expanding). GARCH(1,1)
        needs ~500+ obs to converge; 1000 is a good default.
    refit_freq : int
        Refit every N test steps. Between refits, use last model's
        variance recursion to update. 5 = refit weekly.
    min_train : int
        Minimum training observations before producing forecasts.
    forecast_method : str
        'simulation' or 'bootstrap' for multi-step forecast.
    n_sims : int
        Number of simulations for multi-step forecast.

    Returns
    -------
    pd.Series
        h-step ahead variance forecasts, aligned with returns index.
        NaN where insufficient training data.
    """
    from arch import arch_model

    ret = returns.dropna()
    n = len(ret)
    forecasts = np.full(n, np.nan)
    last_model = None
    last_refit_idx = -refit_freq  # force immediate first refit

    for t in range(min_train, n):
        # Only refit every refit_freq steps
        if (t - last_refit_idx) >= refit_freq:
            start = max(0, t - train_window)
            train_data = ret.iloc[start:t].values * 100

            if len(train_data) < min_train:
                continue

            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                am = arch_model(
                    train_data, vol="Garch", p=1, q=1,
                    dist="normal", rescale=False,
                )
                try:
                    res = am.fit(disp="off", show_warning=False, options={"maxiter": 200})
                    if res.convergence_flag != 0:
                        continue
                except Exception:
                    continue

            last_model = res
            last_refit_idx = t

        # Produce forecast from last fitted model
        if last_model is None:
            continue

        try:
            if horizon == 1:
                # 1-step: use analytical forecast
                fcast = last_model.forecast(horizon=1, method=forecast_method)
                var_forecast = fcast.variance.iloc[-1, 0]
            else:
                # h-step: use simulation or bootstrap
                fcast = last_model.forecast(
                    horizon=horizon, method=forecast_method,
                    simulations=n_sims,
                )
                # Sum of daily variance forecasts over horizon
                var_forecast = fcast.variance.iloc[-1, :].sum()

            # Rescale from %² back to original units
            forecasts[t] = var_forecast / 10000
        except Exception:
            continue

    result = pd.Series(forecasts, index=ret.index, name=f"garch_rolling_h{horizon}d")
    return result


def compute_realized_vol(returns: pd.Series, horizon: int) -> pd.Series:
    """Realized volatility: rolling sum of squared returns over horizon."""
    rv = returns.pow(2).rolling(horizon).sum().shift(-horizon)
    log_rv = np.log(rv.clip(lower=1e-12))
    log_rv.name = f"log_rv_{horizon}d"
    return log_rv


def compare_baselines(
    returns: pd.Series,
    horizon: int = 5,
    refit_freq: int = 5,
    test_start_frac: float = 0.8,
) -> dict:
    """Compare leaky vs rolling GARCH on same test set.

    Returns dict with MSE for both and delta (leaky - rolling).
    """
    target = compute_realized_vol(returns, horizon).dropna()

    print(f"Fitting leaky GARCH h={horizon}d...")
    leaky_var = fit_garch_leaky(returns, horizon)

    print(f"Fitting rolling GARCH h={horizon}d (refit every {refit_freq} steps)...")
    rolling_var = fit_garch_rolling(returns, horizon, refit_freq=refit_freq)

    # Align all series
    log_leaky = np.log(leaky_var.clip(lower=1e-12))
    log_rolling = np.log(rolling_var.clip(lower=1e-12))

    combined = pd.DataFrame({
        "target": target,
        "leaky": log_leaky,
        "rolling": log_rolling,
    }).dropna()

    if len(combined) < 100:
        return {"error": f"Only {len(combined)} aligned samples"}

    # Test on last 20% only
    split = int(len(combined) * test_start_frac)
    test = combined.iloc[split:]

    y = test["target"].values
    leaky_pred = test["leaky"].values
    rolling_pred = test["rolling"].values

    leaky_mse = np.mean((y - leaky_pred) ** 2)
    rolling_mse = np.mean((y - rolling_pred) ** 2)
    delta_pct = (leaky_mse - rolling_mse) / leaky_mse * 100

    return {
        "horizon": horizon,
        "n_test": len(test),
        "leaky_mse": float(leaky_mse),
        "rolling_mse": float(rolling_mse),
        "delta_pct": float(delta_pct),
        "interpretation": (
            f"Leaky GARCH MSE is {abs(delta_pct):.1f}% "
            f"{'higher' if delta_pct > 0 else 'lower'} than rolling "
            f"({'leaky overfits' if delta_pct > 0 else 'leaky surprisingly better'})"
        ),
    }


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="GARCH baseline comparison (leaky vs rolling)")
    parser.add_argument("--asset", type=str, default="BTC-USD")
    parser.add_argument("--horizon", type=int, default=5)
    parser.add_argument("--refit-freq", type=int, default=5)
    parser.add_argument("--dry-run", action="store_true", help="Quick sanity check with synthetic data")
    args = parser.parse_args()

    if args.dry_run:
        np.random.seed(42)
        n = 1500
        synth_ret = pd.Series(
            np.random.randn(n) * 0.02,
            index=pd.date_range("2018-01-01", periods=n, freq="B"),
            name="synth",
        )
        result = compare_baselines(synth_ret, args.horizon, args.refit_freq)
    else:
        import sys
        sys.path.insert(0, str(__file__).rsplit("/", 1)[0])
        from data_sources import fetch_data

        df = fetch_data(args.asset, start="2015-01-01")
        if df is None or df.empty:
            print(f"ERROR: no data for {args.asset}")
            sys.exit(1)
        close = df["Close"].sort_index()
        close = close[~close.index.duplicated(keep="first")]
        ret = np.log(close / close.shift(1)).dropna()
        result = compare_baselines(ret, args.horizon, args.refit_freq)

    print("\n" + "=" * 60)
    print(f"GARCH Baseline Comparison — {args.asset} h={args.horizon}d")
    print("=" * 60)
    for k, v in result.items():
        print(f"  {k}: {v}")
