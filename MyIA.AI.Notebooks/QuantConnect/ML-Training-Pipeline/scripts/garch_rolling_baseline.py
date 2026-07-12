"""GARCH(1,1) rolling baseline (no in-sample leak).

Companion to `har_model.py`. The existing `train_volatility_garch_dl.py`
fits GARCH **once on the whole series** and uses its in-sample
`conditional_volatility ** 2` as a "prediction" for every test point. That
is a leak (the GARCH parameters were estimated using the very test points
it then predicts on) and inflates the GARCH baseline performance, making
the DL hybrid look worse by comparison.

This module provides a leak-free rolling refit + simulation forecast that
matches the academic standard. It is consumed by `train_har_baseline.py`
to produce a fair head-to-head HAR vs GARCH-rolling MSE comparison.
"""

from __future__ import annotations

import numpy as np
import pandas as pd


def garch_rolling_forecast(
    returns: pd.Series,
    horizon: int = 1,
    train_size: int = 250,
    refit_every: int = 22,
    p: int = 1,
    q: int = 1,
    method: str = "simulation",
    simulations: int = 1000,
    seed: int = 0,
) -> pd.Series:
    """Walk-forward GARCH(p,q) refit + h-step variance forecast.

    Returns a Series of variance forecasts indexed by the *first* day of the
    forecast window (so it is naturally aligned with HAR's `targets` series).
    """
    try:
        from arch import arch_model
    except ImportError as exc:
        raise ImportError("arch package required: pip install arch") from exc
    rets = returns.dropna().astype(float)
    n = len(rets)
    if n < train_size + horizon + 30:
        raise ValueError(f"need >={train_size + horizon + 30} obs, got {n}")
    rng = np.random.default_rng(seed)
    forecasts: list[float] = []
    dates: list[pd.Timestamp] = []
    model = None
    fit_res = None
    last_refit = -1
    for i in range(train_size, n - horizon):
        if model is None or (i - last_refit) >= refit_every:
            sample = rets.iloc[i - train_size:i] * 100.0
            model = arch_model(sample, p=p, q=q, mean="Zero", vol="GARCH", dist="Normal")
            fit_res = model.fit(disp="off", show_warning=False)
            last_refit = i
        if method == "analytic" and horizon == 1:
            f = fit_res.forecast(horizon=1, reindex=False)
            sigma2 = float(f.variance.iloc[-1, 0]) / 1e4
        else:
            sim = fit_res.forecast(
                horizon=horizon,
                method="simulation",
                simulations=simulations,
                random_state=rng,
                reindex=False,
            )
            var_path = sim.variance.iloc[-1].values  # length horizon, in (returns*100)² units
            sigma2 = float(np.mean(var_path)) / 1e4
        forecasts.append(sigma2)
        dates.append(rets.index[i])
    return pd.Series(forecasts, index=pd.DatetimeIndex(dates), name="garch_var_pred")


def naive_constant_baseline(
    rv: pd.Series,
    horizon: int = 1,
    train_size: int = 250,
    refit_every: int = 22,
) -> pd.Series:
    """Trailing-mean baseline: predict next-h average RV with the trailing 30d mean.

    This is the simplest non-trivial benchmark. Any model that does not beat
    it should be discarded.
    """
    rv = rv.dropna().astype(float)
    n = len(rv)
    if n < train_size + horizon:
        raise ValueError(f"need >={train_size + horizon} obs, got {n}")
    forecasts: list[float] = []
    dates: list[pd.Timestamp] = []
    for i in range(train_size, n - horizon):
        sigma2 = float(rv.iloc[i - 30:i].mean())
        forecasts.append(sigma2)
        dates.append(rv.index[i])
    return pd.Series(forecasts, index=pd.DatetimeIndex(dates), name="naive_var_pred")
