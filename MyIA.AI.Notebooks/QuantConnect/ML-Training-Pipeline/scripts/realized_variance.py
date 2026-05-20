"""Realized Variance & related volatility estimators from intraday returns.

References:
- Andersen, Bollerslev, Diebold, Labys (2003) "Modeling and Forecasting Realized Volatility"
- Barndorff-Nielsen & Shephard (2002) — bipower variation for jump-robust RV

Pure pandas/numpy. The HAR model in `har_model.py` consumes the daily series
returned by `daily_realized_variance`.

Conventions:
- All series are tz-naive, indexed by *calendar day* in UTC for daily aggregates.
- Log returns are close-to-close at the native intraday granularity (no overlap).
- "Realized Variance" RV_t = sum_{h in day t} r²_h. Annualizing is left to callers.
"""

from __future__ import annotations

import numpy as np
import pandas as pd


def daily_realized_variance(
    intraday_log_returns: pd.Series,
    min_obs_per_day: int = 6,
) -> pd.Series:
    """Aggregate intraday log returns to a daily Realized Variance series.

    RV_t = sum_{h in day t} r²_h. Days with fewer than `min_obs_per_day`
    observations are dropped (incomplete sessions, exchange downtimes, gaps).

    Returns a Series indexed by calendar Date with name "RV".
    """
    if not isinstance(intraday_log_returns.index, pd.DatetimeIndex):
        raise TypeError("intraday_log_returns must be DatetimeIndex")
    sq = intraday_log_returns.astype(float) ** 2
    by_day = sq.groupby(sq.index.normalize())
    rv = by_day.sum()
    counts = by_day.count()
    rv = rv[counts >= min_obs_per_day]
    rv.index = pd.DatetimeIndex(rv.index).normalize()
    rv.index.name = "date"
    rv.name = "RV"
    return rv


def daily_realized_volatility(
    intraday_log_returns: pd.Series,
    min_obs_per_day: int = 6,
) -> pd.Series:
    """Realized volatility = sqrt(RV)."""
    rv = daily_realized_variance(intraday_log_returns, min_obs_per_day=min_obs_per_day)
    rvol = np.sqrt(rv)
    rvol.name = "RVol"
    return rvol


def daily_bipower_variation(
    intraday_log_returns: pd.Series,
    min_obs_per_day: int = 6,
) -> pd.Series:
    """Barndorff-Nielsen & Shephard bipower variation (jump-robust RV proxy).

    BV_t = (pi/2) * sum_{i=2..M} |r_i| * |r_{i-1}|
    """
    if not isinstance(intraday_log_returns.index, pd.DatetimeIndex):
        raise TypeError("intraday_log_returns must be DatetimeIndex")
    abs_r = intraday_log_returns.abs().astype(float)
    abs_lag = abs_r.shift(1)
    same_day = abs_r.index.normalize() == abs_lag.index.normalize()
    paired = (abs_r * abs_lag).where(same_day, other=0.0)
    by_day = paired.groupby(paired.index.normalize())
    bv = (np.pi / 2.0) * by_day.sum()
    counts = abs_r.groupby(abs_r.index.normalize()).count()
    bv = bv[counts >= min_obs_per_day]
    bv.index = pd.DatetimeIndex(bv.index).normalize()
    bv.index.name = "date"
    bv.name = "BV"
    return bv


def daily_squared_returns(
    intraday_log_returns: pd.Series,
    min_obs_per_day: int = 6,
) -> pd.Series:
    """Naive r²_daily target (sum-of-intraday close-to-close, then squared).

    Used as the *bad* baseline target the GARCH/DL pipeline currently fits.
    Equivalent to (sum r_h)² which is much noisier than RV = sum r_h².
    """
    if not isinstance(intraday_log_returns.index, pd.DatetimeIndex):
        raise TypeError("intraday_log_returns must be DatetimeIndex")
    by_day = intraday_log_returns.groupby(intraday_log_returns.index.normalize())
    daily_ret = by_day.sum()
    counts = by_day.count()
    daily_ret = daily_ret[counts >= min_obs_per_day]
    out = (daily_ret.astype(float) ** 2)
    out.index = pd.DatetimeIndex(out.index).normalize()
    out.index.name = "date"
    out.name = "r2_daily"
    return out


def har_lag_features(rv: pd.Series) -> pd.DataFrame:
    """Build the Corsi (2009) HAR lag features.

    Columns:
    - rv_d   = RV_{t-1}
    - rv_w   = mean(RV_{t-5..t-1})  (weekly average)
    - rv_m   = mean(RV_{t-22..t-1}) (monthly ~ 22 trading days)

    Returns a DataFrame aligned to the original `rv` index. The first 22 rows
    will contain NaN for `rv_m` and should be dropped before modelling.
    """
    if not isinstance(rv, pd.Series):
        raise TypeError("rv must be a pandas Series")
    rv = rv.astype(float)
    rv_d = rv.shift(1)
    rv_w = rv.shift(1).rolling(window=5, min_periods=5).mean()
    rv_m = rv.shift(1).rolling(window=22, min_periods=22).mean()
    return pd.DataFrame({"rv_d": rv_d, "rv_w": rv_w, "rv_m": rv_m})


def realized_variance_to_log(rv: pd.Series, eps: float = 1e-12) -> pd.Series:
    """log(RV) with floor on zeros to keep the regression well-defined."""
    rv = rv.astype(float)
    return np.log(rv.clip(lower=eps))
