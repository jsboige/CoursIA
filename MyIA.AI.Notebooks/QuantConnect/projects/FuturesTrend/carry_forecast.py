# -*- coding: utf-8 -*-
"""Pure-numpy Carver #11 carry forecast (annualised term-structure carry).

Strategy #11 — Combined Carry and Trend (Carver 2023, *Advanced Futures
Trading Strategies*, Harriman House, ISBN 9780857199683), as re-created in
the QuantConnect research post #16001 "Combined Carry and Trend" (Derek
Melchin). Carver does not endorse this implementation.

Formula (post #16001, alpha.py `update` / `calculate_carry_forecasts`):

    raw_carry              = near_price - further_price
    months_between         = round((further_expiry - near_expiry).days / 30)
    expiry_diff_years      = abs(months_between) / 12
    annualized_raw_carry   = raw_carry / expiry_diff_years
    daily_risk_price_terms = EWMA_32(|daily returns|) * last_price
    carry_forecast         = annualized_raw_carry / (daily_risk_price_terms * sqrt(256))
    smoothed(span)         = EWMA_span(carry_forecast)[-1]   (min_periods=span)
    scaled(span)           = smoothed * CARRY_FORECAST_SCALAR
    capped(span)           = clip(scaled, -CAP, +CAP)
    blend                  = (1 - w) * trend + w * carry     (w = 0.4, article 60/40)

Per-span forecasts are aggregated equal-weight by the caller. Spans whose
history is shorter than the span itself are skipped, mirroring the article
(`if smoothed_carry_forecast.empty: continue`).

Semis #17320, tranche 2 (claim 5768478492). This module is intentionally
**pure numpy** so `tests/test_carry_forecast.py` runs on CPU without the
QC Cloud runtime, following the `breadth_multiplier.py` pattern (REPAIR-8
c.1115: no formula duplication between tests and production). The EWMA
here uses alpha = 2/(span+1), the same convention as `main_carver13._ewma`;
when tranche 3 wires this into the LEAN algorithm, `main_carver13` must
**import** this module (like it imports `breadth_multiplier`) rather than
re-implement the smoothing.

Divergence note (documented in the semis #17320 acceptance): the trend leg
of the existing #13 port uses sqrt(slow/32)-scaled scalars, not Carver's
Table 29 values; the carry scalar here is Carver's exact 30 (p.216). The
scalar harmonisation is deliberately deferred to tranche 3 (backtests),
where the FDM-vs-breadth choice must also be measured.
"""

import numpy as np

# Carver #11 carry forecast scalar (Advanced Futures Trading Strategies,
# p.216, cited by post #16001). Scales the smoothed carry so its average
# absolute value is ~10 (half the cap).
CARRY_FORECAST_SCALAR = 30.0

# Smoothing spans for the carry forecast (post #16001 `carry_spans`).
CARRY_SMOOTHING_SPANS = (5, 20, 60, 120)

# Per-forecast cap (same constant as the #13 port, Carver rule).
CARRY_FORECAST_CAP = 20.0

# Instrument-risk EWMA span for the carry risk adjustment (Carver's
# default estimate of daily risk in price terms; sigma_span 32, p.604,
# cited by the port's sigma_target usage).
CARRY_RISK_SPAN = 32

# Annualisation factor for daily risk (Carver convention, sqrt(256)).
TRADING_DAYS_PER_YEAR = 256.0

# Bounded carry history: the slowest smoothing span is 120, so 130
# observations let every span reach its min_periods with margin.
CARRY_HISTORY_MAX = 130


def annualized_raw_carry(near_price, further_price, near_expiry_day, further_expiry_day):
    """Annualised raw carry between two consecutive futures contracts.

    Parameters
    ----------
    near_price, further_price : float
        Close prices of the near (front) and further contracts.
    near_expiry_day, further_expiry_day : float
        Expiry dates as day counts (any consistent unit — only the
        difference matters, e.g. `.toordinal()` outputs or day offsets).

    Returns
    -------
    float or None
        `(near_price - further_price) / expiry_diff_years`, where the gap
        in years is `abs(round((further - near).days / 30)) / 12`
        (post #16001 `update`). Returns None when the gap is zero (same
        expiry: division by zero) or when prices are non-positive.
    """
    if near_price is None or further_price is None:
        return None
    if near_price <= 0.0 or further_price <= 0.0:
        return None
    if near_expiry_day is None or further_expiry_day is None:
        return None
    months_between = round((further_expiry_day - near_expiry_day) / 30.0)
    expiry_diff_years = abs(months_between) / 12.0
    if expiry_diff_years == 0.0:
        return None
    return (near_price - further_price) / expiry_diff_years


def _ewma_adjusted(values, span):
    """Exponentially weighted mean, pandas `ewm(span, adjust=True)` semantics.

    Weight of x_i is (1-alpha)^(t-i) for every i (x_0 included), with
    alpha = 2/(span+1) — the same alpha convention as `main_carver13._ewma`.
    A constant series is exactly its constant.
    """
    alpha = 2.0 / (span + 1.0)
    n = len(values)
    if n == 0:
        return None
    # Ages measured from the last point: age of x_i is (n-1-i).
    ages = np.arange(n - 1, -1, -1, dtype=float)
    weights = (1.0 - alpha) ** ages
    return float(np.dot(weights, values) / np.sum(weights))


def carry_forecasts(carry_forecast_series, spans=CARRY_SMOOTHING_SPANS,
                    scalar=CARRY_FORECAST_SCALAR, cap=CARRY_FORECAST_CAP):
    """Per-span carry forecasts from a risk-adjusted carry history.

    Parameters
    ----------
    carry_forecast_series : sequence of float
        Daily `annualized_raw_carry / daily_risk_price_terms` values,
        oldest first, most recent last (the series accumulated by the
        article's consolidation handler).
    spans : sequence of int
        EWMA smoothing spans. A span is skipped when the series is
        shorter than the span (pandas `min_periods=span` behaviour).
    scalar : float
        Carry forecast scalar (Carver p.216 -> 30.0).
    cap : float
        Symmetric absolute cap applied after scaling.

    Returns
    -------
    list of float
        One capped, scaled, smoothed forecast per span with enough
        history, most-recent-point semantics (like the article's
        `.iloc[-1]`). Empty list when no span has enough history.
    """
    series = np.asarray([float(v) for v in carry_forecast_series], dtype=float)
    forecasts = []
    for span in spans:
        if series.size < span:
            continue  # pandas min_periods=span -> empty -> `continue` in the article
        smoothed = _ewma_adjusted(series, int(span))
        if smoothed is None:
            continue
        scaled = smoothed * scalar
        forecasts.append(float(np.clip(scaled, -cap, cap)))
    return forecasts


def daily_price_risk(prices, span=CARRY_RISK_SPAN):
    """Daily risk in price terms: EWMA(|daily returns|) * last price.

    Carver's instrument-risk estimate (sigma_span 32, p.604): the expected
    absolute daily price change of the instrument, in price units. Used as
    the denominator of the carry forecast, annualised by the caller with
    sqrt(TRADING_DAYS_PER_YEAR).

    Returns None when fewer than 2 prices are given or when the smoothed
    absolute return is not strictly positive (e.g. a perfectly flat price
    series — risk-division would be undefined).
    """
    prices_arr = np.asarray([float(p) for p in prices], dtype=float)
    if prices_arr.size < 2:
        return None
    if np.any(prices_arr <= 0.0):
        return None
    abs_rets = np.abs(np.diff(prices_arr) / prices_arr[:-1])
    smoothed = _ewma_adjusted(abs_rets, int(span))
    if smoothed is None or not np.isfinite(smoothed) or smoothed <= 0.0:
        return None
    return float(smoothed * prices_arr[-1])


def risk_adjusted_carry(raw_carry, prices, span=CARRY_RISK_SPAN,
                        trading_days=TRADING_DAYS_PER_YEAR):
    """Risk-adjusted carry: annualised raw carry / annualised price risk.

    Both numerator and denominator are in price-units-per-year, so the
    ratio is dimensionless and comparable across instruments — the series
    that `carry_forecasts` then EWMA-smooths, scales (x30) and caps
    (+/-20). `raw_carry` is the output of `annualized_raw_carry`.

    Returns None when raw_carry is None (no valid term-structure
    observation today) or when the risk estimate is unavailable.
    """
    if raw_carry is None:
        return None
    daily_risk = daily_price_risk(prices, span)
    if daily_risk is None:
        return None
    annual_risk = daily_risk * np.sqrt(float(trading_days))
    if annual_risk <= 0.0:
        return None
    return float(raw_carry / annual_risk)


def blend_forecasts(trend_forecast, carry_forecast, carry_weight):
    """Carver-style trend/carry blend with leg renormalisation.

    With both legs available: `(1 - carry_weight) * trend + carry_weight
    * carry` (the article #16001 60/40 blend uses carry_weight=0.4).
    When the carry leg is None — no span of the carry history has enough
    observations yet, so `_carry_forecast` could not produce a value —
    the weight renormalises onto the available leg and the trend
    forecast is returned as-is. This mirrors the article's early-window
    behaviour (forecasts contribute only once `min_periods` is met).

    Raises ValueError on a carry_weight outside [0, 1] (a config typo
    must not silently produce an inverted blend).
    """
    if not 0.0 <= carry_weight <= 1.0:
        raise ValueError(f"carry_weight must be in [0, 1], got {carry_weight}")
    if carry_forecast is None:
        return float(trend_forecast)
    return float(
        (1.0 - carry_weight) * trend_forecast + carry_weight * carry_forecast
    )
