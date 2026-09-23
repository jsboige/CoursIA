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
    carry_forecast         = annualized_raw_carry / daily_risk_price_terms
    smoothed(span)         = EWMA_span(carry_forecast)[-1]   (min_periods=span)
    scaled(span)           = smoothed * CARRY_FORECAST_SCALAR
    capped(span)           = clip(scaled, -CAP, +CAP)

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
