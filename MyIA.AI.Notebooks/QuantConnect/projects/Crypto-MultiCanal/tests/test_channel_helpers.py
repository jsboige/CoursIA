# -*- coding: utf-8 -*-
"""Unit tests for ``Crypto-MultiCanal/channel_helpers.py`` pure geometry helpers.

``channel_helpers.py`` implements the channel-detection geometry (slope/intercept
of trend lines through price pivots, point-vs-line containment, nested-envelope
checks, the classic ZigZag pivot extractor) used by the Crypto-MultiCanal
strategy. Unlike most QuantConnect project modules it depends only on
``numpy`` / ``pandas`` / ``math`` (NOT ``AlgorithmImports``), so its geometry
helpers are unit-testable in pure Python without the QC Lean environment.

The strategy-facing entry points (``find_envelope_line``,
``find_best_channel_line_strict_weighted``) take elaborately-shaped pivot
DataFrames and are exercised through the strategy backtest; this file pins the
**leaf geometry primitives** they compose from, which had zero direct coverage.

Run from the repo root::

    python -m pytest MyIA.AI.Notebooks/QuantConnect/projects/Crypto-MultiCanal/tests/test_channel_helpers.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

# Make the sibling ``channel_helpers.py`` importable (no package __init__).
_HERE = Path(__file__).resolve().parent
_SRC = _HERE.parent
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))

from channel_helpers import (  # noqa: E402
    _check_nesting,
    check_point_position,
    classic_chart_zigzag,
    get_channel_value_at_time,
    get_line_params_time,
)


# ---------------------------------------------------------------------------
# get_line_params_time
# ---------------------------------------------------------------------------
def test_line_params_simple_slope_intercept():
    """Two points (0,100) and (10,200) -> slope=10, intercept=100."""
    m, c = get_line_params_time(0, 100, 10, 200)
    assert m == pytest.approx(10.0)
    assert c == pytest.approx(100.0)


def test_line_params_negative_slope():
    """Descending line (0,200)->(10,100) -> slope=-10, intercept=200."""
    m, c = get_line_params_time(0, 200, 10, 100)
    assert m == pytest.approx(-10.0)
    assert c == pytest.approx(200.0)


def test_line_params_vertical_returns_inf():
    """Two points at the same time (vertical line) -> slope=inf, intercept=t1.

    A vertical line cannot be expressed as y = m*t + c; the helper signals it
    with slope=inf and returns the (numeric) time as the intercept placeholder
    so downstream consumers can detect and skip it.
    """
    m, c = get_line_params_time(5, 100, 5, 200)  # dt = 0
    assert m == float("inf")
    assert c == pytest.approx(5.0)


# ---------------------------------------------------------------------------
# check_point_position
# ---------------------------------------------------------------------------
def test_point_position_above_line_true_when_above():
    """check_above=True: a point above the line returns True."""
    # line: y = 10*t + 100 -> at t=5, line_y=150. Point at 300 is above.
    assert check_point_position(5, 300, 10, 100, check_above=True) is True


def test_point_position_above_line_false_when_below():
    """check_above=True: a point well below the line returns False."""
    # at t=5 line_y=150. Point at 50 is below.
    assert check_point_position(5, 50, 10, 100, check_above=True) is False


def test_point_position_below_line_true_when_below():
    """check_above=False (support check): a point below the line returns True."""
    assert check_point_position(5, 50, 10, 100, check_above=False) is True


def test_point_position_below_line_false_when_above():
    """check_above=False: a point above the line returns False."""
    assert check_point_position(5, 300, 10, 100, check_above=False) is False


def test_point_position_vertical_line_returns_false():
    """A vertical line (m=inf) never classifies a point (no y = m*t+c)."""
    assert check_point_position(5, 300, float("inf"), 5, check_above=True) is False
    assert check_point_position(5, 50, float("inf"), 5, check_above=False) is False


# ---------------------------------------------------------------------------
# get_channel_value_at_time
# ---------------------------------------------------------------------------
def test_channel_value_at_time_line_value():
    """Channel through (0,100)-(10,200): value at t=5 is 150 (midpoint)."""
    p1 = {"time_numeric": 0, "price": 100}
    p2 = {"time_numeric": 10, "price": 200}
    assert get_channel_value_at_time((p1, p2), 5) == pytest.approx(150.0)


def test_channel_value_at_time_none_or_nan_pivots():
    """Missing / NaN pivots -> NaN (graceful, no exception)."""
    assert np.isnan(get_channel_value_at_time(None, 5))
    assert np.isnan(get_channel_value_at_time((None, None), 5))
    p_nan = {"time_numeric": float("nan"), "price": 100}
    p_ok = {"time_numeric": 10, "price": 200}
    assert np.isnan(get_channel_value_at_time((p_nan, p_ok), 5))


def test_channel_value_at_time_vertical_returns_nan():
    """A vertical channel (same time) cannot be evaluated -> NaN."""
    p1 = {"time_numeric": 5, "price": 100}
    p2 = {"time_numeric": 5, "price": 200}
    assert np.isnan(get_channel_value_at_time((p1, p2), 5))


# ---------------------------------------------------------------------------
# _check_nesting
# ---------------------------------------------------------------------------
def test_check_nesting_resistance_inner_below_outer():
    """For resistance, inner must stay <= outer across [t_start, t_end]."""
    # outer: y = 2t + 100 ; inner: y = t + 100 -> inner always below outer for t>=0.
    assert _check_nesting(1, 100, 2, 100, t_start=0, t_end=10,
                          is_resistance=True) is True


def test_check_nesting_resistance_violation():
    """Inner crossing above outer at any check point -> False."""
    # outer: y = 0t + 100 (flat) ; inner: y = 5t + 0 -> inner=50 at t=10 > 100? no.
    # Use inner that exceeds: inner = 20t + 0, outer = 0t + 100 -> at t=5 inner=100, t=10 inner=200 > 100.
    assert _check_nesting(20, 0, 0, 100, t_start=0, t_end=10,
                          is_resistance=True) is False


def test_check_nesting_support_inner_above_outer():
    """For support, inner must stay >= outer across [t_start, t_end]."""
    # outer: y = 0t + 50 ; inner: y = 0t + 100 -> inner always above. OK for support.
    assert _check_nesting(0, 100, 0, 50, t_start=0, t_end=10,
                          is_resistance=False) is True


def test_check_nesting_support_violation():
    """Support: inner dipping below outer -> False."""
    # outer: y = 0t + 100 ; inner: y = -20t + 0 -> at t=10 inner=-200 < 100.
    assert _check_nesting(-20, 0, 0, 100, t_start=0, t_end=10,
                          is_resistance=False) is False


# ---------------------------------------------------------------------------
# classic_chart_zigzag
# ---------------------------------------------------------------------------
def _zigzag_df(closes):
    """Build the minimal df shape classic_chart_zigzag consumes: close + time."""
    return pd.DataFrame({
        "close": closes,
        "time": np.arange(len(closes), dtype=float),
    })


def test_zigzag_too_short_returns_empty():
    """Fewer than 2 rows -> no pivot can be formed -> empty list."""
    assert classic_chart_zigzag(_zigzag_df([100]), threshold_percent=0.05) == []


def test_zigzag_monotonic_uptrend_single_direction():
    """A purely rising series produces a single low pivot then a high pivot."""
    closes = [100, 105, 110, 115, 120, 125, 130]
    pivots = classic_chart_zigzag(_zigzag_df(closes), threshold_percent=0.05)
    # First pivot is always seeded at index 0.
    assert len(pivots) >= 1
    assert pivots[0]["price"] == 100
    assert pivots[0]["type"] == 1  # +1 = Low (direction_up seed)


def test_zigzag_reversal_emits_alternating_pivots():
    """A clear up-then-down reversal emits a high pivot at the peak."""
    # Up 100->130, then down 130->90 (>5% retrace from 130).
    closes = [100, 110, 120, 130, 120, 110, 100, 90]
    pivots = classic_chart_zigzag(_zigzag_df(closes), threshold_percent=0.05)
    # Expect at least: low@100, high@130, then low@<=100 on the retrace.
    prices = [p["price"] for p in pivots]
    assert 100 in prices
    assert 130 in prices
    # Pivot types must alternate (no two consecutive same-type after the seed).
    types = [p["type"] for p in pivots]
    for a, b in zip(types, types[1:]):
        assert a != b, f"consecutive pivots same type {a}: {types}"


def test_zigzag_threshold_filters_small_moves():
    """A higher threshold ignores small reversals (fewer pivots)."""
    closes = [100, 102, 101, 103, 100, 105]  # small wiggles ~2-3%
    low_thr = classic_chart_zigzag(_zigzag_df(closes), threshold_percent=0.01)
    high_thr = classic_chart_zigzag(_zigzag_df(closes), threshold_percent=0.50)
    # A 50% threshold tolerates everything -> only the seed pivot remains.
    assert len(high_thr) <= len(low_thr)
