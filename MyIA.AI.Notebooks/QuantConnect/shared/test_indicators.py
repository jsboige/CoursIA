#!/usr/bin/env python3
"""Pytest suite for `QuantConnect/shared/indicators.py`.

Co-located with the module under `shared/`. CPU-only, no network, no LEAN
engine, no QuantBook. The module imports only typing + numpy (lines 20-21)
and defines 3 stateful LEAN-style indicator classes + an IndicatorValue
helper, all exercised by feeding deterministic (high, low, close) bars via
the `.Update()` warm-up API.

The module is consumed by notebooks 11 and 18 (Technical Indicators, Feature
Engineering) and had 0 dedicated Python test coverage before this PR.

Strategy: feed hand-picked price/bar sequences so every indicator value is
hand-computable. Warm-up, window-slide, readiness threshold, division guards
(old_price=0, flat-move), and Reset are all pinned.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

# Load the module by path (lives under shared/, typing + numpy only, no
# package-relative imports -> no sys.path manipulation needed).
_MODULE_PATH = Path(__file__).resolve().parent / "indicators.py"
_spec = importlib.util.spec_from_file_location("indicators", _MODULE_PATH)
ind = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ind)

CustomMomentumIndicator = ind.CustomMomentumIndicator
TrendStrengthIndicator = ind.TrendStrengthIndicator
VolatilityBandIndicator = ind.VolatilityBandIndicator
IndicatorValue = ind.IndicatorValue


# --------------------------------------------------------------------------
# IndicatorValue
# --------------------------------------------------------------------------


def test_indicator_value_float_cast():
    iv = IndicatorValue(1.5)
    assert float(iv) == 1.5


def test_indicator_value_repr_rounds_to_four_decimals():
    assert repr(IndicatorValue(0.123456)) == "IndicatorValue(0.1235)"


def test_indicator_value_default_time_is_none():
    iv = IndicatorValue(2.0)
    assert iv.Time is None
    assert iv.Value == 2.0


# --------------------------------------------------------------------------
# CustomMomentumIndicator
# --------------------------------------------------------------------------


def test_momentum_not_ready_before_period_bars():
    m = CustomMomentumIndicator("mom", period=3)
    m.Update(None, 100)
    m.Update(None, 110)
    assert m.IsReady is False


def test_momentum_ready_and_value_at_period():
    # period=3, prices [100, 110, 121] -> old=100, cur=121 -> 0.21
    m = CustomMomentumIndicator("mom", period=3)
    for p in (100, 110, 121):
        m.Update(None, p)
    assert m.IsReady is True
    assert float(m.Current) == pytest.approx(0.21)


def test_momentum_window_slides_on_new_bar():
    # After the 4th bar (130), the first price (100) drops off the window;
    # window becomes [110, 121, 130] -> old=110, cur=130 -> 20/110.
    m = CustomMomentumIndicator("mom", period=3)
    for p in (100, 110, 121, 130):
        m.Update(None, p)
    assert float(m.Current) == pytest.approx(20 / 110)


def test_momentum_zero_division_guard_when_old_price_zero():
    # old_price=0 must not raise; momentum falls back to 0.0.
    m = CustomMomentumIndicator("mom", period=2)
    m.Update(None, 0)
    m.Update(None, 100)
    assert m.IsReady is True
    assert float(m.Current) == 0.0


def test_momentum_reset_clears_state():
    m = CustomMomentumIndicator("mom", period=2)
    m.Update(None, 100)
    m.Update(None, 110)
    assert m.IsReady is True
    m.Reset()
    assert m.IsReady is False
    assert m.prices == []
    assert float(m.Current) == 0.0


def test_momentum_default_period_is_20():
    m = CustomMomentumIndicator("mom")
    assert m.period == 20
    assert m.Name == "mom"


# --------------------------------------------------------------------------
# TrendStrengthIndicator
# --------------------------------------------------------------------------


def test_trend_strength_monotonic_up_is_plus_one():
    # Strictly increasing closes -> all moves up -> strength +1.0
    t = TrendStrengthIndicator("trend", period=4)
    for c in (1, 2, 3, 4, 5, 6):
        t.Update(None, high=c + 1, low=c - 1, close=c)
    assert t.IsReady is True
    assert float(t.Current) == pytest.approx(1.0)


def test_trend_strength_monotonic_down_is_minus_one():
    t = TrendStrengthIndicator("trend", period=4)
    for c in (6, 5, 4, 3, 2, 1):
        t.Update(None, high=c + 1, low=c - 1, close=c)
    assert float(t.Current) == pytest.approx(-1.0)


def test_trend_strength_alternating_is_zero():
    # closes 1,2,1,2,1 -> equal up/down moves -> strength 0.0
    t = TrendStrengthIndicator("trend", period=4)
    for c in (1, 2, 1, 2, 1):
        t.Update(None, high=c + 1, low=c - 1, close=c)
    assert float(t.Current) == pytest.approx(0.0)


def test_trend_strength_all_flat_is_neutral_zero():
    # Regression guard: previously `moves_down = (len-1) - moves_up` bucketed
    # flat moves (close[i] == close[i-1]) as "down", so an all-flat series
    # reported strength = -1.0 (maximally bearish) for a flat market -- and the
    # `moves_up + moves_down == 0` guard was dead (sum == len-1 for len >= 2).
    # Now moves_down is counted explicitly with `<`, flat moves are excluded
    # from both buckets, and the guard fires for all-flat -> 0.0 (neutral
    # range/consolidation), matching the interpretation documented in the
    # notebook ("0.0 : Range/consolidation").
    t = TrendStrengthIndicator("trend", period=4)
    for _ in range(5):
        t.Update(None, high=6, low=4, close=5)
    assert t.IsReady is True
    assert float(t.Current) == pytest.approx(0.0)


def test_trend_strength_mixed_with_flat_excludes_flat():
    # Series [1, 2, 2, 2, 3]: moves up = 2 (1->2, 2->3), moves down = 0, flat
    # moves = 2. Previously the 2 flat moves were bucketed as down, dragging
    # strength to (2 - 2) / 4 = 0.0 (falsely "range"). Now flat moves are
    # excluded -> (2 - 0) / 2 = 1.0 (correctly strong uptrend: price rose, no
    # down bars). This is the broader blast radius of the flat-bucketing fix.
    t = TrendStrengthIndicator("trend", period=4)
    for c in (1, 2, 2, 2, 3):
        t.Update(None, high=c + 1, low=c - 1, close=c)
    assert t.IsReady is True
    assert float(t.Current) == pytest.approx(1.0)


def test_trend_strength_reset_clears_state():
    t = TrendStrengthIndicator("trend", period=3)
    for c in (1, 2, 3, 4):
        t.Update(None, high=c + 1, low=c - 1, close=c)
    assert t.IsReady is True
    t.Reset()
    assert t.IsReady is False
    assert t.close_prices == []


# --------------------------------------------------------------------------
# VolatilityBandIndicator
# --------------------------------------------------------------------------


def test_vol_band_not_ready_before_period():
    vb = VolatilityBandIndicator("vb", period=3)
    vb.Update(None, high=2, low=0, close=1)
    vb.Update(None, high=2, low=0, close=1)
    assert vb.IsReady is False


def test_vol_band_known_values_and_symmetric_width():
    # period=2, bars: (H,L,C) = (101,99,100), (103,101,102)
    #   middle = mean([100,102]) = 101
    #   TR at i=1: max(H-L=103-101=2, |H-Cprev|=|103-100|=3, |L-Cprev|=|101-100|=1) = 3
    #   atr = mean([3]) = 3 ; multiplier=2 -> width = 6
    #   upper = 101+6 = 107 ; lower = 101-6 = 95
    vb = VolatilityBandIndicator("vb", period=2, multiplier=2.0)
    vb.Update(None, high=101, low=99, close=100)
    vb.Update(None, high=103, low=101, close=102)
    assert vb.IsReady is True
    assert float(vb.MiddleBand) == pytest.approx(101.0)
    assert float(vb.UpperBand) == pytest.approx(107.0)
    assert float(vb.LowerBand) == pytest.approx(95.0)
    # Symmetric around the SMA.
    assert float(vb.UpperBand) - float(vb.MiddleBand) == pytest.approx(
        float(vb.MiddleBand) - float(vb.LowerBand)
    )


def test_vol_band_zero_atr_when_constant_bars():
    # Constant bars -> every TR component is 0 -> atr 0 -> bands == middle.
    vb = VolatilityBandIndicator("vb", period=3, multiplier=2.0)
    for _ in range(3):
        vb.Update(None, high=100, low=100, close=100)
    assert float(vb.UpperBand) == pytest.approx(100.0)
    assert float(vb.MiddleBand) == pytest.approx(100.0)
    assert float(vb.LowerBand) == pytest.approx(100.0)


def test_vol_band_reset_clears_state():
    vb = VolatilityBandIndicator("vb", period=2)
    vb.Update(None, high=2, low=0, close=1)
    vb.Update(None, high=2, low=0, close=1)
    assert vb.IsReady is True
    vb.Reset()
    assert vb.IsReady is False
    assert vb.close_prices == []
    assert float(vb.UpperBand) == 0.0
