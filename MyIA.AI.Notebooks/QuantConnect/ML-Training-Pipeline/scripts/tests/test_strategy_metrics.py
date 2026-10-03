"""Tests for strategy_metrics.py -- the shared Sharpe, CAGR and drawdown."""

from __future__ import annotations

import math

import numpy as np
import pytest

from strategy_metrics import TRADING_DAYS, cagr, max_drawdown, sharpe, wealth


def test_sharpe_definition():
    r = np.array([0.01, -0.005, 0.002, 0.004, -0.001])
    expected = r.mean() / r.std(ddof=1) * math.sqrt(TRADING_DAYS)
    assert sharpe(r) == pytest.approx(expected, rel=1e-12)
    assert sharpe(list(r)) == pytest.approx(expected, rel=1e-12)


def test_sharpe_axis_gives_one_value_per_draw():
    rng = np.random.default_rng(0)
    draws = rng.normal(0.0005, 0.01, size=(7, 50))
    by_row = sharpe(draws, axis=1)
    assert by_row.shape == (7,)
    for k in range(7):
        assert by_row[k] == pytest.approx(sharpe(draws[k]), rel=1e-12)


def test_wealth_starts_after_first_return():
    assert wealth([0.1, -0.5]).tolist() == pytest.approx([1.1, 0.55])


def test_cagr_known_value():
    # +21 % over two years is +10 % a year.
    assert cagr([0.1, 0.1], years=2.0) == pytest.approx(0.1)


def test_cagr_needs_positive_years():
    with pytest.raises(ValueError):
        cagr([0.01, 0.02], years=0.0)


def test_max_drawdown_known_path():
    # 1.1 -> 0.55 -> 0.605 -> 1.21: the worst fall is 1.1 -> 0.55, i.e. -50 %.
    assert max_drawdown([0.1, -0.5, 0.1, 1.0]) == pytest.approx(-0.5)


def test_max_drawdown_is_zero_when_wealth_never_falls():
    assert max_drawdown([0.01, 0.0, 0.02]) == 0.0
