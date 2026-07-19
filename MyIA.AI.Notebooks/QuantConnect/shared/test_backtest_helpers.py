#!/usr/bin/env python3
"""Pytest suite for `QuantConnect/shared/backtest_helpers.py`.

Co-located with the module under `shared/`. CPU-only, no network, no
QuantBook/QC Cloud. The module imports only stdlib + pandas + numpy (lines
20-23) and performs pure computation on equity/return Series, so it is fully
exercisable deterministically.

The module is the shared backtest-metrics helper consumed by the QuantConnect
notebook series (Sharpe/Sortino/Calmar/Max-Drawdown/Alpha-Beta) and had 0
dedicated Python test coverage before this PR.

Strategy: deterministic equity curves (no RNG) so every metric is
hand-computable or formula-pinned. Edge cases (flat equity, no negative
returns, constant benchmark) exercise the division guards.
"""
from __future__ import annotations

import importlib.util
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

# Load the module by path (it lives under shared/, stdlib + pandas + numpy
# only, no package-relative imports -> no sys.path manipulation needed).
_MODULE_PATH = Path(__file__).resolve().parent / "backtest_helpers.py"
_spec = importlib.util.spec_from_file_location("backtest_helpers", _MODULE_PATH)
bt = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(bt)


# --------------------------------------------------------------------------
# Deterministic fixtures
# --------------------------------------------------------------------------


def _equity(values, start="2020-01-01"):
    """Build a dated equity Series from a plain list of levels."""
    idx = pd.date_range(start, periods=len(values), freq="D")
    return pd.Series(values, index=idx, dtype=float)


# --------------------------------------------------------------------------
# default_backtest_config
# --------------------------------------------------------------------------


def test_default_backtest_config_defaults():
    cfg = bt.default_backtest_config()
    assert cfg["start_date"] == "2020-01-01"
    assert cfg["end_date"] == "2023-12-31"
    assert cfg["initial_capital"] == 100000
    assert cfg["resolution"] == "Daily"


def test_default_backtest_config_keys():
    cfg = bt.default_backtest_config()
    for key in (
        "start_date", "end_date", "initial_capital", "resolution",
        "brokerage_model", "slippage_model", "fill_model", "fee_model",
        "benchmark",
    ):
        assert key in cfg


def test_default_backtest_config_overrides_propagate():
    cfg = bt.default_backtest_config(
        start="2021-06-01", end="2022-06-01",
        initial_capital=50000, resolution="Minute",
    )
    assert cfg["start_date"] == "2021-06-01"
    assert cfg["end_date"] == "2022-06-01"
    assert cfg["initial_capital"] == 50000
    assert cfg["resolution"] == "Minute"
    # Untouched defaults remain.
    assert cfg["benchmark"] == "SPY"


# --------------------------------------------------------------------------
# calculate_metrics — basic structure + hand-computed values
# --------------------------------------------------------------------------


def test_calculate_metrics_keys_present():
    m = bt.calculate_metrics(_equity([100, 110, 121]))
    for key in (
        "total_return", "annualized_return", "volatility", "sharpe_ratio",
        "sortino_ratio", "max_drawdown", "calmar_ratio", "win_rate",
        "alpha", "beta", "total_trades",
    ):
        assert key in m


def test_calculate_metrics_total_return_known():
    # equity [100, 110, 121] -> total return = 21/100 = 0.21
    m = bt.calculate_metrics(_equity([100, 110, 121]))
    assert m["total_return"] == pytest.approx(0.21)


def test_calculate_metrics_flat_equity_zero_total_return():
    m = bt.calculate_metrics(_equity([100.0, 100.0, 100.0, 100.0]))
    assert m["total_return"] == pytest.approx(0.0)


def test_calculate_metrics_flat_equity_zero_volatility_sharpe():
    # Constant equity -> all returns 0 -> volatility 0 -> Sharpe guard -> 0.0
    m = bt.calculate_metrics(_equity([100.0, 100.0, 100.0, 100.0]))
    assert m["volatility"] == pytest.approx(0.0)
    assert m["sharpe_ratio"] == 0.0


def test_calculate_metrics_max_drawdown_value_and_negative_sign():
    # equity [100, 120, 90]: peak 120 then 90 -> drawdown to -25%
    #   returns = [0.2, -0.25]; cumulative = [1.2, 0.9]; drawdown = [0, -0.25]
    m = bt.calculate_metrics(_equity([100, 120, 90]))
    assert m["max_drawdown"] <= 0  # drawdown reported as negative depth
    assert m["max_drawdown"] == pytest.approx(-0.25)


def test_calculate_metrics_win_rate_half():
    # equity [100, 110, 100]: returns = [+0.1, ~-0.0909] -> 1 of 2 positive
    m = bt.calculate_metrics(_equity([100, 110, 100]))
    assert m["win_rate"] == pytest.approx(0.5)


def test_calculate_metrics_calmar_uses_abs_max_drawdown():
    # Calmar = annualized_return / abs(max_drawdown) -> positive when positive
    # annualized return and a real drawdown.
    m = bt.calculate_metrics(_equity([100, 120, 110]))
    assert m["max_drawdown"] < 0
    assert m["calmar_ratio"] >= 0


def test_calculate_metrics_no_negative_returns_sortino_zero():
    # Strictly increasing equity -> all positive returns -> no downside -> the
    # std-of-empty is NaN -> guard (NaN > 0 is False) -> Sortino 0.0.
    m = bt.calculate_metrics(_equity([100, 101, 102, 103]))
    assert m["sortino_ratio"] == 0.0


def test_calculate_metrics_sharpe_positive_on_monotonic_growth():
    m = bt.calculate_metrics(_equity([100, 110, 121, 133]))
    # Positive excess return with finite volatility -> positive Sharpe.
    assert m["sharpe_ratio"] > 0
    assert np.isfinite(m["sharpe_ratio"])


# --------------------------------------------------------------------------
# calculate_metrics — alpha/beta with benchmark
# --------------------------------------------------------------------------


def test_calculate_metrics_with_benchmark_returns_finite_alpha_beta():
    equity = _equity([100, 102, 101, 105, 108])
    benchmark = _equity([100, 101, 103, 102, 106])
    m = bt.calculate_metrics(equity, benchmark=benchmark)
    assert np.isfinite(m["beta"])
    assert np.isfinite(m["alpha"])


def test_calculate_metrics_constant_benchmark_beta_defaults_to_one():
    # Constant benchmark -> zero variance -> beta guard -> 1.0 default.
    equity = _equity([100, 110, 105])
    benchmark = _equity([100.0, 100.0, 100.0])
    m = bt.calculate_metrics(equity, benchmark=benchmark)
    assert m["beta"] == 1.0


def test_calculate_metrics_without_benchmark_alpha_beta_defaults():
    m = bt.calculate_metrics(_equity([100, 110, 121]))
    # No benchmark -> alpha 0.0, beta 1.0 (initial defaults, unchanged).
    assert m["alpha"] == 0.0
    assert m["beta"] == 1.0


# --------------------------------------------------------------------------
# format_backtest_summary
# --------------------------------------------------------------------------


def test_format_backtest_summary_contains_strategy_name():
    summary = bt.format_backtest_summary(
        {"total_return": 0.25, "sharpe_ratio": 1.5}, "Alpha Strat"
    )
    assert "Alpha Strat" in summary


def test_format_backtest_summary_formats_percentages():
    summary = bt.format_backtest_summary(
        {"total_return": 0.25, "sharpe_ratio": 1.5,
         "max_drawdown": -0.15, "win_rate": 0.55}, "S"
    )
    assert "25.00%" in summary
    assert "-15.00%" in summary
    assert "55.00%" in summary


def test_format_backtest_summary_handles_missing_keys():
    # Missing metrics default to 0 via .get(..., 0) -> no KeyError, still a str.
    summary = bt.format_backtest_summary({}, "Empty")
    assert isinstance(summary, str)
    assert "Empty" in summary


# --------------------------------------------------------------------------
# compare_strategies
# --------------------------------------------------------------------------


def test_compare_strategies_indexes_by_name_and_length():
    s1 = _equity([100, 110, 121])
    s2 = _equity([100, 105, 100])
    df = bt.compare_strategies({"A": s1, "B": s2})
    assert list(df.index) == ["A", "B"]
    assert len(df) == 2


def test_compare_strategies_default_columns():
    df = bt.compare_strategies({"A": _equity([100, 110, 121])})
    for col in ("total_return", "sharpe_ratio", "max_drawdown",
                "volatility", "win_rate"):
        assert col in df.columns


def test_compare_strategies_custom_metrics_respected():
    df = bt.compare_strategies(
        {"A": _equity([100, 110, 121])},
        metrics_to_compare=["total_return", "win_rate"],
    )
    assert list(df.columns) == ["total_return", "win_rate"]


# --------------------------------------------------------------------------
# is_trading_day
# --------------------------------------------------------------------------


def test_is_trading_day_weekday_true():
    # 2023-01-02 is a Monday.
    assert bt.is_trading_day(datetime(2023, 1, 2)) is True


@pytest.mark.parametrize("dt,expected", [
    (datetime(2023, 1, 7), False),  # Saturday
    (datetime(2023, 1, 8), False),  # Sunday
])
def test_is_trading_day_weekend_false(dt, expected):
    assert bt.is_trading_day(dt) is expected


# --------------------------------------------------------------------------
# annualized_sharpe
# --------------------------------------------------------------------------


def test_annualized_sharpe_matches_formula():
    # Pin the documented arithmetic formula: (mean*252 - rf) / (std*sqrt(252)).
    returns = pd.Series([0.01, 0.005, -0.002, 0.012, 0.008, -0.003])
    rf = 0.02
    expected = (returns.mean() * 252 - rf) / (returns.std() * np.sqrt(252))
    assert bt.annualized_sharpe(returns, rf) == pytest.approx(expected)


def test_annualized_sharpe_empty_returns_zero():
    assert bt.annualized_sharpe(pd.Series([], dtype=float)) == 0.0


def test_annualized_sharpe_zero_std_returns_zero():
    # Constant returns -> std 0 -> guard -> 0.0
    assert bt.annualized_sharpe(pd.Series([0.01, 0.01, 0.01])) == 0.0


def test_annualized_sharpe_returns_float():
    out = bt.annualized_sharpe(pd.Series([0.01, 0.02, -0.005]))
    assert isinstance(out, float)
