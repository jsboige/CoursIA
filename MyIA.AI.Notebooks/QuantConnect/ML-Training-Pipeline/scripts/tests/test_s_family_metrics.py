"""The s3-s8 scripts delegate Sharpe and max drawdown to strategy_metrics (#19016).

Each script keeps its own guard (0.0 or nan when the Sharpe is undefined) and
delegates the computation. These tests pin both halves: the delegated value is
exactly ``strategy_metrics``, and the guard still answers what the script's
docstring says.

Two groups of scripts, two histories:

- ``_sharpe`` (s3, s4, s5_lasso) used the population standard deviation
  (ddof=0). It now uses ddof=1: the standard deviation grows by
  sqrt(n / (n - 1)), so each Sharpe is multiplied by sqrt((n - 1) / n).
- ``_sharpe_ann`` (s5_hmm, s6, s7, s8) already used ddof=1: its values are
  bit-identical to the former formula, which a test below re-computes.

``_max_drawdown`` now counts the starting capital as the first peak: a path that
falls from its first return reads as a drawdown, where it used to read as 0.0.
"""

from __future__ import annotations

import importlib

import numpy as np
import pytest

import strategy_metrics

SHARPE_ZERO_GUARD = ["s3_hmm_regime", "s4_inverse_vol_ridge_v2", "s5_lasso_stop_loss"]
SHARPE_NAN_GUARD = [
    ("s5_hmm_regime_sizing", 252),
    ("s7_composite", 252),
    ("s6_cost_forecasting", 365),
    ("s8_trend_long_horizon", 365),
]
WITH_MAX_DRAWDOWN = [
    "s3_hmm_regime",
    "s4_inverse_vol_ridge_v2",
    "s5_lasso_stop_loss",
    "s5_hmm_regime_sizing",
    "s7_composite",
]


def _load(name: str):
    if name == "s8_trend_long_horizon":
        pytest.importorskip("lightgbm")
    return importlib.import_module(name)


def _paths(seed: int = 19016) -> list[np.ndarray]:
    rng = np.random.default_rng(seed)
    return [rng.normal(0.0004, 0.012, size=n) for n in (10, 37, 252, 1000)]


@pytest.mark.parametrize("name", SHARPE_ZERO_GUARD)
def test_sharpe_delegates_to_strategy_metrics(name):
    module = _load(name)
    for r in _paths():
        assert module._sharpe(r) == float(strategy_metrics.sharpe(r))


@pytest.mark.parametrize("name", SHARPE_ZERO_GUARD)
def test_sharpe_guard_returns_zero(name):
    module = _load(name)
    assert module._sharpe(np.array([0.01])) == 0.0
    assert module._sharpe(np.full(20, 0.001)) == 0.0


@pytest.mark.parametrize("name,days", SHARPE_NAN_GUARD)
def test_sharpe_ann_delegates_to_strategy_metrics(name, days):
    module = _load(name)
    for r in _paths():
        assert module._sharpe_ann(r) == float(strategy_metrics.sharpe(r, periods_per_year=days))


@pytest.mark.parametrize("name,days", SHARPE_NAN_GUARD)
def test_sharpe_ann_is_bit_identical_to_former_formula(name, days):
    module = _load(name)
    for r in _paths(seed=7):
        former = (float(np.mean(r)) / float(np.std(r, ddof=1))) * np.sqrt(days)
        assert module._sharpe_ann(r) == former


@pytest.mark.parametrize("name,days", SHARPE_NAN_GUARD)
def test_sharpe_ann_guard_returns_nan(name, days):
    module = _load(name)
    assert np.isnan(module._sharpe_ann(np.full(9, 0.01) + np.arange(9) * 1e-3))
    assert np.isnan(module._sharpe_ann(np.full(30, 0.001)))


@pytest.mark.parametrize("name", WITH_MAX_DRAWDOWN)
def test_max_drawdown_delegates_to_strategy_metrics(name):
    module = _load(name)
    for r in _paths():
        assert module._max_drawdown(r) == strategy_metrics.max_drawdown(r)


@pytest.mark.parametrize("name", WITH_MAX_DRAWDOWN)
def test_max_drawdown_counts_the_starting_capital(name):
    module = _load(name)
    # 1 -> 0.9 -> 0.945: the fall from the starting capital is -10 %.
    assert module._max_drawdown(np.array([-0.1, 0.05])) == pytest.approx(-0.1)
    assert module._max_drawdown(np.array([])) == 0.0
