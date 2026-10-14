"""The tranche-4 scripts delegate Sharpe and max drawdown to strategy_metrics (#19016).

Two RL/DT lineages of the pipeline, two histories:

- ``_sharpe_ann`` (s2_v2_vol_ensemble_dm, L3_trend_long_horizon_gpu) already used
  ddof=1: its values are bit-identical to the former formula, which a test below
  re-computes.
- ``compute_sharpe`` (ablation_rtg_leak, sweep_l4_decision_transformer,
  sweep_l6_dt_extension, eval_rl_dt) used the population standard deviation
  (ddof=0; ``baselines.sharpe_from_returns`` for the last one). It now uses
  ddof=1: the standard deviation grows by sqrt(n / (n - 1)), so each Sharpe is
  multiplied by sqrt((n - 1) / n).

Each script keeps its own guard (0.0 or nan) and its own annualisation factor.
``eval_rl_dt.compute_max_drawdown`` changes convention, not only precision: it
took a cumulative-sum path normalised by ``abs(peak) + 1e-8`` and now takes the
returns series, like the shared definition; both call sites were updated with it.
"""

from __future__ import annotations

import importlib
import math

import numpy as np
import pytest

import strategy_metrics

SHARPE_ANN_NAN_GUARD = [
    ("s2_v2_vol_ensemble_dm", 365),
    ("L3_trend_long_horizon_gpu", 252),
]
SHARPE_ZERO_GUARD = [
    ("ablation_rtg_leak", 252),
    ("sweep_l4_decision_transformer", 252),
    ("sweep_l6_dt_extension", 252),
]
EVAL = "eval_rl_dt"


def _load(name: str):
    # torch and statsmodels are imported at module scope by these scripts: the
    # pipeline's own requirements provide them, so no test is conditionally skipped.
    return importlib.import_module(name)


def _paths(seed: int = 19016) -> list[np.ndarray]:
    rng = np.random.default_rng(seed)
    return [rng.normal(0.0004, 0.012, size=n) for n in (10, 37, 252, 1000)]


@pytest.mark.parametrize("name,days", SHARPE_ANN_NAN_GUARD)
def test_sharpe_ann_delegates_to_strategy_metrics(name, days):
    module = _load(name)
    for r in _paths():
        assert module._sharpe_ann(r) == float(
            strategy_metrics.sharpe(r, periods_per_year=days))


@pytest.mark.parametrize("name,days", SHARPE_ANN_NAN_GUARD)
def test_sharpe_ann_is_bit_identical_to_former_formula(name, days):
    module = _load(name)
    for r in _paths(seed=7):
        former = (float(np.mean(r)) / float(np.std(r, ddof=1))) * np.sqrt(days)
        assert module._sharpe_ann(r) == former


@pytest.mark.parametrize("name,days", SHARPE_ANN_NAN_GUARD)
def test_sharpe_ann_guard_returns_nan(name, days):
    module = _load(name)
    assert np.isnan(module._sharpe_ann(np.full(9, 0.01) + np.arange(9) * 1e-3))
    assert np.isnan(module._sharpe_ann(np.full(30, 0.001)))


@pytest.mark.parametrize("name,days", SHARPE_ZERO_GUARD)
def test_compute_sharpe_delegates_to_strategy_metrics(name, days):
    module = _load(name)
    for r in _paths():
        assert module.compute_sharpe(r) == float(
            strategy_metrics.sharpe(r, periods_per_year=days))


@pytest.mark.parametrize("name,days", SHARPE_ZERO_GUARD)
def test_compute_sharpe_grows_by_the_ddof_factor(name, days):
    module = _load(name)
    for r in _paths(seed=7):
        former = float(np.mean(r)) / float(np.std(r)) * np.sqrt(days)
        n = len(r)
        assert module.compute_sharpe(r) == pytest.approx(
            former * math.sqrt((n - 1) / n), rel=1e-12)
        assert module.compute_sharpe(r) != former  # the ddof=0 value is gone


@pytest.mark.parametrize("name,days", SHARPE_ZERO_GUARD)
def test_compute_sharpe_guard_returns_zero(name, days):
    module = _load(name)
    assert module.compute_sharpe(np.full(9, 0.01) + np.arange(9) * 1e-3) == 0.0
    assert module.compute_sharpe(np.full(30, 0.001)) == 0.0


def test_compute_sharpe_annual_factor_is_honoured():
    module = _load("sweep_l4_decision_transformer")
    r = _paths()[2]
    assert module.compute_sharpe(r, annual_factor=365) == float(
        strategy_metrics.sharpe(r, periods_per_year=365))
    assert module.compute_sharpe(r, annual_factor=365) != module.compute_sharpe(r)


def test_eval_rl_dt_compute_sharpe_delegates():
    module = _load(EVAL)
    for r in _paths():
        assert module.compute_sharpe(r) == float(
            strategy_metrics.sharpe(r, periods_per_year=252))


def test_eval_rl_dt_compute_sharpe_grows_by_the_ddof_factor():
    module = _load(EVAL)
    for r in _paths(seed=7):
        former = float(np.mean(r)) / float(np.std(r)) * np.sqrt(252)
        n = len(r)
        assert module.compute_sharpe(r) == pytest.approx(
            former * math.sqrt((n - 1) / n), rel=1e-12)


def test_eval_rl_dt_annualize_false_is_per_period():
    module = _load(EVAL)
    r = _paths()[2]
    per_period = module.compute_sharpe(r, annualize=False)
    assert per_period == float(strategy_metrics.sharpe(r, periods_per_year=1))
    assert module.compute_sharpe(r, annualize=True) == pytest.approx(
        per_period * math.sqrt(252), rel=1e-12)


def test_eval_rl_dt_compute_sharpe_guard_returns_zero():
    module = _load(EVAL)
    assert module.compute_sharpe(np.array([])) == 0.0
    assert module.compute_sharpe(np.array([0.01])) == 0.0
    assert module.compute_sharpe(np.full(30, 0.001)) == 0.0


def test_eval_rl_dt_max_drawdown_delegates():
    module = _load(EVAL)
    for r in _paths():
        assert module.compute_max_drawdown(r) == strategy_metrics.max_drawdown(r)


def test_eval_rl_dt_max_drawdown_takes_returns_not_a_path():
    module = _load(EVAL)
    # The former signature took a cumulative-sum path. The same numbers now read
    # as returns: wealth 1 -> 1.2 -> 1.14 -> 1.368 is a -5 % dip from the peak.
    assert module.compute_max_drawdown(np.array([0.2, -0.05, 0.2])) == pytest.approx(-0.05)
    # A path whose wealth only rises has no drawdown at all.
    assert module.compute_max_drawdown(np.array([0.01] * 20)) == 0.0


def test_eval_rl_dt_max_drawdown_guard_returns_zero():
    module = _load(EVAL)
    assert module.compute_max_drawdown(np.array([])) == 0.0
    assert module.compute_max_drawdown(np.array([1.0])) == 0.0
