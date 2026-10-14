"""The m11j-m15 scripts delegate Sharpe and max drawdown to strategy_metrics (#19016).

Each script keeps its own guard (nan for fewer than 10 returns or a flat path)
and delegates the computation. These tests pin both halves: the delegated value
is exactly ``strategy_metrics``, and the guard still answers nan.

``_sharpe_ann`` already used ddof=1 in every script: its values are
bit-identical to the former formula, which a test below re-computes.

``_max_drawdown`` (m11j only) now counts the starting capital as the first
peak: a path that falls from its first return reads as a drawdown, where it
used to read as 0.0. Its nan guard for fewer than 10 returns is kept.
"""

from __future__ import annotations

import importlib

import numpy as np
import pytest

import strategy_metrics

SHARPE_NAN_GUARD = [
    ("m11j_multi_asset_kelly", 365),
    ("m12_har_rv_j", 365),
    ("m12_hf_compare", 365),
    ("m12_hf_har_rv_j", 365),
    ("m13_ms_har", 365),
    ("m14_heavy", 365),
    ("m15_cross_asset_lstm", 252),
    ("m15_lstm_rv", 365),
]


def _load(name: str):
    # torch, statsmodels and scipy.stats are imported inside functions: every
    # script loads without them, so no test is skipped.
    return importlib.import_module(name)


def _paths(seed: int = 19016) -> list[np.ndarray]:
    rng = np.random.default_rng(seed)
    return [rng.normal(0.0004, 0.012, size=n) for n in (10, 37, 365, 1000)]


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


def test_m11j_max_drawdown_delegates_to_strategy_metrics():
    module = _load("m11j_multi_asset_kelly")
    for r in _paths():
        assert module._max_drawdown(r) == strategy_metrics.max_drawdown(r)


def test_m11j_max_drawdown_counts_the_starting_capital():
    module = _load("m11j_multi_asset_kelly")
    # 1 -> 0.9 (flat) -> 0.945: the fall from the starting capital is -10 %.
    path = np.array([-0.1] + [0.0] * 8 + [0.05])
    assert module._max_drawdown(path) == pytest.approx(-0.1)


def test_m11j_max_drawdown_guard_returns_nan():
    module = _load("m11j_multi_asset_kelly")
    assert np.isnan(module._max_drawdown(np.array([-0.1, 0.05])))
