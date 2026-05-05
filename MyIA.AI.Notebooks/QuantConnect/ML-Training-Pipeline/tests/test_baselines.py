"""Tests for baselines.py -- baseline models for direction prediction."""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from baselines import (
    buy_and_hold_baseline,
    majority_class_baseline,
    naive_momentum_baseline,
    random_walk_baseline,
)


@pytest.fixture
def prices():
    np.random.seed(42)
    n = 500
    return pd.Series(100.0 + np.cumsum(np.random.randn(n) * 0.5))


class TestMajorityClassBaseline:
    def test_balanced(self):
        y_train = np.array([0, 1, 0, 1, 0, 1])
        y_test = np.array([0, 1, 0, 1])
        result = majority_class_baseline(y_train, y_test)
        assert result["accuracy"] == pytest.approx(0.5, abs=0.01)

    def test_all_up(self):
        y_train = np.ones(100)
        y_test = np.ones(20)
        result = majority_class_baseline(y_train, y_test)
        assert result["accuracy"] == 1.0
        assert result["majority_class"] == 1

    def test_all_down(self):
        y_train = np.zeros(100)
        y_test = np.zeros(20)
        result = majority_class_baseline(y_train, y_test)
        assert result["accuracy"] == 1.0
        assert result["majority_class"] == 0

    def test_output_keys(self):
        y_train = np.array([0, 1] * 50)
        y_test = np.array([0, 1] * 10)
        result = majority_class_baseline(y_train, y_test)
        for key in ["accuracy", "majority_class", "majority_freq", "n_train", "n_test"]:
            assert key in result

    def test_series_input(self):
        y_train = pd.Series([0, 1, 0, 1])
        y_test = pd.Series([0, 1])
        result = majority_class_baseline(y_train, y_test)
        assert "accuracy" in result


class TestNaiveMomentumBaseline:
    def test_output_keys(self, prices):
        result = naive_momentum_baseline(prices)
        for key in ["accuracy", "sharpe", "lookback", "n_signals"]:
            assert key in result

    def test_default_lookback(self, prices):
        result = naive_momentum_baseline(prices)
        assert result["lookback"] == 20

    def test_custom_lookback(self, prices):
        result = naive_momentum_baseline(prices, lookback=50)
        assert result["lookback"] == 50


class TestRandomWalkBaseline:
    def test_output_keys(self, prices):
        result = random_walk_baseline(prices, n_simulations=50)
        for key in ["sharpe_mean", "sharpe_std", "sharpe_p95", "diracc_mean"]:
            assert key in result

    def test_reproducible(self, prices):
        r1 = random_walk_baseline(prices, n_simulations=50, seed=42)
        r2 = random_walk_baseline(prices, n_simulations=50, seed=42)
        assert r1["sharpe_mean"] == r2["sharpe_mean"]

    def test_diracc_near_50(self, prices):
        result = random_walk_baseline(prices, n_simulations=200)
        assert 0.45 < result["diracc_mean"] < 0.55


class TestBuyAndHoldBaseline:
    def test_output_keys(self, prices):
        result = buy_and_hold_baseline(prices)
        for key in ["total_return", "cagr", "sharpe", "max_drawdown", "volatility"]:
            assert key in result

    def test_positive_sharpe_for_upward(self):
        upward = pd.Series(np.linspace(100, 200, 252))
        result = buy_and_hold_baseline(upward)
        assert result["total_return"] > 0

    def test_max_drawdown_nonpositive(self, prices):
        result = buy_and_hold_baseline(prices)
        assert result["max_drawdown"] <= 0

    def test_empty_after_filter(self):
        prices = pd.Series([100.0])
        result = buy_and_hold_baseline(prices, test_start=100)
        assert result["n_days"] == 0
