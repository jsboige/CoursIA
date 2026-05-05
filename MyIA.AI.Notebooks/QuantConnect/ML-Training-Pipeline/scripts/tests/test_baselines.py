"""Tests for baselines.py — baseline models for financial ML evaluation."""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from scripts.baselines import (
    buy_and_hold_baseline,
    majority_class_baseline,
    naive_momentum_baseline,
    oos_direction_distribution,
    random_walk_baseline,
    _sharpe_from_returns,
)


class TestMajorityClassBaseline:
    def test_balanced_classes(self):
        y_train = np.array([0, 1, 0, 1, 0, 1])
        y_test = np.array([0, 1, 0, 1])
        result = majority_class_baseline(y_train, y_test)
        assert result["accuracy"] == 0.5
        assert result["n_train"] == 6
        assert result["n_test"] == 4

    def test_imbalanced_majority_up(self):
        y_train = np.array([1, 1, 1, 1, 0, 0])
        y_test = np.array([1, 0, 1, 1])
        result = majority_class_baseline(y_train, y_test)
        assert result["majority_class"] == 1
        assert result["majority_freq"] == pytest.approx(4 / 6)
        assert result["accuracy"] == 0.75  # 3/4 correct

    def test_imbalanced_majority_down(self):
        y_train = np.array([0, 0, 0, 1, 1])
        y_test = np.array([0, 0, 1])
        result = majority_class_baseline(y_train, y_test)
        assert result["majority_class"] == 0
        assert result["accuracy"] == pytest.approx(2 / 3)

    def test_all_same_class(self):
        y_train = np.ones(100)
        y_test = np.ones(20)
        result = majority_class_baseline(y_train, y_test)
        assert result["accuracy"] == 1.0
        assert result["majority_freq"] == 1.0

    def test_spy_like_frequency(self):
        """SPY up-day frequency ~54% is a realistic check."""
        rng = np.random.default_rng(42)
        y_train = rng.choice([0, 1], size=1000, p=[0.46, 0.54])
        result = majority_class_baseline(y_train, y_train)
        assert 0.50 <= result["majority_freq"] <= 0.60


class TestNaiveMomentumBaseline:
    @pytest.fixture
    def trending_prices(self):
        """Monotonically increasing prices."""
        return pd.Series(np.arange(100, 200, dtype=float))

    @pytest.fixture
    def mean_revert_prices(self):
        """Oscillating prices around 100."""
        t = np.arange(200)
        return pd.Series(100 + 5 * np.sin(t * 2 * np.pi / 20))

    def test_high_accuracy_trending(self, trending_prices):
        result = naive_momentum_baseline(trending_prices, lookback=10)
        assert result["accuracy"] > 0.8

    def test_returns_lookback(self, trending_prices):
        result = naive_momentum_baseline(trending_prices, lookback=5)
        assert result["lookback"] == 5

    def test_sharpe_positive_trending(self, trending_prices):
        result = naive_momentum_baseline(trending_prices, lookback=10)
        assert result["sharpe"] > 0

    def test_oscillating_lower_accuracy(self, mean_revert_prices):
        result = naive_momentum_baseline(mean_revert_prices, lookback=20)
        # MA crossover on mean-reverting data should be near 50%
        assert 0.3 <= result["accuracy"] <= 0.7

    def test_test_start_parameter(self, trending_prices):
        result = naive_momentum_baseline(trending_prices, lookback=10, test_start=50)
        assert result["start"] == 50


class TestRandomWalkBaseline:
    @pytest.fixture
    def spy_like_prices(self):
        """Simulate SPY-like price series."""
        rng = np.random.default_rng(42)
        returns = rng.normal(0.0004, 0.01, size=500)
        prices = 100 * np.cumprod(1 + returns)
        return pd.Series(prices)

    def test_sharpe_centered_near_zero(self, spy_like_prices):
        result = random_walk_baseline(spy_like_prices, n_simulations=500, seed=42)
        assert abs(result["sharpe_mean"]) < 1.0

    def test_diracc_near_50_percent(self, spy_like_prices):
        result = random_walk_baseline(spy_like_prices, n_simulations=500, seed=42)
        assert abs(result["diracc_mean"] - 0.5) < 0.05

    def test_reproducible_with_seed(self, spy_like_prices):
        r1 = random_walk_baseline(spy_like_prices, seed=123)
        r2 = random_walk_baseline(spy_like_prices, seed=123)
        assert r1["sharpe_mean"] == r2["sharpe_mean"]

    def test_different_seeds_different_results(self, spy_like_prices):
        r1 = random_walk_baseline(spy_like_prices, seed=1)
        r2 = random_walk_baseline(spy_like_prices, seed=2)
        assert r1["sharpe_mean"] != r2["sharpe_mean"]

    def test_p95_greater_than_mean(self, spy_like_prices):
        result = random_walk_baseline(spy_like_prices, n_simulations=500, seed=42)
        assert result["sharpe_p95"] > result["sharpe_mean"]

    def test_n_simulations(self, spy_like_prices):
        result = random_walk_baseline(spy_like_prices, n_simulations=50)
        assert result["n_simulations"] == 50


class TestBuyAndHoldBaseline:
    @pytest.fixture
    def spy_like_prices(self):
        rng = np.random.default_rng(42)
        returns = rng.normal(0.0004, 0.01, size=500)
        return pd.Series(100 * np.cumprod(1 + returns))

    def test_positive_total_return(self, spy_like_prices):
        result = buy_and_hold_baseline(spy_like_prices)
        assert result["total_return"] > 0

    def test_positive_cagr(self, spy_like_prices):
        result = buy_and_hold_baseline(spy_like_prices)
        assert result["cagr"] > 0

    def test_positive_sharpe(self, spy_like_prices):
        result = buy_and_hold_baseline(spy_like_prices)
        assert result["sharpe"] > 0

    def test_max_drawdown_negative(self, spy_like_prices):
        result = buy_and_hold_baseline(spy_like_prices)
        assert result["max_drawdown"] < 0

    def test_volatility_positive(self, spy_like_prices):
        result = buy_and_hold_baseline(spy_like_prices)
        assert result["volatility"] > 0

    def test_n_days_matches(self, spy_like_prices):
        result = buy_and_hold_baseline(spy_like_prices)
        assert result["n_days"] == 499  # n-1 returns

    def test_declining_prices(self):
        prices = pd.Series(np.linspace(100, 50, 100))
        result = buy_and_hold_baseline(prices)
        assert result["total_return"] < 0
        assert result["cagr"] < 0

    def test_flat_prices(self):
        prices = pd.Series(np.full(100, 100.0))
        result = buy_and_hold_baseline(prices)
        assert result["total_return"] == pytest.approx(0.0)
        assert result["sharpe"] == pytest.approx(0.0)

    def test_test_start(self, spy_like_prices):
        full = buy_and_hold_baseline(spy_like_prices)
        half = buy_and_hold_baseline(spy_like_prices, test_start=250)
        assert half["n_days"] < full["n_days"]


class TestSharpeFromReturns:
    def test_zero_returns(self):
        assert _sharpe_from_returns(pd.Series([])) == 0.0

    def test_constant_returns(self):
        assert _sharpe_from_returns(pd.Series([0.01] * 100)) == 0.0

    def test_positive_mean(self):
        rng = np.random.default_rng(42)
        returns = pd.Series(rng.normal(0.001, 0.01, 252))
        sharpe = _sharpe_from_returns(returns)
        assert sharpe > 0

    def test_negative_mean(self):
        rng = np.random.default_rng(99)
        returns = pd.Series(rng.normal(-0.005, 0.01, 252))
        sharpe = _sharpe_from_returns(returns)
        assert sharpe < 0

    def test_no_annualize(self):
        rng = np.random.default_rng(42)
        r = pd.Series(rng.normal(0.001, 0.01, 252))
        s_ann = _sharpe_from_returns(r, annualize=True)
        s_raw = _sharpe_from_returns(r, annualize=False)
        assert abs(s_ann) > abs(s_raw)


class TestOOSDirectionDistribution:
    def test_balanced_returns(self):
        y = np.array([1.0, -1.0] * 50)
        result = oos_direction_distribution(y)
        assert result["pct_up"] == pytest.approx(0.5)
        assert result["pct_down"] == pytest.approx(0.5)
        assert result["majority_class_accuracy"] == pytest.approx(0.5)

    def test_all_positive(self):
        y = np.ones(100)
        result = oos_direction_distribution(y)
        assert result["pct_up"] == 1.0
        assert result["pct_down"] == 0.0
        assert result["majority_class_accuracy"] == 1.0

    def test_all_negative(self):
        y = -np.ones(100)
        result = oos_direction_distribution(y)
        assert result["pct_up"] == 0.0
        assert result["majority_class_accuracy"] == 1.0

    def test_zeros_counted_as_down(self):
        y = np.zeros(10)
        result = oos_direction_distribution(y)
        assert result["pct_up"] == 0.0
        assert result["majority_class_accuracy"] == 1.0

    def test_multidimensional_flattened(self):
        y = np.array([[1.0, -1.0], [1.0, -1.0]])
        result = oos_direction_distribution(y)
        assert result["pct_up"] == pytest.approx(0.5)

    def test_rounded_output(self):
        y = np.array([1.0, -1.0, 1.0])
        result = oos_direction_distribution(y)
        assert result["pct_up"] == pytest.approx(2 / 3, abs=0.0001)
        assert isinstance(result["pct_up"], float)
