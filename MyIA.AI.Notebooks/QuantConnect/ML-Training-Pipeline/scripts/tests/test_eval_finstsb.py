"""Tests for eval_finstsb.py — FinTSB-style regime evaluation."""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from eval_finstsb import (
    detect_regimes,
    eval_per_regime,
    validate_no_regime_failure,
)
from baselines import sharpe_from_returns


class TestDetectRegimes:
    """Market regime detection tests."""

    @pytest.fixture
    def trending_up_prices(self):
        """Monotonically increasing prices → should detect uptrend."""
        return pd.Series(np.linspace(100, 200, 252))

    @pytest.fixture
    def trending_down_prices(self):
        """Monotonically decreasing prices → should detect downtrend."""
        return pd.Series(np.linspace(200, 100, 252))

    @pytest.fixture
    def spy_2018_prices(self):
        """SPY-like prices with 2018 Q4 selloff pattern.

        Jan-Oct uptrend, Oct-Dec ~20% drawdown then recovery.
        """
        rng = np.random.default_rng(42)
        # 200 days uptrend, 50 days selloff, 50 days recovery
        n = 300
        returns = rng.normal(0.0005, 0.005, n)
        # Inject selloff at day 200
        returns[200:220] = -0.02
        returns[220:250] = 0.005  # recovery
        return pd.Series(100 * np.cumprod(1 + returns))

    @pytest.fixture
    def covid_crash_prices(self):
        """Prices with a sudden ~30% crash (march 2020-like)."""
        rng = np.random.default_rng(42)
        n = 200
        returns = rng.normal(0.0003, 0.008, n)
        # Sudden crash over 15 days
        returns[100:115] = -0.025
        returns[115:130] = 0.015  # bounce
        return pd.Series(100 * np.cumprod(1 + returns))

    def test_uptrend_detected(self, trending_up_prices):
        regimes = detect_regimes(trending_up_prices, lookback_days=20)
        assert "uptrend" in regimes.values

    def test_downtrend_detected(self, trending_down_prices):
        regimes = detect_regimes(trending_down_prices, lookback_days=20)
        assert "downtrend" in regimes.values

    def test_no_normal_remaining(self, trending_up_prices):
        """All observations should be classified into a regime (not 'normal')."""
        regimes = detect_regimes(trending_up_prices, lookback_days=20)
        # Only the first lookback_days can be 'normal' (NaN fill)
        non_initial = regimes.iloc[20:]
        assert "normal" not in non_initial.values

    def test_black_swan_in_crash(self, covid_crash_prices):
        """A -30% drawdown should trigger black_swan regime."""
        regimes = detect_regimes(
            covid_crash_prices,
            lookback_days=20,
            black_swan_drawdown=-0.20,
            black_swan_window=30,
        )
        assert "black_swan" in regimes.values

    def test_returns_series_same_length(self, trending_up_prices):
        regimes = detect_regimes(trending_up_prices)
        assert len(regimes) == len(trending_up_prices)

    def test_lookback_fill(self, trending_up_prices):
        """First lookback_days observations should be 'normal' (NaN fill)."""
        lookback = 30
        regimes = detect_regimes(trending_up_prices, lookback_days=lookback)
        assert (regimes.iloc[:lookback] == "normal").all()

    def test_known_regimes_count(self):
        """At least 3 different regimes in a varied price series."""
        rng = np.random.default_rng(42)
        n = 500
        returns = rng.normal(0.0003, 0.015, n)
        # Inject crash
        returns[300:315] = -0.03
        prices = pd.Series(100 * np.cumprod(1 + returns))
        regimes = detect_regimes(prices, lookback_days=30)
        unique = set(regimes.iloc[30:].values)  # skip initial fill
        assert len(unique) >= 3

    def test_custom_thresholds(self, trending_up_prices):
        """Very high threshold should classify less as uptrend."""
        low_thresh = detect_regimes(trending_up_prices, uptrend_threshold=0.01, lookback_days=20)
        high_thresh = detect_regimes(trending_up_prices, uptrend_threshold=0.50, lookback_days=20)
        n_up_low = (low_thresh == "uptrend").sum()
        n_up_high = (high_thresh == "uptrend").sum()
        assert n_up_low >= n_up_high


class TestEvalPerRegime:
    """Per-regime evaluation tests."""

    @pytest.fixture
    def perfect_model(self):
        """Model that always predicts correctly."""

        class Perfect:
            def predict(self, X):
                return np.array([1 if x[0] > 0 else 0 for x in X])

        return Perfect()

    @pytest.fixture
    def random_model(self):
        """Model that predicts randomly."""

        class Random:
            def __init__(self):
                self.rng = np.random.default_rng(42)

            def predict(self, X):
                return self.rng.choice([0, 1], size=len(X))

        return Random()

    @pytest.fixture
    def sample_data(self):
        """Generate sample features, labels, and prices."""
        rng = np.random.default_rng(42)
        n = 300
        prices = pd.Series(100 * np.cumprod(1 + rng.normal(0.0003, 0.01, n)))
        returns = prices.pct_change().fillna(0).values
        y = (returns > 0).astype(int)
        X = rng.normal(0, 1, (n, 5))
        # Make features predictive: X[:, 0] correlates with returns
        X[:, 0] = returns + rng.normal(0, 0.1, n)
        return X, y, prices

    def test_perfect_model_high_diracc(self, perfect_model, sample_data):
        X, y, prices = sample_data
        results = eval_per_regime(perfect_model, X, y, prices)
        # At least one regime should have high accuracy
        max_acc = max(
            results[r]["diracc"]
            for r in ["uptrend", "downtrend", "volatility", "black_swan"]
            if not np.isnan(results[r].get("diracc", float("nan")))
        )
        assert max_acc > 0.5

    def test_weighted_avg_present(self, random_model, sample_data):
        X, y, prices = sample_data
        results = eval_per_regime(random_model, X, y, prices)
        assert "weighted_avg" in results
        assert "diracc" in results["weighted_avg"]
        assert "sharpe" in results["weighted_avg"]

    def test_all_regimes_present(self, random_model, sample_data):
        X, y, prices = sample_data
        results = eval_per_regime(random_model, X, y, prices)
        for regime in ["uptrend", "downtrend", "volatility", "black_swan"]:
            assert regime in results
            assert "diracc" in results[regime]
            assert "sharpe" in results[regime]
            assert "n_samples" in results[regime]

    def test_n_samples_sum(self, random_model, sample_data):
        X, y, prices = sample_data
        results = eval_per_regime(random_model, X, y, prices)
        total = sum(
            results[r]["n_samples"]
            for r in ["uptrend", "downtrend", "volatility", "black_swan"]
        )
        assert total == results["weighted_avg"]["n_samples"]

    def test_custom_regimes(self, random_model, sample_data):
        """Passing pre-computed regimes should work."""
        X, y, prices = sample_data
        n = len(X)
        regimes = detect_regimes(prices)
        results = eval_per_regime(random_model, X, y, prices, regimes=regimes)
        assert "weighted_avg" in results

    def test_few_samples_nan(self, random_model):
        """With very few samples in a regime, metrics should be NaN."""
        X = np.random.randn(10, 3)
        y = np.array([0, 1, 0, 1, 0, 1, 0, 1, 0, 1])
        prices = pd.Series(np.linspace(100, 101, 10))
        # Small lookback to get some regime labels
        regimes = detect_regimes(prices, lookback_days=3)
        # Override to force tiny regime
        regimes.iloc[:3] = "black_swan"
        results = eval_per_regime(random_model, X, y, prices, regimes=regimes)
        # black_swan has < 5 samples → NaN
        if results["black_swan"]["n_samples"] < 5:
            assert np.isnan(results["black_swan"]["diracc"])


class TestValidateNoRegimeFailure:
    """Regime failure validation tests."""

    def test_all_pass(self):
        results = {
            "uptrend": {"sharpe": 1.5, "n_samples": 100},
            "downtrend": {"sharpe": 0.5, "n_samples": 80},
            "volatility": {"sharpe": 0.2, "n_samples": 50},
            "black_swan": {"sharpe": 0.1, "n_samples": 10},
        }
        passed, failures = validate_no_regime_failure(results, min_sharpe=0.0)
        assert passed is True
        assert len(failures) == 0

    def test_one_regime_fails(self):
        results = {
            "uptrend": {"sharpe": 1.5, "n_samples": 100},
            "downtrend": {"sharpe": -0.5, "n_samples": 80},
            "volatility": {"sharpe": 0.2, "n_samples": 50},
            "black_swan": {"sharpe": 0.1, "n_samples": 10},
        }
        passed, failures = validate_no_regime_failure(results, min_sharpe=0.0)
        assert passed is False
        assert any("downtrend" in f for f in failures)

    def test_nan_sharpe_fails(self):
        results = {
            "uptrend": {"sharpe": 1.5, "n_samples": 100},
            "downtrend": {"sharpe": float("nan"), "n_samples": 80},
        }
        passed, failures = validate_no_regime_failure(results, min_sharpe=0.0)
        assert passed is False

    def test_few_samples_skipped(self):
        """Regimes with < 5 samples are skipped."""
        results = {
            "uptrend": {"sharpe": 1.5, "n_samples": 100},
            "black_swan": {"sharpe": -5.0, "n_samples": 3},
        }
        passed, failures = validate_no_regime_failure(results, min_sharpe=0.0)
        assert passed is True  # black_swan skipped due to n_samples < 5

    def test_custom_min_sharpe(self):
        results = {
            "uptrend": {"sharpe": 1.5, "n_samples": 100},
            "downtrend": {"sharpe": 0.3, "n_samples": 80},
        }
        passed, failures = validate_no_regime_failure(results, min_sharpe=0.5)
        assert passed is False
        assert any("downtrend" in f for f in failures)

    def test_missing_regime_ok(self):
        """Missing regime key is simply ignored."""
        results = {
            "uptrend": {"sharpe": 1.0, "n_samples": 100},
        }
        passed, failures = validate_no_regime_failure(results, min_sharpe=0.0)
        assert passed is True


class TestSharpe:
    """Internal Sharpe ratio helper tests."""

    def test_empty_returns(self):
        assert sharpe_from_returns(np.array([])) == 0.0

    def test_zero_std(self):
        assert sharpe_from_returns(np.array([0.01] * 100)) == 0.0

    def test_positive_sharpe(self):
        rng = np.random.default_rng(42)
        returns = rng.normal(0.001, 0.01, 252)
        assert sharpe_from_returns(returns) > 0

    def test_negative_sharpe(self):
        rng = np.random.default_rng(99)
        returns = rng.normal(-0.005, 0.01, 252)
        assert sharpe_from_returns(returns) < 0

    def test_no_annualize(self):
        rng = np.random.default_rng(42)
        r = rng.normal(0.001, 0.01, 252)
        s_ann = sharpe_from_returns(r, annualize=True)
        s_raw = sharpe_from_returns(r, annualize=False)
        assert abs(s_ann) > abs(s_raw)
