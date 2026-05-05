"""Tests for regime_detector.py — market regime detection."""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from regime_detector import (
    GaussianHMM,
    HMMRegimeResult,
    detect_regimes,
    detect_regimes_hmm,
    detect_regimes_price,
)


# ---------------------------------------------------------------------------
# Price-based regime detection tests
# ---------------------------------------------------------------------------


class TestDetectRegimesPrice:
    @pytest.fixture
    def trending_up(self):
        return pd.Series(np.linspace(100, 200, 252))

    @pytest.fixture
    def trending_down(self):
        return pd.Series(np.linspace(200, 100, 252))

    @pytest.fixture
    def crash_prices(self):
        rng = np.random.default_rng(42)
        n = 200
        returns = rng.normal(0.0003, 0.008, n)
        returns[100:115] = -0.025
        returns[115:130] = 0.015
        return pd.Series(100 * np.cumprod(1 + returns))

    def test_uptrend_detected(self, trending_up):
        regimes = detect_regimes_price(trending_up, lookback_days=20)
        assert "uptrend" in regimes.values

    def test_downtrend_detected(self, trending_down):
        regimes = detect_regimes_price(trending_down, lookback_days=20)
        assert "downtrend" in regimes.values

    def test_output_length_matches_input(self, trending_up):
        regimes = detect_regimes_price(trending_up)
        assert len(regimes) == len(trending_up)

    def test_no_normal_after_lookback(self, trending_up):
        regimes = detect_regimes_price(trending_up, lookback_days=20)
        after_lookback = regimes.iloc[20:]
        assert "normal" not in after_lookback.values

    def test_black_swan_in_crash(self, crash_prices):
        regimes = detect_regimes_price(
            crash_prices,
            lookback_days=20,
            black_swan_drawdown=-0.20,
            black_swan_window=30,
        )
        assert "black_swan" in regimes.values

    def test_known_regimes_count(self):
        rng = np.random.default_rng(42)
        returns = rng.normal(0.0003, 0.015, 500)
        returns[300:315] = -0.03
        prices = pd.Series(100 * np.cumprod(1 + returns))
        regimes = detect_regimes_price(prices, lookback_days=30)
        unique = set(regimes.iloc[30:].values)
        assert len(unique) >= 3

    def test_custom_thresholds(self, trending_up):
        low = detect_regimes_price(trending_up, uptrend_threshold=0.01, lookback_days=20)
        high = detect_regimes_price(trending_up, uptrend_threshold=0.50, lookback_days=20)
        assert (low == "uptrend").sum() >= (high == "uptrend").sum()


# ---------------------------------------------------------------------------
# Gaussian HMM tests
# ---------------------------------------------------------------------------


class TestGaussianHMM:
    @pytest.fixture
    def bull_bear_data(self):
        """Two-regime data: bull (positive mean) and bear (negative mean)."""
        rng = np.random.default_rng(42)
        n_bull = 200
        n_bear = 200
        bull = rng.normal(0.002, 0.01, (n_bull, 2))
        bear = rng.normal(-0.003, 0.015, (n_bear, 2))
        return np.vstack([bull, bear])

    def test_fit_converges(self, bull_bear_data):
        hmm = GaussianHMM(n_states=2, n_iter=50)
        hmm.fit(bull_bear_data)
        assert hasattr(hmm, "log_likelihood_")
        assert np.isfinite(hmm.log_likelihood_)

    def test_predict_shape(self, bull_bear_data):
        hmm = GaussianHMM(n_states=2, n_iter=50)
        hmm.fit(bull_bear_data)
        labels = hmm.predict(bull_bear_data)
        assert labels.shape == (len(bull_bear_data),)
        assert set(labels) <= {0, 1}

    def test_two_states_found(self, bull_bear_data):
        hmm = GaussianHMM(n_states=2, n_iter=50)
        hmm.fit(bull_bear_data)
        labels = hmm.predict(bull_bear_data)
        assert len(np.unique(labels)) == 2

    def test_transition_matrix_shape(self, bull_bear_data):
        hmm = GaussianHMM(n_states=3, n_iter=30)
        hmm.fit(bull_bear_data)
        assert hmm.A.shape == (3, 3)
        # Rows should sum to 1
        np.testing.assert_allclose(hmm.A.sum(axis=1), 1.0, atol=1e-6)

    def test_reproducible_with_same_data(self, bull_bear_data):
        hmm1 = GaussianHMM(n_states=2, n_iter=30)
        hmm1.fit(bull_bear_data)
        labels1 = hmm1.predict(bull_bear_data)

        hmm2 = GaussianHMM(n_states=2, n_iter=30)
        hmm2.fit(bull_bear_data)
        labels2 = hmm2.predict(bull_bear_data)
        np.testing.assert_array_equal(labels1, labels2)


# ---------------------------------------------------------------------------
# HMM regime detection (full pipeline) tests
# ---------------------------------------------------------------------------


class TestDetectRegimesHMM:
    @pytest.fixture
    def spy_like_prices(self):
        rng = np.random.default_rng(42)
        returns = rng.normal(0.0004, 0.01, 500)
        return pd.Series(100 * np.cumprod(1 + returns))

    def test_returns_hmm_result(self, spy_like_prices):
        result = detect_regimes_hmm(spy_like_prices, n_states=3)
        assert isinstance(result, HMMRegimeResult)
        assert result.n_states == 3

    def test_labels_match_prices_length(self, spy_like_prices):
        result = detect_regimes_hmm(spy_like_prices, n_states=3)
        assert len(result.labels) == len(spy_like_prices)

    def test_regime_names_populated(self, spy_like_prices):
        result = detect_regimes_hmm(spy_like_prices, n_states=3)
        assert "bull" in result.regime_names
        assert "bear" in result.regime_names
        assert "neutral" in result.regime_names

    def test_two_state_names(self, spy_like_prices):
        result = detect_regimes_hmm(spy_like_prices, n_states=2)
        assert "bull" in result.regime_names
        assert "bear" in result.regime_names

    def test_transition_matrix_square(self, spy_like_prices):
        result = detect_regimes_hmm(spy_like_prices, n_states=3)
        assert result.transition_matrix.shape == (3, 3)

    def test_insufficient_data(self):
        prices = pd.Series([100, 101, 102])
        result = detect_regimes_hmm(prices, n_states=3, min_samples=80)
        assert all(name == "unknown" for name in result.regime_names)

    def test_log_likelihood_finite(self, spy_like_prices):
        result = detect_regimes_hmm(spy_like_prices, n_states=3)
        assert np.isfinite(result.log_likelihood)


# ---------------------------------------------------------------------------
# Unified detect_regimes() convenience function tests
# ---------------------------------------------------------------------------


class TestDetectRegimes:
    @pytest.fixture
    def prices(self):
        rng = np.random.default_rng(42)
        returns = rng.normal(0.0004, 0.01, 300)
        return pd.Series(100 * np.cumprod(1 + returns))

    def test_price_method(self, prices):
        regimes = detect_regimes(prices, method="price")
        assert isinstance(regimes, pd.Series)
        assert len(regimes) == len(prices)

    def test_hmm_method(self, prices):
        regimes = detect_regimes(prices, method="hmm", n_states=3)
        assert isinstance(regimes, pd.Series)
        assert len(regimes) == len(prices)

    def test_invalid_method_raises(self, prices):
        with pytest.raises(ValueError, match="Unknown method"):
            detect_regimes(prices, method="invalid")
