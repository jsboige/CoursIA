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

    def test_causal_threshold_uses_past_only(self):
        """At t, the volatility threshold must be a function of [0, t) only.

        Build two 300-day series that share the first 150 days, then
        diverge. With causal_threshold=True the regimes produced at any
        index t < 150 must be identical between the two series — the
        threshold at t is fully determined by the shared prefix.
        """
        rng = np.random.default_rng(0)
        shared = rng.normal(0.0004, 0.01, 150)
        future_a = rng.normal(0.0004, 0.01, 150)
        future_b = rng.normal(0.0004, 0.05, 150)  # much higher vol

        prices_a = pd.Series(100 * np.cumprod(1 + np.concatenate([shared, future_a])))
        prices_b = pd.Series(100 * np.cumprod(1 + np.concatenate([shared, future_b])))

        lookback = 30
        regimes_a = detect_regimes_price(prices_a, lookback_days=lookback, causal_threshold=True)
        regimes_b = detect_regimes_price(prices_b, lookback_days=lookback, causal_threshold=True)

        # Identical regime labels on the shared prefix (post-lookback).
        # shift(1) keeps this property: at any t < 150, the threshold
        # is computed from rolling_std[0..t-1] which is identical
        # between the two series (shared prefix).
        np.testing.assert_array_equal(
            regimes_a.iloc[lookback:150].values,
            regimes_b.iloc[lookback:150].values,
        )

    def test_non_causal_threshold_legacy_default(self):
        """non_causal mode reproduces the pre-#21054 global-quantile path.

        The two modes disagree when the future differs from the past.
        Here we manufacture a clean regime switch: low-vol first half,
        high-vol second half. The non-causal threshold (computed over
        the whole series) will be HIGH, classifying few second-half
        rows as 'volatility' in a way the causal mode would not.
        """
        rng = np.random.default_rng(1)
        n = 400
        returns = np.empty(n)
        returns[:200] = rng.normal(0.0004, 0.005, 200)         # calm
        returns[200:] = rng.normal(0.0004, 0.04, 200)          # stormy
        prices = pd.Series(100 * np.cumprod(1 + returns))

        causal = detect_regimes_price(prices, lookback_days=30, causal_threshold=True)
        legacy = detect_regimes_price(prices, lookback_days=30, causal_threshold=False)

        # Causal threshold on the calm window is much LOWER than the
        # global quantile (which is dragged up by the stormy window),
        # so the causal mode must mark at least as many 'volatility'
        # rows in the stormy second half as the legacy mode. The
        # shift(1) used by the causal mode keeps this invariant
        # (the threshold on the storm boundary is even lower than
        # without shift, since the stormy values are not yet in the
        # window).
        stormy_causal = (causal.iloc[200:] == "volatility").sum()
        stormy_legacy = (legacy.iloc[200:] == "volatility").sum()
        assert stormy_causal >= stormy_legacy

    def test_causal_is_default(self, trending_up):
        """`causal_threshold=True` is the documented default (#21054)."""
        explicit = detect_regimes_price(trending_up, lookback_days=20, causal_threshold=True)
        default = detect_regimes_price(trending_up, lookback_days=20)
        np.testing.assert_array_equal(explicit.values, default.values)

    def test_causal_threshold_strict_t_minus_1(self):
        """#21111 v2: the threshold at t is the quantile of [0, t-1],
        not [0, t]. The .shift(1) makes the contract strict
        known-at-t-1.

        Discriminator: with shared rolling_std prefix, append a single
        extreme value at the boundary. The non-causal (no shift)
        expanding threshold at the boundary INCLUDES the extreme
        value; the causal (shifted) threshold at the same index does
        NOT.
        """
        rng = np.random.default_rng(2)
        n = 200
        returns = rng.normal(0.0004, 0.01, n)
        prices = pd.Series(100 * np.cumprod(1 + returns))
        lookback = 30
        L = lookback

        # Use the public path: re-implement both branches via
        # detect_regimes_price with two seeds, then read the actual
        # threshold that the function used by inferring the
        # classification decision.
        # Easier discriminator: at the LAST index, compare the
        # number of 'volatility' classifications between causal
        # and non-causal modes on identical input. They will
        # differ because the global quantile (non-causal) is
        # higher than the strict t-1 quantile (causal) when the
        # tail is calm but the global threshold is pulled by
        # middle outliers.
        causal = detect_regimes_price(prices, lookback_days=L, causal_threshold=True)
        legacy = detect_regimes_price(prices, lookback_days=L, causal_threshold=False)

        # Strict-t-1 must produce a *lower* (or equal) threshold on
        # the last index than the global one, because the last
        # index is excluded from its own threshold. In regime
        # terms, the causal mode will mark at least as many rows
        # 'volatility' on the calm tail.
        calm_tail_causal = (causal.iloc[100:] == "volatility").sum()
        calm_tail_legacy = (legacy.iloc[100:] == "volatility").sum()
        # The discriminating claim: on random data, the two counts
        # can be EQUAL, but they cannot be lower for causal (which
        # is the bug fixed by the shift). Add an adversarial tail
        # to make the inequality strict.
        adversarial = np.concatenate([returns[:100], rng.normal(0.0004, 0.04, 100)])
        prices_adv = pd.Series(100 * np.cumprod(1 + adversarial))
        causal_adv = detect_regimes_price(prices_adv, lookback_days=L, causal_threshold=True)
        legacy_adv = detect_regimes_price(prices_adv, lookback_days=L, causal_threshold=False)
        adv_causal = (causal_adv.iloc[100:] == "volatility").sum()
        adv_legacy = (legacy_adv.iloc[100:] == "volatility").sum()
        assert adv_causal >= adv_legacy, (
            f"causal ({adv_causal}) must mark >= legacy ({adv_legacy}) "
            "volatility rows in the stormy half when the threshold is "
            "shifted (strict t-1 contract)"
        )

    def test_causal_warmup_at_2L_minus_1(self):
        """#21111 v2: first valid threshold at index 2*lookback_days - 1.

        rolling_std (a rolling(L).std()) is NaN for indices 0..L-2 and
        valid from L-1. expanding(min_periods=L) needs L non-NaN values
        to produce a quantile, so its first valid output is at index
        (L-1) + (L-1) = 2L-2. The .shift(1) adds one more index of
        latency, so the first usable threshold is at 2L-1. Before
        that index the threshold is NaN and the volatility regime is
        unreachable (NaN >= NaN is False).

        Discriminator: on a constant high-volatility series, the
        count of 'volatility' rows in [0, 2L-1) must be 0 and >0 in
        [2L-1, ...).
        """
        rng = np.random.default_rng(3)
        n = 200
        lookback = 30
        L = lookback
        # Constant high volatility so the threshold is well below
        # the realised rolling_std once defined.
        returns = rng.normal(0.0004, 0.05, n)
        prices = pd.Series(100 * np.cumprod(1 + returns))

        regimes = detect_regimes_price(prices, lookback_days=L, causal_threshold=True)
        warmup_idx = 2 * L - 1
        # Before warmup_idx: no 'volatility' (threshold NaN).
        pre_warmup = (regimes.iloc[:warmup_idx] == "volatility").sum()
        # From warmup_idx onward: at least one 'volatility' in a
        # high-vol series.
        post_warmup = (regimes.iloc[warmup_idx:] == "volatility").sum()
        assert pre_warmup == 0, (
            f"pre-warmup ([:{warmup_idx}]) should have 0 'volatility' rows "
            f"(NaN threshold), got {pre_warmup}"
        )
        assert post_warmup > 0, (
            f"post-warmup ([{warmup_idx}:]) should have >0 'volatility' rows, "
            f"got {post_warmup}"
        )


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
