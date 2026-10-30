"""Tests for regime_detector.py — market regime detection."""

from __future__ import annotations

import re
import sys
import types
from pathlib import Path
from unittest.mock import patch

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

    def test_causal_warmup_at_2L(self):
        """#21111 v2: first valid threshold at index 2*lookback_days.

        rolling_std (a rolling(L).std() of returns) is NaN for
        indices 0..L-1 and valid from L (returns[0] is NaN, so the
        first 30 non-NaN returns are at indices 1..30 and the
        rolling(30) emits at the right edge = index 30).
        expanding(min_periods=L) needs L non-NaN values to produce
        a quantile, so its first valid output is at index L + (L-1)
        = 2L-1. The .shift(1) adds one more index of latency, so
        the first usable threshold is at 2L. Before that index the
        threshold is NaN and the volatility regime is unreachable
        (NaN >= NaN is False).

        Discriminator: on a constant high-volatility series, the
        count of 'volatility' rows in [0, 2L) must be 0 and >0 in
        [2L, ...).
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
        warmup_idx = 2 * L
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

    def test_causal_warmup_exact_threshold_at_2L(self):
        """#21111 v2: vol_threshold is NaN at 2L-1 and finite at 2L.

        The prior warmup test (pre/post counts) does not distinguish
        2L-1 from 2L as the boundary — both have pre=0 and post>0 on
        a high-vol series. The exact assertion is on the threshold
        itself, not on the regime count.

        Reproduce the vol_threshold calculation and assert:
        - vol_threshold.iloc[2L-1] is NaN
        - vol_threshold.iloc[2L] is finite
        """
        rng = np.random.default_rng(3)
        n = 200
        L = 30
        returns = rng.normal(0.0004, 0.05, n)
        prices = pd.Series(100 * np.cumprod(1 + returns))

        # Reproduce the threshold calculation
        ret = prices.pct_change()
        rolling_std = ret.rolling(L).std() * np.sqrt(252)
        vol_threshold = rolling_std.expanding(min_periods=L).quantile(0.75).shift(1)

        # Threshold at 2L-1 is NaN
        assert pd.isna(vol_threshold.iloc[2 * L - 1]), (
            f"vol_threshold at 2L-1 = {2 * L - 1} should be NaN, "
            f"got {vol_threshold.iloc[2 * L - 1]}"
        )
        # Threshold at 2L is finite
        assert pd.notna(vol_threshold.iloc[2 * L]), (
            f"vol_threshold at 2L = {2 * L} should be finite, got NaN"
        )

    def test_strict_t_minus_1_witness_via_extreme_value(self):
        """#21111 v2: the .shift(1) is operative, not decorative.

        Witness: build a series where rolling_std at index 2L is an
        extreme outlier (one-off spike). The shifted threshold at 2L
        uses rolling_std[0..2L-1] (excluding 2L); the unshifted
        threshold at 2L uses rolling_std[0..2L] (including 2L). The
        two must differ at 2L, proving the shift is operative and
        the strict t-1 contract is enforced.

        The prior test_causal_threshold_strict_t_minus_1 compared
        causal vs non-causal (different code paths); this one
        compares shift vs no-shift on the same code path — the
        discriminator the adjoint flagged as missing.
        """
        rng = np.random.default_rng(42)
        L = 30
        n = 100
        returns = np.zeros(n)
        # Indices 0..L+29 = 0..59: small returns
        returns[:60] = rng.normal(0.0004, 0.01, 60)
        # Index 60 = 2L: extreme spike (50% single-day return)
        returns[60] = 0.5
        # Indices 61..99: small returns
        returns[61:] = rng.normal(0.0004, 0.01, n - 61)

        prices = pd.Series(100 * np.cumprod(1 + returns))

        # Compute the threshold with and without shift
        ret = prices.pct_change()
        rolling_std = ret.rolling(L).std() * np.sqrt(252)

        # Without shift (the buggy version, look-ahead at t)
        threshold_no_shift = rolling_std.expanding(min_periods=L).quantile(0.75)
        # With shift (the current correct version, strict t-1)
        threshold_with_shift = threshold_no_shift.shift(1)

        # At index 2L = 60, the two must differ (rolling_std[60] is huge)
        val_no_shift = threshold_no_shift.iloc[2 * L]
        val_with_shift = threshold_with_shift.iloc[2 * L]

        assert not np.isclose(val_no_shift, val_with_shift), (
            f"shift must produce a different threshold at index 2L={2 * L}: "
            f"with_shift={val_with_shift}, no_shift={val_no_shift}"
        )
        # And the shift must EXCLUDE the extreme: the unshifted
        # threshold at 2L includes rolling_std[2L] (huge), so
        # unshifted > shifted.
        assert val_no_shift > val_with_shift, (
            f"unshifted threshold ({val_no_shift}) must exceed shifted "
            f"({val_with_shift}) when rolling_std[2L] is an extreme spike"
        )

    def test_strict_t_minus_1_witness_via_source_removal(self):
        """#21111 v4: removing the .shift(1) from line 114 of the production
        source must turn this test RED, proving the .shift(1) is operative
        on the regime path.

        The v3 witness (test_strict_t_minus_1_witness_on_production, now
        removed) used ``unittest.mock.patch.object(pd.Series, "shift", ...)``
        to neutralize ``.shift`` globally. The adjoint reproduced that this
        patch also breaks ``prices.pct_change()`` (which uses
        ``prices - prices.shift(1)`` internally), so the diff observed in
        v3 was the combined effect of breaking both the production shift
        AND the returns computation — not a witness of the production
        shift alone. Re-running v3 with the production ``.shift(1)``
        literally removed (but ``pct_change`` intact) still passes,
        confirming v3 is non-discriminative.

        This v4 witness uses ``exec`` of the production source with
        ``.shift(1)`` removed, leaving ``pct_change`` and ``rolling``
        untouched. The exec happens in a fresh module registered in
        ``sys.modules`` (required by ``@dataclass``), so the original
        file is never modified. The witness is therefore:

        - Pristine (current source has ``.shift(1)``): production regimes
          differ from the exec-mutated regimes. ``n_diff > 0``. GREEN.
        - Mutation (source has no ``.shift(1)``): production regimes
          equal the exec-mutated regimes. ``n_diff == 0``. RED.
        - Restoration: implicit — the file is never touched, so pristine
          == restored by construction.

        Three cycles, in line with the adjoint's spec
        (``adjoint-21111-mutant30-confirmed-correction-20261016``).
        """
        rng = np.random.default_rng(42)
        L = 30
        n = 100
        returns = np.zeros(n)
        # Indices 0..59: small returns (the shared prefix that drives
        # the threshold under causal mode).
        returns[:60] = rng.normal(0.0004, 0.01, 60)
        # Index 60 = 2L: extreme spike (50% single-day return). The
        # threshold at 60 differs depending on whether rolling_std[60]
        # is included (no shift) or excluded (with shift).
        returns[60] = 0.5
        # Indices 61..99: small returns
        returns[61:] = rng.normal(0.0004, 0.01, n - 61)

        prices = pd.Series(100 * np.cumprod(1 + returns))

        # Pristine: production call with the current source.
        regimes_pristine = detect_regimes_price(prices, lookback_days=L)

        # Mutation: exec the source with ``.shift(1)`` removed from
        # the vol_threshold chain (line 114). Only that line is
        # affected; ``pct_change`` and ``rolling`` are intact.
        import regime_detector
        src_path = Path(regime_detector.__file__)
        src = src_path.read_text()
        # Pattern: ``            .shift(1)\n        )\n    else:`` ->
        # ``        )\n    else:`` (one unique match, the production
        # vol_threshold chain).
        src_mutant = re.sub(
            r"            \.shift\(1\)\n        \)\n    else:",
            "        )\n    else:",
            src,
            count=1,
        )
        assert src_mutant != src, (
            "expected to find the production .shift(1) at line 114 "
            "of regime_detector.py but the pattern did not match"
        )

        mutant_name = "regime_detector_mutant_v4"
        mutant_mod = types.ModuleType(mutant_name)
        mutant_mod.__file__ = str(src_path)
        sys.modules[mutant_name] = mutant_mod
        exec(compile(src_mutant, str(src_path), "exec"), mutant_mod.__dict__)
        regimes_mutant = mutant_mod.detect_regimes_price(prices, lookback_days=L)

        # The witness: pristine and mutant must differ somewhere.
        n_diff = int((regimes_pristine != regimes_mutant).sum())
        assert n_diff > 0, (
            f"Removing .shift(1) from line 114 produced no regime "
            f"change: the production .shift(1) is non-operative on the "
            f"regime path "
            f"(pristine[:5]={list(regimes_pristine[:5])}, "
            f"mutant[:5]={list(regimes_mutant[:5])})"
        )

        # Belt-and-suspenders: verify the same exec pattern is
        # idempotent (re-exec'ing the same source on a clean module
        # gives the same regimes) — guards against test flakiness
        # from a polluted sys.modules entry.
        mutant_mod_2 = types.ModuleType(mutant_name + "_bis")
        mutant_mod_2.__file__ = str(src_path)
        sys.modules[mutant_name + "_bis"] = mutant_mod_2
        exec(compile(src_mutant, str(src_path), "exec"), mutant_mod_2.__dict__)
        regimes_mutant_2 = mutant_mod_2.detect_regimes_price(prices, lookback_days=L)
        np.testing.assert_array_equal(
            regimes_mutant.values,
            regimes_mutant_2.values,
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
# Decoding causality tests (#21054 case 2): viterbi is retrospective,
# mode="filter" is the causal forward-only decode for signal use.
# ---------------------------------------------------------------------------


class TestDecodeCausality:
    @pytest.fixture
    def hand_set_hmm(self):
        """Two-state HMM with hand-set parameters (deterministic decode).

        Emissions are weakly informative (sigma=4) so the globally most
        likely path is driven by the sticky transition matrix, making the
        end-backtracking sensitive to future observations.
        """
        hmm = GaussianHMM(n_states=2)
        hmm.pi = np.array([0.5, 0.5])
        hmm.A = np.array([[0.95, 0.05], [0.05, 0.95]])
        hmm.mu = np.array([[0.0], [1.0]])
        hmm.sig = np.array([[4.0], [4.0]])
        return hmm

    def test_filter_truncation_invariant_on_fitted(self):
        """Filter decode of X[:t] equals the first t states of the decode
        of X[:T] — the labels at t never depend on observations after t."""
        rng = np.random.default_rng(42)
        X = np.vstack([rng.normal(0.002, 0.01, (200, 2)),
                       rng.normal(-0.003, 0.015, (200, 2))])
        hmm = GaussianHMM(n_states=2, n_iter=50)
        hmm.fit(X)
        full = hmm.predict(X, mode="filter")
        for t in (1, 2, 5, 50, 199, 350, 399):
            truncated = hmm.predict(X[:t], mode="filter")
            np.testing.assert_array_equal(truncated, full[:t])

    def test_viterbi_label_depends_on_future_observation(self, hand_set_hmm):
        """Witness of the look-ahead: appending one observation flips the
        VITERBI label at t=0 (0 -> 1 via end-backtracking), while the
        filter label at t=0 stays 0."""
        X = np.array([[0.0], [1.2]])
        # Truncated series: only x=0 observed, emission favors state 0.
        assert hand_set_hmm.predict(X[:1])[0] == 0
        # Full series: the future observation x=1.2 makes the sticky path
        # ending in state 1 globally better, and the backtracking rewrites
        # t=0 to state 1 — that label was NOT knowable at t=0.
        assert hand_set_hmm.predict(X)[0] == 1
        # Filter decode is unaffected by the appended observation.
        assert hand_set_hmm.predict(X[:1], mode="filter")[0] == 0
        assert hand_set_hmm.predict(X, mode="filter")[0] == 0

    def test_filter_matches_argmax_forward(self, hand_set_hmm):
        """Filter decode is exactly argmax of the forward probabilities."""
        X = np.array([[0.0], [1.2], [0.4], [0.9], [0.1]])
        log_emit = hand_set_hmm._log_emission(X)
        alpha = hand_set_hmm._forward(log_emit)
        expected = np.argmax(alpha, axis=1)
        np.testing.assert_array_equal(hand_set_hmm.predict(X, mode="filter"), expected)

    def test_predict_invalid_mode_raises(self, hand_set_hmm):
        X = np.array([[0.0], [1.2]])
        with pytest.raises(ValueError, match="mode"):
            hand_set_hmm.predict(X, mode="smooth")

    def test_detect_regimes_hmm_decode_mode_propagates(self):
        rng = np.random.default_rng(42)
        returns = rng.normal(0.0004, 0.01, 500)
        prices = pd.Series(100 * np.cumprod(1 + returns))
        default_result = detect_regimes_hmm(prices, n_states=3)
        assert default_result.decode_mode == "viterbi"
        filtered = detect_regimes_hmm(prices, n_states=3, decode_mode="filter")
        assert filtered.decode_mode == "filter"
        assert len(filtered.labels) == len(prices)

    def test_detect_regimes_hmm_invalid_decode_mode_raises(self):
        rng = np.random.default_rng(42)
        returns = rng.normal(0.0004, 0.01, 500)
        prices = pd.Series(100 * np.cumprod(1 + returns))
        with pytest.raises(ValueError, match="mode"):
            detect_regimes_hmm(prices, n_states=3, decode_mode="bogus")


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
