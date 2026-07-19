"""Unit tests for s3_hmm_regime — HMM regime-detection KEEPER.

S3 (Markov-regime-switching detection with VIX exogenous regressor) is a
Curriculum-V3 KEEPER (per #1409: S3 HMM regime, delta +0.669 over 4/4 seeds —
the strongest single KEEPER) and a production-candidate, yet had ZERO dedicated
tests. The existing test_regime_detector.py covers a *different* module
(regime_detector.py, the pedagogical GaussianHMM `detect_regimes`), not this
statsmodels MarkovRegression-based KEEPER.

This suite covers the pure helpers that carry the regime pipeline logic:

- ``resample_weekly``: daily -> weekly OHLC-style resampling
- ``block_bootstrap``: stationary block bootstrap resampling
- ``_jitter_regime_boundaries``: regime-switch timing perturbation
- ``_sharpe`` / ``_max_drawdown``: performance statistics
- ``_regime_durations``: mean/median duration per regime

The statsmodels-dependent functions (``fit_markov_regime``, ``walk_forward_regime``)
import lazily inside the body, so importing ``s3_hmm_regime`` is side-effect
free. All fixtures are deterministic synthetic arrays — no network, no GPU, no
data files, no statsmodels fit. Runs in well under a second on CPU.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

SCRIPT_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from s3_hmm_regime import (  # noqa: E402
    _jitter_regime_boundaries,
    _max_drawdown,
    _regime_durations,
    _sharpe,
    block_bootstrap,
    resample_weekly,
)


def _daily_panel(n: int = 120) -> pd.DataFrame:
    """A small synthetic daily panel mimicking the load_data() schema."""
    idx = pd.date_range("2020-01-01", periods=n, freq="D", name="Date")
    rng = np.random.default_rng(0)
    spy = 100 * np.exp(np.cumsum(rng.standard_normal(n) * 0.01))
    tlt = 100 * np.exp(np.cumsum(rng.standard_normal(n) * 0.005))
    vix = np.abs(rng.standard_normal(n)) * 5 + 15
    df = pd.DataFrame(
        {"spy_close": spy, "tlt_close": tlt, "vix_close": vix}, index=idx
    )
    df["spy_ret"] = df["spy_close"].pct_change()
    df["tlt_ret"] = df["tlt_close"].pct_change()
    df["vix_level"] = df["vix_close"]
    return df.dropna()


# ── resample_weekly ─────────────────────────────────────────────────────────

class TestResampleWeekly:
    def test_returns_weekly_indexed_dataframe(self) -> None:
        out = resample_weekly(_daily_panel(120))
        # Weekly resample ("W", W-SUN) must yield a DatetimeIndex with week-end
        # labels. The last bucket may land on the Sunday after the daily range
        # ends, so bound generously (~ 120 days from 2020-01-01 => mid-May).
        assert isinstance(out.index, pd.DatetimeIndex)
        assert (out.index <= pd.Timestamp("2020-05-15")).all()
        assert len(out) <= 120 // 5  # generous upper bound

    def test_columns_preserved_and_computed(self) -> None:
        out = resample_weekly(_daily_panel(120))
        for col in ("spy_close", "tlt_close", "vix_close", "spy_ret", "tlt_ret", "vix_level"):
            assert col in out.columns
        assert out.notna().all().all()  # final .dropna() in the function

    def test_weekly_return_matches_last_pct_change(self) -> None:
        # spy_ret at week t (for t>=1) = pct_change of spy_close week t vs t-1.
        # The first weekly row carries a spy_ret computed from the last daily bar
        # of the *prior* (pre-panel) window — resample_weekly keeps it but it is
        # NOT a weekly pct_change, so compare from row 1 onward only.
        df = _daily_panel(120)
        out = resample_weekly(df)
        if len(out) >= 2:
            expected = out["spy_close"].pct_change().iloc[1:]
            got = out["spy_ret"].iloc[1:]
            np.testing.assert_allclose(
                got.values, expected.values, rtol=1e-9, atol=1e-15,
                err_msg="weekly spy_ret (t>=1) must equal pct_change of weekly spy_close",
            )


# ── block_bootstrap ─────────────────────────────────────────────────────────

class TestBlockBootstrap:
    def test_preserves_length(self) -> None:
        data = np.arange(60, dtype=float)
        out = block_bootstrap(data, block_size=5, seed=1)
        assert out.shape == (60,)

    def test_deterministic_with_seed(self) -> None:
        data = np.arange(100, dtype=float)
        a = block_bootstrap(data, block_size=7, seed=42)
        b = block_bootstrap(data, block_size=7, seed=42)
        np.testing.assert_array_equal(a, b)

    def test_samples_from_input(self) -> None:
        data = np.array([10.0, 20.0, 30.0, 40.0, 50.0])
        out = block_bootstrap(data, block_size=2, seed=3)
        assert np.isin(out, data).all()

    def test_different_seeds_differ(self) -> None:
        data = np.arange(90, dtype=float)
        a = block_bootstrap(data, block_size=6, seed=1)
        b = block_bootstrap(data, block_size=6, seed=2)
        assert not np.array_equal(a, b)


# ── _jitter_regime_boundaries ───────────────────────────────────────────────

class TestJitterRegimeBoundaries:
    def test_seed_zero_is_identity(self) -> None:
        labels = np.array([0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0])
        out = _jitter_regime_boundaries(labels, seed=0, max_jitter=5)
        np.testing.assert_array_equal(out, labels)

    def test_preserves_length_and_label_set(self) -> None:
        labels = np.array([0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0])
        out = _jitter_regime_boundaries(labels, seed=7, max_jitter=3)
        assert out.shape == labels.shape
        assert set(np.unique(out)).issubset({0, 1})

    def test_no_switches_returns_copy(self) -> None:
        # A constant-regime series has no switch points -> jitter is a no-op
        # regardless of seed.
        labels = np.zeros(20, dtype=int)
        out = _jitter_regime_boundaries(labels, seed=5, max_jitter=4)
        np.testing.assert_array_equal(out, labels)

    def test_total_regime_count_is_invariant_under_jitter(self) -> None:
        # Jitter shifts *boundaries*, it must not change how many bars sit in
        # each regime class (it only moves them around), so the per-class totals
        # are invariant. This is the core "robustness to boundary timing" claim.
        labels = np.array([0] * 30 + [1] * 30 + [0] * 30)
        base = _jitter_regime_boundaries(labels, seed=0, max_jitter=5)
        jittered = _jitter_regime_boundaries(labels, seed=3, max_jitter=5)
        # With 3 contiguous blocks the jitter propagates only at the 2 boundary
        # regions; total 0-count and 1-count are preserved.
        assert (jittered == 0).sum() == (base == 0).sum()
        assert (jittered == 1).sum() == (base == 1).sum()


# ── _sharpe / _max_drawdown ─────────────────────────────────────────────────

class TestStatistics:
    def test_sharpe_too_short_returns_zero(self) -> None:
        assert _sharpe(np.array([0.01])) == 0.0

    def test_sharpe_zero_sigma_returns_zero(self) -> None:
        assert _sharpe(np.full(20, 0.001)) == 0.0

    def test_sharpe_known_value(self) -> None:
        rng = np.random.default_rng(0)
        r = rng.standard_normal(252) * 0.01
        expected = float(r.mean() / r.std() * np.sqrt(252))  # ddof=0
        np.testing.assert_allclose(_sharpe(r), expected, rtol=1e-12)

    def test_max_drawdown_monotonic_up_is_zero(self) -> None:
        assert _max_drawdown(np.full(50, 0.001)) == 0.0

    def test_max_drawdown_known_crash(self) -> None:
        # +100% (cum 2.0) then -50% (cum 1.0): peak 2.0, trough 1.0 -> dd -0.5
        np.testing.assert_allclose(_max_drawdown(np.array([1.0, -0.5])), -0.5, atol=1e-12)

    def test_max_drawdown_non_positive(self) -> None:
        rng = np.random.default_rng(4)
        r = rng.standard_normal(200) * 0.02
        assert _max_drawdown(r) <= 1e-12


# ── _regime_durations ───────────────────────────────────────────────────────

class TestRegimeDurations:
    def test_keys_present(self) -> None:
        out = _regime_durations(np.array([0, 0, 0, 1, 1, 0]))
        for k in ("regime_0_mean_duration", "regime_0_median_duration",
                  "regime_1_mean_duration", "regime_1_median_duration"):
            assert k in out

    def test_known_durations(self) -> None:
        # Two regime-0 segments (len 3 and 1) and one regime-1 segment (len 2).
        labels = np.array([0, 0, 0, 1, 1, 0])
        out = _regime_durations(labels)
        # regime_0 segments: [3, 1] -> mean 2.0, median np.median([3,1]) = 2.0
        assert out["regime_0_mean_duration"] == pytest.approx(2.0)
        assert out["regime_0_median_duration"] == pytest.approx(2.0)
        # regime_1 segments: [2] -> mean 2.0, median 2.0
        assert out["regime_1_mean_duration"] == pytest.approx(2.0)
        assert out["regime_1_median_duration"] == pytest.approx(2.0)

    def test_constant_regime(self) -> None:
        # Single regime the whole way -> one segment of length n.
        labels = np.zeros(10, dtype=int)
        out = _regime_durations(labels)
        assert out["regime_0_mean_duration"] == pytest.approx(10.0)
        assert out["regime_1_mean_duration"] == 0.0  # no regime-1 segment

    def test_empty_labels_returns_zeros(self) -> None:
        out = _regime_durations(np.array([], dtype=int))
        for v in out.values():
            assert v == 0.0
