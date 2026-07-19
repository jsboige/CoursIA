"""Unit tests for m11d_hmm_kelly — HMM regime-conditional Kelly sizing.

These cover the *regime-conditional Kelly* logic that distinguishes M11d from
the M11a/M11b/M11c kelly_har_mu60 baseline (the latter uses a global rolling
mean for ``mu``):

- ``_regime_persistence``: mean run length of consecutive identical-regime days
- ``_regime_conditional_mu``: trailing-``mu_window`` mean of log-returns
  restricted to days sharing today's regime label, with fallback to the
  unrestricted rolling mean when in-regime samples are fewer than
  ``min_in_regime``; strict ``shift(1)`` (uses only data with index < t).
- ``_kelly_returns_regime``: Kelly fraction ``f = clip(mu_regime / sigma2_HAR,
  0, kelly_cap)`` with fee drag from turnover (``fee_bps / 1e4 * |Δf|``).
- ``_fit_hmm_winsorized``: 2-state Gaussian HMM with MAD winsorization (clip at
  median ± 4·MAD); degenerate short input returns a uniform-prior HMM.
- ``_regime_labels_walkforward``: walk-forward online Viterbi regime decode
  (smoke test on synthetic 2-regime data — shape, label range, diagnostic dict).

All fixtures are deterministic synthetic series — no network, no GPU, no data
files. The whole module runs in well under a second on CPU.
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

from m11d_hmm_kelly import (  # noqa: E402
    _fit_hmm_winsorized,
    _kelly_returns_regime,
    _regime_conditional_mu,
    _regime_labels_walkforward,
    _regime_persistence,
)
from regime_detector import GaussianHMM  # noqa: E402


# ── Fixtures ────────────────────────────────────────────────────────────────

def _daily_logret(n: int = 200, seed: int = 0) -> pd.Series:
    """Deterministic synthetic daily log-returns (date index)."""
    rng = np.random.default_rng(seed)
    idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
    return pd.Series(rng.standard_normal(n) * 0.01, index=idx, name="r")


@pytest.fixture
def daily() -> pd.Series:
    return _daily_logret()


# ── _regime_persistence ─────────────────────────────────────────────────────


class TestRegimePersistence:
    """Mean run length of consecutive identical-regime days."""

    def test_empty_returns_zero(self):
        assert _regime_persistence(np.array([], dtype=int)) == 0.0

    def test_single_element_returns_one(self):
        assert _regime_persistence(np.array([0])) == 1.0

    def test_all_same_regime_equals_length(self):
        # One run of length 5 -> mean run length 5.
        assert _regime_persistence(np.array([1, 1, 1, 1, 1])) == 5.0

    def test_mixed_runs_mean(self):
        # [0,0,1,1,1,0] -> runs [2,3,1] -> mean = 6/3 = 2.0
        assert _regime_persistence(np.array([0, 0, 1, 1, 1, 0])) == 2.0

    def test_alternating_returns_one(self):
        # [0,1,0,1] -> runs [1,1,1,1] -> mean = 1.0
        assert _regime_persistence(np.array([0, 1, 0, 1])) == 1.0

    def test_returns_python_float(self):
        out = _regime_persistence(np.array([0, 0, 1]))
        assert isinstance(out, float)


# ── _regime_conditional_mu ──────────────────────────────────────────────────


class TestRegimeConditionalMu:
    """Rolling regime-conditional mu with unrestricted fallback."""

    def test_first_element_is_nan(self, daily):
        # i=0 has no past data and fallback_mu.iloc[-1] path is guarded by i>=1.
        regime = pd.Series(0, index=daily.index)
        mu = _regime_conditional_mu(daily, regime, mu_window=10, min_in_regime=5)
        assert np.isnan(mu.iloc[0])

    def test_fallback_when_too_few_in_regime(self):
        # All days in regime 0, but a tiny window so in-regime count < min_in_regime:
        # mu must fall back to the unrestricted rolling mean (shifted by 1).
        n = 30
        idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
        r = pd.Series(np.arange(n, dtype=float), index=idx, name="r")
        regime = pd.Series(0, index=idx)
        mu_window, min_in_regime = 5, 50  # impossible threshold -> always fallback
        mu = _regime_conditional_mu(r, regime, mu_window=mu_window, min_in_regime=min_in_regime)
        fallback = r.rolling(mu_window).mean()
        # From i=1 onward, fallback path uses fallback_mu.iloc[i-1]; while the
        # rolling mean is still warming up that value is NaN (and propagates),
        # then both become the same finite number.
        for i in range(1, n):
            f_val = fallback.iloc[i - 1]
            if np.isnan(f_val):
                assert np.isnan(mu.iloc[i])
            else:
                assert mu.iloc[i] == f_val

    def test_regime_conditional_when_enough_matches(self):
        # Two regimes, each frequent enough in the window: mu at day t is the
        # mean of prior in-regime days only (NOT the unrestricted mean).
        n = 40
        idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
        r = pd.Series(np.arange(n, dtype=float), index=idx, name="r")
        # Alternating regimes 0/1 — both well represented in any 20-day window.
        regime = pd.Series(np.array([i % 2 for i in range(n)]), index=idx)
        mu = _regime_conditional_mu(r, regime, mu_window=20, min_in_regime=5)
        # At day 30 (regime 0): in-regime past days are {28,26,...,10} (even idxs
        # in [10,30)), mean of those.
        t = 30
        lo = max(0, t - 20)
        in_reg = r.values[lo:t][regime.values[lo:t] == regime.values[t]]
        assert mu.iloc[t] == pytest.approx(in_reg.mean())

    def test_shift1_excludes_current_day(self):
        # Day t's own return must NOT influence mu at t (shift(1) discipline).
        n = 25
        idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
        r = pd.Series(np.zeros(n), index=idx, name="r")
        regime = pd.Series(0, index=idx)
        # Spike ONLY day 20; if shift discipline holds, mu at 20 is the mean of
        # prior in-regime days (all zero) -> exactly 0, unaffected by the spike.
        r.iloc[20] = 1e6
        mu = _regime_conditional_mu(r, regime, mu_window=15, min_in_regime=5)
        assert mu.iloc[20] == pytest.approx(0.0)


# ── _kelly_returns_regime ───────────────────────────────────────────────────


class TestKellyReturnsRegime:
    """Kelly fraction = clip(mu_regime / sigma2_HAR, 0, kelly_cap), minus fees."""

    def _aligned_inputs(self, n: int = 120, seed: int = 1):
        idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
        rng = np.random.default_rng(seed)
        r = pd.Series(rng.standard_normal(n) * 0.01, index=idx, name="r")
        # log-RV around log(1e-4) so sigma2 = exp(logrv) ~ 1e-4.
        logrv = pd.Series(np.full(n, np.log(1e-4)), index=idx, name="logrv")
        regime = pd.Series(0, index=idx)
        return r, logrv, regime

    def test_short_series_returns_empty(self):
        # Fewer than mu_window+30 aligned points -> empty result.
        n = 20
        idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
        r = pd.Series(np.zeros(n), index=idx)
        logrv = pd.Series(np.zeros(n), index=idx)
        regime = pd.Series(0, index=idx)
        net, f = _kelly_returns_regime(r, logrv, regime, mu_window=60,
                                       kelly_cap=1.0, fee_bps=10.0)
        assert net.empty and f.empty

    def test_negative_mu_clipped_to_zero(self):
        # All-negative returns -> mu negative -> f clipped to 0 (long-only).
        n = 120
        idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
        r = pd.Series(np.full(n, -0.01), index=idx)
        logrv = pd.Series(np.full(n, np.log(1e-4)), index=idx)
        regime = pd.Series(0, index=idx)
        _, f = _kelly_returns_regime(r, logrv, regime, mu_window=60,
                                     kelly_cap=2.0, fee_bps=0.0)
        assert (f >= 0).all()
        # After the warmup where mu is defined and negative, fraction is 0.
        assert (f.iloc[-20:] == 0.0).all()

    def test_kelly_cap_clipping(self):
        # Tiny sigma2 + large positive mu -> f = mu/sigma2 huge -> clipped to cap.
        n = 120
        idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
        r = pd.Series(np.full(n, 0.01), index=idx)  # positive mu
        logrv = pd.Series(np.full(n, np.log(1e-12)), index=idx)  # tiny sigma2
        regime = pd.Series(0, index=idx)
        cap = 0.5
        _, f = _kelly_returns_regime(r, logrv, regime, mu_window=60,
                                     kelly_cap=cap, fee_bps=0.0)
        assert (f <= cap + 1e-12).all()
        # In the region where mu is defined, fraction is pinned at the cap.
        assert np.isclose(f.iloc[-1], cap)

    def test_zero_turnover_no_fee_drag(self):
        # Constant fraction -> turnover 0 -> net == pnl (no fee), with fee_bps>0.
        n = 120
        idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
        # Positive constant returns -> once mu is defined, f is constant (cap).
        r = pd.Series(np.full(n, 0.01), index=idx)
        logrv = pd.Series(np.full(n, np.log(1e-12)), index=idx)
        regime = pd.Series(0, index=idx)
        net, f = _kelly_returns_regime(r, logrv, regime, mu_window=60,
                                       kelly_cap=0.5, fee_bps=50.0)
        # Where f is flat (tail), turnover==0 so net == f*r exactly.
        tail = slice(-10, None)
        assert np.allclose(net.iloc[tail].values, f.iloc[tail].values * r.iloc[tail].values)

    def test_fee_drag_reduces_net(self):
        # With turnover (varying f) and fee_bps>0, net < gross pnl somewhere.
        n = 120
        idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
        rng = np.random.default_rng(7)
        r = pd.Series(rng.standard_normal(n) * 0.02, index=idx)
        logrv = pd.Series(np.full(n, np.log(1e-4)), index=idx)
        regime = pd.Series(0, index=idx)
        net, f = _kelly_returns_regime(r, logrv, regime, mu_window=60,
                                       kelly_cap=1.0, fee_bps=100.0)
        pnl = f.values * r.values
        # Where there is non-trivial turnover, net < pnl (fee drag active).
        turnover = np.abs(np.diff(f.values, prepend=f.values[0]))
        busy = np.where(turnover > 1e-6)[0]
        assert len(busy) > 0
        assert np.all(net.values[busy] <= pnl[busy] + 1e-15)

    def test_returns_named_series(self):
        r, logrv, regime = self._aligned_inputs()
        net, f = _kelly_returns_regime(r, logrv, regime, mu_window=60,
                                       kelly_cap=1.0, fee_bps=10.0)
        assert not net.empty
        assert net.name == "net"
        assert f.name == "f"
        assert len(net) == len(f)


# ── _fit_hmm_winsorized ─────────────────────────────────────────────────────


class TestFitHmmWinsorized:
    """2-state Gaussian HMM with MAD winsorization."""

    def test_returns_correct_n_states(self):
        x = np.random.default_rng(0).standard_normal(200) * 0.01
        hmm = _fit_hmm_winsorized(x, n_states=2)
        assert isinstance(hmm, GaussianHMM)
        assert hmm.n_states == 2

    def test_fit_params_finite(self):
        x = np.random.default_rng(1).standard_normal(200) * 0.01
        hmm = _fit_hmm_winsorized(x, n_states=3)
        assert np.all(np.isfinite(hmm.mu.ravel()))
        assert np.all(np.isfinite(hmm.sig.ravel()))
        assert np.all(np.isfinite(hmm.A))
        assert np.all(np.isfinite(hmm.pi))
        # Transition matrix rows sum to 1.
        assert np.allclose(hmm.A.sum(axis=1), 1.0)

    def test_bimodal_data_yields_separated_states(self):
        # Two well-separated Gaussian blobs -> fitted means should differ.
        rng = np.random.default_rng(2)
        x = np.concatenate([
            rng.normal(-0.05, 0.005, 150),
            rng.normal(0.05, 0.005, 150),
        ])
        hmm = _fit_hmm_winsorized(x, n_states=2)
        means = np.sort(hmm.mu.ravel())
        assert means[1] - means[0] > 0.05  # clearly separated

    def test_winsorization_resists_outliers(self):
        # A few extreme outliers should not blow up the variance: 4-MAD clip
        # keeps fitted sigmas bounded relative to the inlier spread.
        rng = np.random.default_rng(3)
        x = rng.normal(0, 0.01, 300)
        x[:5] = 1e3  # gross outliers
        hmm = _fit_hmm_winsorized(x, n_states=2)
        # Without winsorization sig would be ~ var of 1e3 outliers; with it,
        # sigmas stay close to the inlier scale (<< 1).
        assert np.all(hmm.sig.ravel() < 1.0)

    def test_degenerate_short_input(self):
        # < 60 finite points -> uniform-prior HMM (n_iter=2), still a valid fit.
        x = np.random.default_rng(4).standard_normal(20) * 0.01
        hmm = _fit_hmm_winsorized(x, n_states=2)
        assert isinstance(hmm, GaussianHMM)
        assert hmm.n_states == 2

    def test_drops_non_finite(self):
        # NaN/inf entries are filtered before fitting (no exception).
        x = np.random.default_rng(5).standard_normal(200) * 0.01
        x[::20] = np.nan
        x[1::20] = np.inf
        hmm = _fit_hmm_winsorized(x, n_states=2)
        assert np.all(np.isfinite(hmm.mu.ravel()))


# ── _regime_labels_walkforward (smoke) ──────────────────────────────────────


class TestRegimeLabelsWalkforward:
    """Walk-forward online Viterbi regime decode — shape + diagnostics."""

    def test_short_series_returns_zeros(self):
        # len(daily) < train_min + refit_every -> degenerate zeros path.
        n = 50
        idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
        daily = pd.Series(np.zeros(n), index=idx)
        labels, diag = _regime_labels_walkforward(
            daily, idx, n_splits=5, refit_every=22, n_states=2, train_min=250,
        )
        assert len(labels) == n
        assert (labels == 0).all()
        assert diag["n_refits"] == 0
        assert len(diag["regime_means"]) == 2

    def test_smoke_two_regime_synthetic(self):
        # Clear 2-regime structure: low-vol bearish first half, high-vol bullish
        # second half. Exercise the real walk-forward path (lowered train_min).
        rng = np.random.default_rng(42)
        n = 400
        idx = pd.date_range("2020-01-01", periods=n, freq="D", name="date")
        bear = rng.normal(-0.002, 0.005, n // 2)
        bull = rng.normal(0.004, 0.015, n - n // 2)
        daily = pd.Series(np.concatenate([bear, bull]), index=idx, name="r")
        labels, diag = _regime_labels_walkforward(
            daily, idx, n_splits=5, refit_every=22, n_states=2, train_min=120,
        )
        # Shape + label range.
        assert len(labels) == n
        assert set(np.unique(labels.values)).issubset({0, 1})
        # Diagnostic dict contract.
        assert {"regime_means", "regime_vols", "A", "n_refits"} <= set(diag.keys())
        assert diag["n_refits"] >= 1
        assert len(diag["regime_means"]) == 2
        assert len(diag["regime_vols"]) == 2
        # The two regimes should have different conditional means (sorted ascending).
        m = diag["regime_means"]
        assert m[1] > m[0]
