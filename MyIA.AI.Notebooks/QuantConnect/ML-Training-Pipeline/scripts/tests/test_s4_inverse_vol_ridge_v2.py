"""Unit tests for s4_inverse_vol_ridge_v2 — Inverse-Vol Ridge regime KEEPER.

S4 (regime-conditional inverse-volatility weighting with Ridge shrinkage) is a
Curriculum-V3 KEEPER (per #1409: S4 v2 Regime+Ridge, delta +0.325 4/4 seeds) and
a production-candidate, yet had ZERO dedicated tests. This suite covers the
portfolio-construction primitives that carry the model's core logic:

- ``_project_simplex``: Euclidean projection onto the probability simplex
- ``inv_vol_weights``: inverse-volatility weights (lower vol -> higher weight)
- ``equal_weights``: uniform baseline
- ``regime_conditional_weights``: bear-regime defensive tilt + Ridge shrinkage
- ``block_bootstrap``: stationary block bootstrap resampling
- ``jitter_regime``: regime-switch perturbation for robustness seeds
- ``_sharpe`` / ``_max_drawdown``: performance statistics

All fixtures are deterministic synthetic arrays — no network, no GPU, no data
files, no statsmodels fit. The whole module runs in well under a second on CPU.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

SCRIPT_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from s4_inverse_vol_ridge_v2 import (  # noqa: E402
    DEFENSIVE,
    SYMBOLS,
    _max_drawdown,
    _project_simplex,
    _sharpe,
    block_bootstrap,
    equal_weights,
    inv_vol_weights,
    jitter_regime,
    regime_conditional_weights,
)


def _returns(t: int = 100, n_assets: int = len(SYMBOLS), seed: int = 0) -> np.ndarray:
    """Deterministic (T, n_assets) returns matrix."""
    rng = np.random.default_rng(seed)
    return rng.standard_normal((t, n_assets)) * 0.01


# ── _project_simplex ────────────────────────────────────────────────────────

class TestProjectSimplex:
    def test_sums_to_one_non_negative(self) -> None:
        rng = np.random.default_rng(0)
        for _ in range(10):
            v = rng.standard_normal(8) * 5
            w = _project_simplex(v)
            assert w.shape == (8,)
            assert (w >= -1e-12).all()
            assert abs(w.sum() - 1.0) < 1e-12

    def test_uniform_input_yields_uniform_output(self) -> None:
        w = _project_simplex(np.full(5, 3.0))
        np.testing.assert_allclose(w, np.full(5, 0.2), atol=1e-12)

    def test_known_two_asset_cases(self) -> None:
        # Corner case: [3, 1] -> [1, 0] (3 dominates, 1 is driven to 0).
        # Interior case: [1.5, 1.0] -> [0.75, 0.25] (both stay positive).
        np.testing.assert_allclose(_project_simplex(np.array([3.0, 1.0])),
                                   np.array([1.0, 0.0]), atol=1e-12)
        np.testing.assert_allclose(_project_simplex(np.array([1.5, 1.0])),
                                   np.array([0.75, 0.25]), atol=1e-12)

    def test_ordering_preserved(self) -> None:
        # A strictly larger input component must not get a smaller weight.
        v = np.array([4.0, 1.0, 2.0, 0.5])
        w = _project_simplex(v)
        order = np.argsort(v)  # ascending
        assert np.all(np.diff(w[order]) >= -1e-12)


# ── inv_vol_weights ─────────────────────────────────────────────────────────

class TestInvVolWeights:
    def test_is_valid_weight_vector(self) -> None:
        w = inv_vol_weights(_returns())
        assert w.shape == (len(SYMBOLS),)
        assert (w >= -1e-12).all()
        assert abs(w.sum() - 1.0) < 1e-9

    def test_lower_vol_gets_higher_weight(self) -> None:
        # Asset 0 has tiny vol, asset 1 huge vol -> w[0] > w[1].
        rng = np.random.default_rng(1)
        t = 200
        r = np.column_stack([
            rng.standard_normal(t) * 0.001,   # low vol
            rng.standard_normal(t) * 0.10,    # high vol
        ])
        w = inv_vol_weights(r)
        assert w[0] > w[1]

    def test_equal_vol_yields_equal_weight(self) -> None:
        rng = np.random.default_rng(2)
        base = rng.standard_normal(200) * 0.02
        r = np.column_stack([base, base, base])
        w = inv_vol_weights(r)
        np.testing.assert_allclose(w, np.full(3, 1.0 / 3.0), atol=1e-6)


# ── equal_weights ───────────────────────────────────────────────────────────

class TestEqualWeights:
    def test_uniform_valid(self) -> None:
        w = equal_weights(7)
        np.testing.assert_allclose(w, np.full(7, 1.0 / 7.0))
        assert abs(w.sum() - 1.0) < 1e-12

    def test_single_asset(self) -> None:
        np.testing.assert_allclose(equal_weights(1), np.array([1.0]))


# ── regime_conditional_weights ──────────────────────────────────────────────

class TestRegimeConditionalWeights:
    @staticmethod
    def _defensive_weight(w: np.ndarray) -> float:
        return float(sum(w[i] for i, s in enumerate(SYMBOLS) if s in DEFENSIVE))

    def test_bull_is_valid_weight_vector(self) -> None:
        w = regime_conditional_weights(_returns(), regime_label=0, alpha=1.0)
        assert w.shape == (len(SYMBOLS),)
        assert (w >= -1e-12).all()
        assert abs(w.sum() - 1.0) < 1e-9

    def test_bear_tilts_toward_defensive(self) -> None:
        # Bear regime (label=1) doubles defensive inverse-vol contribution ->
        # total weight on defensive assets must exceed the bull allocation.
        # Use equal-vol assets (tiled series) so base_w is spread ~uniform
        # and the bear tilt is not masked by a degenerate inv-vol corner.
        rng = np.random.default_rng(5)
        base = rng.standard_normal(300) * 0.01
        r = np.tile(base[:, None], (1, len(SYMBOLS)))
        bull = regime_conditional_weights(r, regime_label=0, alpha=0.0)
        bear = regime_conditional_weights(r, regime_label=1, alpha=0.0)
        assert self._defensive_weight(bear) > self._defensive_weight(bull) + 0.01

    def test_alpha_shrinks_toward_equal_weight(self) -> None:
        # Larger alpha -> more Ridge shrinkage toward equal-weight (less spread).
        r = _returns(seed=3)
        low_alpha = regime_conditional_weights(r, regime_label=0, alpha=0.01)
        high_alpha = regime_conditional_weights(r, regime_label=0, alpha=100.0)
        eq = equal_weights(len(SYMBOLS))
        assert np.abs(high_alpha - eq).sum() < np.abs(low_alpha - eq).sum()


# ── block_bootstrap ─────────────────────────────────────────────────────────

class TestBlockBootstrap:
    def test_preserves_length(self) -> None:
        data = np.arange(50, dtype=float)
        out = block_bootstrap(data, block_size=5, seed=1)
        assert out.shape == (50,)

    def test_deterministic_with_seed(self) -> None:
        data = np.arange(100, dtype=float)
        a = block_bootstrap(data, block_size=7, seed=42)
        b = block_bootstrap(data, block_size=7, seed=42)
        np.testing.assert_array_equal(a, b)

    def test_samples_from_input(self) -> None:
        # Every resampled element must be an element of the original array.
        data = np.array([10.0, 20.0, 30.0, 40.0, 50.0])
        out = block_bootstrap(data, block_size=2, seed=3)
        assert np.isin(out, data).all()

    def test_different_seeds_usually_differ(self) -> None:
        data = np.arange(80, dtype=float)
        a = block_bootstrap(data, block_size=6, seed=1)
        b = block_bootstrap(data, block_size=6, seed=2)
        assert not np.array_equal(a, b)


# ── jitter_regime ───────────────────────────────────────────────────────────

class TestJitterRegime:
    def test_seed_zero_is_identity(self) -> None:
        labels = np.array([0, 0, 0, 1, 1, 0, 0, 1, 1, 1])
        out = jitter_regime(labels, seed=0, max_jitter=5)
        np.testing.assert_array_equal(out, labels)

    def test_preserves_length_and_label_set(self) -> None:
        labels = np.array([0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0])
        out = jitter_regime(labels, seed=7, max_jitter=3)
        assert out.shape == labels.shape
        assert set(np.unique(out)).issubset(set(np.unique(labels)))


# ── _sharpe / _max_drawdown ─────────────────────────────────────────────────

class TestStatistics:
    def test_sharpe_too_short_returns_zero(self) -> None:
        assert _sharpe(np.array([0.01])) == 0.0

    def test_sharpe_zero_sigma_returns_zero(self) -> None:
        assert _sharpe(np.full(20, 0.001)) == 0.0

    def test_sharpe_known_value(self) -> None:
        rng = np.random.default_rng(0)
        r = rng.standard_normal(252) * 0.01
        expected = float(r.mean() / r.std() * np.sqrt(252))  # population std (ddof=0)
        np.testing.assert_allclose(_sharpe(r), expected, rtol=1e-12)

    def test_max_drawdown_monotonic_up_is_zero(self) -> None:
        # Strictly positive returns -> no drawdown.
        r = np.full(50, 0.001)
        assert _max_drawdown(r) == 0.0

    def test_max_drawdown_known_crash(self) -> None:
        # +100% then -50% round-trips to 0 -> drawdown of -50%.
        r = np.array([1.0, -0.5])  # cum: 2.0 -> 1.0; peak 2.0, trough 1.0
        np.testing.assert_allclose(_max_drawdown(r), -0.5, atol=1e-12)

    def test_max_drawdown_non_positive(self) -> None:
        rng = np.random.default_rng(4)
        r = rng.standard_normal(200) * 0.02
        assert _max_drawdown(r) <= 1e-12  # never positive
