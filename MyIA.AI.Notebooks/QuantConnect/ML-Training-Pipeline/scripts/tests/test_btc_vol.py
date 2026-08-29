"""Tests for btc_vol.py helpers (issue #12734).

These cover the pure transformations in `scripts/btc_vol.py`:
  - `_mse_decomposition`: split MSE into bias^2 + variance.
  - `_dm_centered_mse`: DM test on errors centered by their own mean.

The full BTC re-validation run needs Bitstamp data + GPU/CPU walk-forward
(not exercised here -- covered by the smoke test that committed
`scripts/results/test_recentered.json` during #12734 development).
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

# Make the parent directory importable.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from btc_vol import _dm_centered_mse, _mse_decomposition  # noqa: E402


class TestMseDecomposition:
    def test_zero_bias_zero_variance(self):
        """All-zero errors -> MSE=0, bias^2=0, variance=0."""
        e = np.zeros(100)
        d = _mse_decomposition(e)
        assert d["mse"] == 0.0
        assert d["bias_sq"] == 0.0
        assert d["variance"] == 0.0

    def test_constant_nonzero_bias(self):
        """Constant +c errors -> MSE=c^2, bias^2=c^2, variance=0."""
        e = np.full(50, 0.5)
        d = _mse_decomposition(e)
        assert d["mse"] == pytest.approx(0.25, abs=1e-10)
        assert d["bias_sq"] == pytest.approx(0.25, abs=1e-10)
        assert d["variance"] == pytest.approx(0.0, abs=1e-12)

    def test_known_decomposition(self):
        """A specific non-trivial case: mean(e)=0.1, var=0.04."""
        e = np.array([0.0, 0.2])
        # mean=0.1, bias^2=0.01
        # variance = (0.1^2 + 0.1^2)/2 = 0.01
        # MSE = (0^2 + 0.2^2)/2 = 0.02 = bias^2 + variance = 0.01 + 0.01 = 0.02 ✓
        d = _mse_decomposition(e)
        assert d["mse"] == pytest.approx(0.02, abs=1e-10)
        assert d["bias_sq"] == pytest.approx(0.01, abs=1e-10)
        assert d["variance"] == pytest.approx(0.01, abs=1e-10)

    def test_empty_returns_nan(self):
        d = _mse_decomposition(np.array([]))
        assert np.isnan(d["mse"])
        assert np.isnan(d["bias_sq"])
        assert np.isnan(d["variance"])

    def test_none_returns_nan(self):
        d = _mse_decomposition(None)
        assert np.isnan(d["mse"])
        assert np.isnan(d["bias_sq"])
        assert np.isnan(d["variance"])


class TestDmCenteredMse:
    def test_centered_errors_have_zero_mean_differential(self):
        """After centering, the loss differential's mean equals 0.

        This is the structural property #12734 relies on: the DM on centered
        errors measures the *variance* differential, not the bias. If we feed
        errors with very different biases, the dm_stat should reflect only the
        variance ratio.
        """
        rng = np.random.default_rng(0)
        n = 200
        # Two error series with same variance but very different means.
        e_a = rng.standard_normal(n) * 0.5 + 1.0   # bias = 1.0
        e_b = rng.standard_normal(n) * 0.5 - 0.5   # bias = -0.5
        out = _dm_centered_mse(e_a, e_b, horizon=1)
        # Centering erases the bias gap; the loss differential d = (e_a')^2 - (e_b')^2
        # has zero mean by construction (variances equal -> means cancel on average).
        # The dm_stat may be small but the verdict is INCONCLUSIVE or low-significance.
        assert "dm_stat" in out
        assert "dm_pvalue" in out
        assert "dm_verdict" in out
        # p_value should be high (no significant precision differential).
        assert out["dm_pvalue"] > 0.05

    def test_shape_mismatch(self):
        e_a = np.zeros(10)
        e_b = np.zeros(11)
        out = _dm_centered_mse(e_a, e_b, horizon=1)
        assert out["dm_verdict"] == "SHAPE_MISMATCH"

    def test_insufficient_data(self):
        e_a = np.zeros(5)
        e_b = np.zeros(5)
        out = _dm_centered_mse(e_a, e_b, horizon=1)
        assert out["dm_verdict"] == "INSUFFICIENT_DATA"

    def test_clearly_more_precise_wins_on_centered(self):
        """DLinear with much smaller centered-error variance should BEATS HAR.

        Construct two error series with identical mean (~1.0) but very
        different dispersions. After centering, the model with smaller
        variance should produce a strongly negative `mean_loss_diff`
        (negative = model wins) and a significant dm_pvalue.
        """
        rng = np.random.default_rng(42)
        n = 1000
        # Model A: tight errors around the bias.
        e_a = rng.standard_normal(n) * 0.3 + 1.0
        # Model B (baseline): wide errors around the same bias.
        e_b = rng.standard_normal(n) * 1.0 + 1.0
        out = _dm_centered_mse(e_a, e_b, horizon=1)
        assert out["dm_verdict"] == "BEATS baseline"
        assert out["dm_pvalue"] < 0.05
        assert out["dm_stat"] < -2.0  # negative = model wins (smaller MSE)