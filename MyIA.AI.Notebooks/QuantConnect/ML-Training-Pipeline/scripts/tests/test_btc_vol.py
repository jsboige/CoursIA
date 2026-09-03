"""Tests for btc_vol.py helpers (issue #12734).

These cover the pure transformations in `scripts/bias_metrics.py`
(extracted from `btc_vol.py`, issue #14363):
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

from bias_metrics import (  # noqa: E402
    _dm_centered_mse,
    _mse_decomposition,
)
from btc_vol import (  # noqa: E402
    _dm_uncentered_mse,
)


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


def _har_like_pair(seed: int = 0, n: int = 300, har_bias: float = 0.5):
    """A (dl_errors, har_errors) pair whose biases differ, as in btc_vol.

    `har_errors` carries a non-zero mean; the de-biased series that
    `run_btc_debiased_recentered` builds is `har_errors - mean(har_errors)`,
    i.e. the *same* series shifted by a constant.
    """
    rng = np.random.default_rng(seed)
    dl_errors = rng.standard_normal(n) * 0.8
    har_errors = rng.standard_normal(n) * 1.0 + har_bias
    har_errors_debiased = har_errors - float(np.mean(har_errors))
    return dl_errors, har_errors, har_errors_debiased


class TestTwoLegsDiscriminate:
    """The two DM legs of `run_btc_debiased_recentered` must not coincide (#14362).

    The verdict leg is centered and runs against **de-biased** HAR; the sanity
    leg is un-centered and runs against **raw** HAR, reproducing the #11011
    keeper. Routing the sanity leg through `_dm_centered_mse` -- as the code
    did before #14362 -- makes the two bit-identical, because centering
    subtracts each series' own mean and the two HAR series differ by exactly
    a constant. A control that cannot go red is not a control.
    """

    def test_biases_actually_differ_in_the_fixture(self):
        """Guard the guard: the fixture must be a pair whose biases differ."""
        _, har_raw, har_deb = _har_like_pair()
        assert abs(float(np.mean(har_raw)) - float(np.mean(har_deb))) > 0.1
        assert float(np.mean(har_deb)) == pytest.approx(0.0, abs=1e-12)

    def test_legs_are_not_the_same_statistic(self):
        """THE sealed control: the two legs must return different statistics."""
        dl, har_raw, har_deb = _har_like_pair()
        verdict_leg = _dm_centered_mse(dl, har_deb, horizon=1)
        sanity_leg = _dm_uncentered_mse(dl, har_raw, horizon=1)
        assert abs(verdict_leg["dm_stat"] - sanity_leg["dm_stat"]) > 1e-6, (
            "the sanity leg reproduces the verdict leg -- it is centered "
            "somewhere it must not be (regression of #14362)"
        )

    def test_old_composition_is_degenerate(self):
        """Falsification: the pre-#14362 composition IS bit-identical.

        Without this, `test_legs_are_not_the_same_statistic` could pass for a
        reason unrelated to centering. Here we reproduce the old code path
        explicitly and show it collapses -- which is what makes the assertion
        above meaningful rather than incidental.
        """
        dl, har_raw, har_deb = _har_like_pair()
        old_verdict_leg = _dm_centered_mse(dl, har_deb, horizon=1)
        old_sanity_leg = _dm_centered_mse(dl, har_raw, horizon=1)  # the bug
        assert old_sanity_leg["dm_stat"] == pytest.approx(
            old_verdict_leg["dm_stat"], abs=1e-12
        )

    def test_centered_leg_is_invariant_under_constant_shift(self):
        """Why the collapse happens, stated as a property."""
        dl, har_raw, _ = _har_like_pair()
        base = _dm_centered_mse(dl, har_raw, horizon=1)
        shifted = _dm_centered_mse(dl, har_raw - 3.14159, horizon=1)
        assert shifted["dm_stat"] == pytest.approx(base["dm_stat"], abs=1e-12)

    def test_uncentered_leg_is_NOT_invariant_under_constant_shift(self):
        """The negative control of the property above, in the other direction."""
        dl, har_raw, _ = _har_like_pair()
        base = _dm_uncentered_mse(dl, har_raw, horizon=1)
        shifted = _dm_uncentered_mse(dl, har_raw - 3.14159, horizon=1)
        assert abs(shifted["dm_stat"] - base["dm_stat"]) > 1e-6

    def test_uncentered_leg_sees_a_pure_bias_gap(self):
        """A baseline that is only *biased* loses the un-centered leg...

        ...and does not lose the centered one. This is the substantive reason
        the sanity leg exists: it is the only one of the two that can tell
        `#11011`'s story (MSE inflated by the HAR bias).
        """
        rng = np.random.default_rng(11)
        n = 800
        dl = rng.standard_normal(n) * 0.7
        har = dl + 1.5  # SAME dispersion realisation, differing only by a constant
        uncentered = _dm_uncentered_mse(dl, har, horizon=1)
        centered = _dm_centered_mse(dl, har, horizon=1)
        # The un-centered leg sees the bias and calls it decisively.
        assert uncentered["dm_verdict"] == "BEATS baseline"
        assert uncentered["dm_pvalue"] < 1e-6
        # The centered leg is blind to it -- the differential is exactly zero.
        assert centered["dm_stat"] == pytest.approx(0.0, abs=1e-9)
        assert centered["dm_verdict"] == "INCONCLUSIVE"

    def test_uncentered_sentinels(self):
        assert (
            _dm_uncentered_mse(np.zeros(10), np.zeros(11), horizon=1)["dm_verdict"]
            == "SHAPE_MISMATCH"
        )
        assert (
            _dm_uncentered_mse(np.zeros(5), np.zeros(5), horizon=1)["dm_verdict"]
            == "INSUFFICIENT_DATA"
        )