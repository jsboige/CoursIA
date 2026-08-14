"""Unit tests for dm_test.py — Diebold-Mariano with HAC variance."""

from __future__ import annotations

import numpy as np
import pytest
from numpy.testing import assert_allclose

from dm_test import (
    DMResult,
    _newey_west_variance,
    _optimal_lag,
    diebold_mariano_test,
    dm_verdict,
)

rng = np.random.default_rng(42)


def _make_errors(n: int, sigma_a: float = 1.0, sigma_b: float = 1.0) -> tuple[np.ndarray, np.ndarray]:
    return rng.normal(0, sigma_a, n), rng.normal(0, sigma_b, n)


class TestNeweyWestVariance:
    def test_iid_positive(self):
        x = rng.normal(0, 1, 500)
        var_nw = _newey_west_variance(x, max_lag=5)
        assert var_nw > 0

    def test_near_constant_near_zero(self):
        x = np.ones(50)
        var_nw = _newey_west_variance(x, max_lag=3)
        assert var_nw >= 0

    def test_single_element(self):
        var_nw = _newey_west_variance(np.array([3.0]), max_lag=1)
        assert np.isnan(var_nw) or var_nw == 0.0


class TestOptimalLag:
    def test_typical_n(self):
        assert _optimal_lag(1000) >= 1
        assert _optimal_lag(1000) == int(np.floor(1000 ** (1 / 3)))

    def test_small_n(self):
        assert _optimal_lag(5) == 1


class TestDieboldMarianoTest:
    def test_identical_errors_inconclusive(self):
        e = rng.normal(0, 1, 200)
        result = diebold_mariano_test(e, e)
        assert result.p_value > 0.05
        assert abs(result.mean_loss_diff) < 1e-10

    def test_better_model_detected(self):
        e_good = rng.normal(0, 0.5, 500)
        e_bad = rng.normal(0, 2.0, 500)
        result = diebold_mariano_test(e_good, e_bad, loss_fn="mse")
        assert result.mean_loss_diff < 0
        assert result.p_value < 0.01

    def test_mae_loss(self):
        e_good = rng.normal(0, 0.5, 500)
        e_bad = rng.normal(0, 2.0, 500)
        result = diebold_mariano_test(e_good, e_bad, loss_fn="mae")
        assert result.p_value < 0.01

    def test_hln_correction_changes_statistic(self):
        e_a, e_b = _make_errors(200, 0.5, 1.5)
        with_hln = diebold_mariano_test(e_a, e_b, hln_correction=True, horizon=1)
        without_hln = diebold_mariano_test(e_a, e_b, hln_correction=False)
        assert with_hln.dm_statistic != without_hln.dm_statistic

    def test_horizon_affects_correction(self):
        e_a, e_b = _make_errors(200, 0.5, 1.5)
        h1 = diebold_mariano_test(e_a, e_b, hln_correction=True, horizon=1)
        h5 = diebold_mariano_test(e_a, e_b, hln_correction=True, horizon=5)
        assert h1.dm_statistic != h5.dm_statistic

    def test_shape_mismatch_raises(self):
        with pytest.raises(ValueError, match="Shape mismatch"):
            diebold_mariano_test(np.ones(10), np.ones(20))

    def test_2d_raises(self):
        with pytest.raises(ValueError, match="1-D"):
            diebold_mariano_test(np.ones((10, 2)), np.ones((10, 2)))

    def test_too_few_obs_raises(self):
        with pytest.raises(ValueError, match=">=10"):
            diebold_mariano_test(np.ones(5), np.ones(5))

    def test_invalid_loss_fn(self):
        with pytest.raises(ValueError, match="loss_fn"):
            diebold_mariano_test(np.ones(50), np.ones(50), loss_fn="rmse")

    def test_linear_loss_distinguishes_opposite_series(self):
        """Regression #10228 relue (#10956): linear distinguishes e from -e.

        Under mse, a forecast-error series and its exact opposite are
        bit-identical -- correct behavior: the two are equally precise. Under
        linear, d_mean = bias_a - bias_b gives them opposite signs, but that
        sign is a BIAS statement, not a precision statement (linear is blind
        to dispersion; see test_linear_loss_is_bias_differential).
        """
        rng2 = np.random.default_rng(7)
        e = rng2.normal(0.5, 1.0, 500)  # nonzero mean so d_mean != 0
        zero = np.zeros_like(e)
        # mse is symmetric: e and -e give the same statistic.
        r_mse_pos = diebold_mariano_test(e, zero, loss_fn="mse")
        r_mse_neg = diebold_mariano_test(-e, zero, loss_fn="mse")
        assert r_mse_pos.dm_statistic == pytest.approx(r_mse_neg.dm_statistic)
        # linear preserves the sign: e and -e give opposite-sign statistics.
        r_lin_pos = diebold_mariano_test(e, zero, loss_fn="linear")
        r_lin_neg = diebold_mariano_test(-e, zero, loss_fn="linear")
        assert r_lin_pos.dm_statistic != pytest.approx(r_lin_neg.dm_statistic)
        assert r_lin_pos.dm_statistic * r_lin_neg.dm_statistic < 0

    def test_linear_loss_is_bias_differential(self):
        """Regression #10956: d_mean = bias_a - bias_b, blind to dispersion.

        Model A (MSE ~0.009, bias ~0) vs baseline B (MSE ~0.103, bias -0.3):
        mse correctly declares A the winner; linear reports d_mean > 0, which
        the verdict convention reads as "BEATEN BY baseline". A strictly more
        precise forecast loses under linear -- exactly the measured
        HAR-vs-DLinear case (#10938).
        """
        rng3 = np.random.default_rng(42)
        e_a = rng3.normal(0, 0.1, 500)         # precise, unbiased
        e_b = -0.3 + rng3.normal(0, 0.1, 500)  # ~11x less precise, biased
        r_mse = diebold_mariano_test(e_a, e_b, loss_fn="mse")
        r_lin = diebold_mariano_test(e_a, e_b, loss_fn="linear")
        assert r_mse.mean_loss_diff < 0                 # A wins under mse
        assert r_lin.mean_loss_diff > 0                 # same pair "loses" under linear
        assert r_lin.mean_loss_diff == pytest.approx(
            np.mean(e_a) - np.mean(e_b)
        )

    def test_linear_loss_blind_to_dispersion(self):
        """Regression #10956: identical bias, radically different precision.

        Two forecasts with identical bias (0.5) but ~15x different MSE give
        d_mean = 0 and p = 1 under linear (INCONCLUSIVE), even though one is
        far more precise. mse detects the gap.
        """
        rng4 = np.random.default_rng(7)
        n = 500
        u = rng4.normal(0, 0.1, n)
        v = rng4.normal(0, 2.0, n)
        e_a = 0.5 + (u - u.mean())             # sample bias exactly 0.5
        e_b = 0.5 + (v - v.mean())
        assert np.isclose(np.mean(e_a), np.mean(e_b))
        assert np.mean(e_a ** 2) < np.mean(e_b ** 2) / 10
        r_lin = diebold_mariano_test(e_a, e_b, loss_fn="linear")
        r_mse = diebold_mariano_test(e_a, e_b, loss_fn="mse")
        assert abs(r_lin.mean_loss_diff) < 1e-12  # d_mean = bias_a - bias_b = 0
        assert r_lin.p_value > 0.05
        assert r_mse.mean_loss_diff < 0
        assert r_mse.p_value < 0.01


class TestDmVerdict:
    def test_model_wins(self):
        e_good = rng.normal(0, 0.3, 500)
        e_bad = rng.normal(0, 2.0, 500)
        v = dm_verdict(e_good, e_bad)
        assert v["verdict"] == "BEATS baseline"
        assert v["p_value"] < 0.05
        assert v["mean_loss_diff"] < 0

    def test_model_loses(self):
        e_bad = rng.normal(0, 2.0, 500)
        e_good = rng.normal(0, 0.3, 500)
        v = dm_verdict(e_bad, e_good)
        assert v["verdict"] == "BEATEN BY baseline"
        assert v["p_value"] < 0.05

    def test_inconclusive_similar(self):
        e_a = rng.normal(0, 1.0, 200)
        e_b = rng.normal(0, 1.0, 200)
        v = dm_verdict(e_a, e_b)
        assert v["verdict"] == "INCONCLUSIVE"
