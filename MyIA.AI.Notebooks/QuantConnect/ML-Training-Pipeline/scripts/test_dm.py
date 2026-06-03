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
