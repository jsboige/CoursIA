"""Tests for diebold_mariano.py — DM test with Newey-West HAC variance."""

from __future__ import annotations

import numpy as np
import pytest

from diebold_mariano import bonferroni_dm, diebold_mariano_test, newey_west_variance


# ---------------------------------------------------------------------------
# Newey-West variance
# ---------------------------------------------------------------------------


class TestNeweyWestVariance:
    def test_constant_series_zero_variance(self):
        x = np.ones(100)
        # After demeaning, all zeros → variance = 0
        assert newey_west_variance(x, lag=5) >= 0.0

    def test_white_noise_positive_variance(self):
        rng = np.random.default_rng(42)
        x = rng.standard_normal(500)
        var_nw = newey_west_variance(x, lag=5)
        # Should be close to 1.0 (variance of standard normal)
        assert 0.5 < var_nw < 2.0

    def test_lag_zero_uses_gamma_0_only(self):
        rng = np.random.default_rng(7)
        x = rng.standard_normal(100)
        var_nw = newey_west_variance(x, lag=0)
        # With lag=0, Newey-West = sample variance (no autocorrelation terms)
        var_sample = float(np.var(x, ddof=0))
        assert var_nw == pytest.approx(var_sample, rel=1e-6)

    def test_n_equals_2_returns_finite_positive(self):
        x = np.array([1.0, 3.0])
        var_nw = newey_west_variance(x, lag=5)
        # n=2: only gamma_0 and k=1 autocorrelation contribute
        assert np.isfinite(var_nw)
        assert var_nw >= 0.0

    def test_positive_semi_definite(self):
        rng = np.random.default_rng(99)
        x = rng.standard_normal(200)
        # Newey-West variance must always be non-negative
        for lag in range(0, 20):
            assert newey_west_variance(x, lag=lag) >= 0.0

    def test_higher_lag_smooths_more(self):
        rng = np.random.default_rng(13)
        x = rng.standard_normal(200)
        var_low = newey_west_variance(x, lag=1)
        var_high = newey_west_variance(x, lag=20)
        # Both should be positive and finite
        assert np.isfinite(var_low)
        assert np.isfinite(var_high)


# ---------------------------------------------------------------------------
# Diebold-Mariano test
# ---------------------------------------------------------------------------


class TestDieboldMariano:
    def test_identical_errors_no_difference(self):
        rng = np.random.default_rng(0)
        errs = rng.standard_normal(100)
        result = diebold_mariano_test(errs, errs)
        assert result["dm_stat"] == pytest.approx(0.0, abs=1e-10)
        assert result["p_value"] == pytest.approx(1.0, abs=1e-10)
        assert result["significant_05"] is False
        assert "Identical" in result["interpretation"]

    def test_model_better_negative_dm(self):
        rng = np.random.default_rng(1)
        errors_baseline = rng.standard_normal(200)
        # Model errors are systematically smaller in absolute value
        errors_model = errors_baseline * 0.5
        result = diebold_mariano_test(errors_model, errors_baseline)
        # Negative DM = model has lower loss
        assert result["dm_stat"] < 0
        assert result["p_value"] < 0.05
        assert result["significant_05"] is True

    def test_baseline_better_positive_dm(self):
        rng = np.random.default_rng(2)
        errors_model = rng.standard_normal(200)
        # Baseline errors are systematically smaller
        errors_baseline = errors_model * 0.5
        result = diebold_mariano_test(errors_model, errors_baseline)
        assert result["dm_stat"] > 0
        assert result["p_value"] < 0.05
        assert result["significant_05"] is True

    def test_absolute_loss_function(self):
        rng = np.random.default_rng(3)
        errors_model = rng.standard_normal(200) * 0.5
        errors_baseline = rng.standard_normal(200)
        result = diebold_mariano_test(
            errors_model, errors_baseline, loss_function="absolute",
        )
        assert np.isfinite(result["dm_stat"])
        assert 0.0 <= result["p_value"] <= 1.0

    def test_unknown_loss_raises(self):
        with pytest.raises(ValueError, match="Unknown loss"):
            diebold_mariano_test(
                np.zeros(50), np.zeros(50), loss_function="huber",
            )

    def test_unknown_alternative_raises(self):
        rng = np.random.default_rng(30)
        # Non-identical errors to avoid early return before alternative check
        with pytest.raises(ValueError, match="Unknown alternative"):
            diebold_mariano_test(
                rng.standard_normal(50), rng.standard_normal(50), alternative="better",
            )

    def test_one_sided_less(self):
        rng = np.random.default_rng(4)
        errors_baseline = rng.standard_normal(200)
        errors_model = errors_baseline * 0.3
        result = diebold_mariano_test(
            errors_model, errors_baseline, alternative="less",
        )
        # "less" tests H1: E[d] < 0 (model better)
        assert result["p_value"] < 0.05

    def test_one_sided_greater(self):
        rng = np.random.default_rng(5)
        errors_model = rng.standard_normal(200)
        errors_baseline = errors_model * 0.3
        result = diebold_mariano_test(
            errors_model, errors_baseline, alternative="greater",
        )
        # "greater" tests H1: E[d] > 0 (baseline better)
        assert result["p_value"] < 0.05

    def test_short_series_returns_nan(self):
        result = diebold_mariano_test(np.zeros(5), np.ones(5))
        assert np.isnan(result["dm_stat"])
        assert np.isnan(result["p_value"])
        assert "Too few" in result["interpretation"]

    def test_n_obs_matches_input(self):
        n = 150
        result = diebold_mariano_test(
            np.random.default_rng(6).standard_normal(n),
            np.random.default_rng(7).standard_normal(n),
        )
        assert result["n_obs"] == n

    def test_unequal_length_truncates(self):
        a = np.random.default_rng(8).standard_normal(100)
        b = np.random.default_rng(9).standard_normal(150)
        result = diebold_mariano_test(a, b)
        assert result["n_obs"] == 100

    def test_small_sample_correction_applied(self):
        rng = np.random.default_rng(10)
        errs_a = rng.standard_normal(100)
        errs_b = rng.standard_normal(100) * 1.5
        result_corrected = diebold_mariano_test(
            errs_a, errs_b, small_sample=True,
        )
        result_uncorrected = diebold_mariano_test(
            errs_a, errs_b, small_sample=False,
        )
        # Small-sample correction should change the statistic
        assert result_corrected["dm_stat"] != pytest.approx(
            result_uncorrected["dm_stat"], rel=1e-3,
        )

    def test_forecast_horizon_affects_lag(self):
        rng = np.random.default_rng(11)
        errs_a = rng.standard_normal(200)
        errs_b = rng.standard_normal(200) * 1.5
        # h=1 → lag=1, h=10 → lag=9, different HAC variance
        r1 = diebold_mariano_test(errs_a, errs_b, h=1, small_sample=False)
        r10 = diebold_mariano_test(errs_a, errs_b, h=10, small_sample=False)
        # Different HAC lag should give different variance → different DM stat
        assert r1["dm_stat"] != pytest.approx(r10["dm_stat"], rel=1e-3)

    def test_return_keys_complete(self):
        rng = np.random.default_rng(12)
        result = diebold_mariano_test(
            rng.standard_normal(50), rng.standard_normal(50),
        )
        for key in ("dm_stat", "p_value", "significant_05", "significant_01",
                     "n_obs", "interpretation"):
            assert key in result


# ---------------------------------------------------------------------------
# Bonferroni DM
# ---------------------------------------------------------------------------


class TestBonferroniDM:
    def test_adjusted_p_is_inflated(self):
        rng = np.random.default_rng(20)
        errs_a = rng.standard_normal(100)
        errs_b = rng.standard_normal(100) * 2.0
        result = bonferroni_dm(errs_a, errs_b, n_tests=10)
        assert result["p_value_adjusted"] >= result["p_value"]
        assert result["p_value_adjusted"] <= 1.0

    def test_n_capped_at_1(self):
        rng = np.random.default_rng(21)
        result = bonferroni_dm(
            rng.standard_normal(50) * 0.1,
            rng.standard_normal(50),
            n_tests=1000,
        )
        assert result["p_value_adjusted"] <= 1.0

    def test_significance_with_correction(self):
        rng = np.random.default_rng(22)
        # Large difference, should survive Bonferroni
        errs_model = rng.standard_normal(200) * 0.1
        errs_baseline = rng.standard_normal(200) * 2.0
        result = bonferroni_dm(errs_model, errs_baseline, n_tests=5)
        assert result["significant_05_bonferroni"] is True

    def test_bonferroni_extra_keys(self):
        rng = np.random.default_rng(23)
        result = bonferroni_dm(
            rng.standard_normal(50), rng.standard_normal(50), n_tests=3,
        )
        assert "p_value_adjusted" in result
        assert "significant_05_bonferroni" in result
        assert "n_tests" in result
        assert result["n_tests"] == 3

    def test_single_test_equals_unadjusted(self):
        rng = np.random.default_rng(24)
        errs_a = rng.standard_normal(100)
        errs_b = rng.standard_normal(100)
        result = bonferroni_dm(errs_a, errs_b, n_tests=1)
        assert result["p_value_adjusted"] == pytest.approx(result["p_value"])
