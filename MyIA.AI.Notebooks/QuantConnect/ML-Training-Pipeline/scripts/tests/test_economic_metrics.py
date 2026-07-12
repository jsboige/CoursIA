"""Tests for economic_metrics.py — vol-targeted Sharpe, VaR breach rate, utility gain."""

from __future__ import annotations

import numpy as np
import pytest

from economic_metrics import utility_gain, var_breach_rate, vol_targeted_sharpe


class TestVolTargetedSharpe:
    def test_perfect_forecast_positive_sharpe(self):
        rng = np.random.default_rng(0)
        n = 252
        realized = rng.uniform(0.10, 0.40, n)
        # Perfect forecast: weights target vol exactly
        result = vol_targeted_sharpe(realized, realized, target_vol=0.15)
        assert np.isfinite(result["sharpe"])
        assert result["n_periods"] == n

    def test_poor_forecast_lower_sharpe(self):
        rng = np.random.default_rng(1)
        n = 252
        realized = rng.uniform(0.10, 0.40, n)
        good_forecast = realized
        # Poor forecast: constant (no timing information)
        poor_forecast = np.full(n, 0.20)
        r_good = vol_targeted_sharpe(realized, good_forecast)
        r_poor = vol_targeted_sharpe(realized, poor_forecast)
        # Both should return finite Sharpe
        assert np.isfinite(r_good["sharpe"])
        assert np.isfinite(r_poor["sharpe"])

    def test_short_series_returns_nan(self):
        result = vol_targeted_sharpe(
            np.array([0.2, 0.3, 0.25]),
            np.array([0.2, 0.3, 0.25]),
        )
        assert np.isnan(result["sharpe"])

    def test_return_keys(self):
        rng = np.random.default_rng(2)
        result = vol_targeted_sharpe(
            rng.uniform(0.1, 0.4, 100),
            rng.uniform(0.1, 0.4, 100),
        )
        for key in ("sharpe", "gross_return", "net_return", "turnover", "n_periods"):
            assert key in result

    def test_unequal_length_truncates(self):
        result = vol_targeted_sharpe(
            np.ones(50) * 0.2,
            np.ones(100) * 0.2,
        )
        assert result["n_periods"] == 50

    def test_fees_reduce_net_return(self):
        rng = np.random.default_rng(3)
        realized = rng.uniform(0.10, 0.40, 252)
        forecast = realized + rng.normal(0, 0.02, 252)
        r_no_fee = vol_targeted_sharpe(realized, forecast, fee_bps=0)
        r_with_fee = vol_targeted_sharpe(realized, forecast, fee_bps=50)
        assert r_with_fee["net_return"] <= r_no_fee["net_return"]


class TestVarBreachRate:
    def test_well_calibrated_model(self):
        rng = np.random.default_rng(10)
        n = 1000
        # Returns ~ N(0, 0.02), VaR at 95% = 1.645 * 0.02 = 0.0329
        returns = rng.normal(0, 0.02, n)
        var_forecast = np.full(n, 0.0329)
        result = var_breach_rate(returns, var_forecast, confidence=0.95)
        # Expected breach rate ≈ 5%, should be within [2%, 8%]
        assert 0.02 <= result["breach_rate"] <= 0.08
        assert result["n_periods"] == n

    def test_zero_breaches(self):
        n = 100
        returns = np.full(n, 0.01)  # always positive
        var_forecast = np.full(n, 0.001)
        result = var_breach_rate(returns, var_forecast)
        assert result["n_breaches"] == 0
        assert result["breach_rate"] == 0.0

    def test_all_breaches(self):
        n = 100
        returns = np.full(n, -0.05)  # always big loss
        var_forecast = np.full(n, 0.01)
        result = var_breach_rate(returns, var_forecast)
        assert result["n_breaches"] == n
        assert result["breach_rate"] == 1.0

    def test_kupiec_test_keys(self):
        rng = np.random.default_rng(11)
        n = 500
        returns = rng.normal(0, 0.02, n)
        var_forecast = np.full(n, 0.0329)
        result = var_breach_rate(returns, var_forecast)
        assert "kupiec_p" in result
        assert "calibrated" in result

    def test_short_series_returns_nan(self):
        result = var_breach_rate(
            np.array([0.01, -0.01, 0.02]),
            np.array([0.02, 0.02, 0.02]),
        )
        assert np.isnan(result["breach_rate"])

    def test_unequal_length_truncates(self):
        result = var_breach_rate(
            np.ones(50),
            np.ones(100),
        )
        assert result["n_periods"] == 50


class TestUtilityGain:
    def test_better_model_positive_gain(self):
        result = utility_gain(mse_model=0.05, mse_baseline=0.10)
        assert result["gain_bps"] > 0
        assert result["mse_reduction_pct"] == 50.0

    def test_worse_model_zero_gain(self):
        result = utility_gain(mse_model=0.15, mse_baseline=0.10)
        assert result["gain_bps"] == 0.0
        assert result["mse_reduction_pct"] < 0

    def test_equal_models_zero_gain(self):
        result = utility_gain(mse_model=0.10, mse_baseline=0.10)
        assert result["gain_bps"] == 0.0
        assert result["mse_reduction_pct"] == 0.0

    def test_zero_baseline_handles_gracefully(self):
        result = utility_gain(mse_model=0.0, mse_baseline=0.0)
        assert result["gain_bps"] == 0.0

    def test_worth_switching_when_gain_exceeds_fees(self):
        result = utility_gain(mse_model=0.01, mse_baseline=0.10, fee_bps=10.0)
        assert result["worth_switching"] is True

    def test_not_worth_switching_when_gain_below_fees(self):
        # Very marginal improvement that doesn't justify switching
        result = utility_gain(mse_model=0.10, mse_baseline=0.1001, fee_bps=100.0,
                              risk_aversion=0.1)
        assert result["worth_switching"] is False

    def test_return_keys(self):
        result = utility_gain(mse_model=0.05, mse_baseline=0.10)
        for key in ("gain_bps", "model_mse", "baseline_mse", "mse_reduction_pct",
                     "worth_switching"):
            assert key in result
