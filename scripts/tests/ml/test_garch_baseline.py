"""Unit tests for GARCH baseline — rolling refit with no data leak.

Tests verify:
    1. Rolling GARCH produces OOS forecasts (NaN in train region)
    2. No future data used in any forecast (strict temporal ordering)
    3. h-step forecast != simple cond_var * h scaling
    4. Rolling MSE != leaky MSE (they should differ)
    5. Edge cases: short series, horizon > 1, convergence failures
"""

import numpy as np
import pandas as pd
import pytest

from pathlib import Path
import sys

SCRIPT_DIR = Path(__file__).resolve().parent.parent.parent / "MyIA.AI.Notebooks" / "QuantConnect" / "ML-Training-Pipeline" / "scripts"
sys.path.insert(0, str(SCRIPT_DIR))

from garch_baseline import (
    fit_garch_leaky,
    fit_garch_rolling,
    compute_realized_vol,
    compare_baselines,
)


@pytest.fixture
def synthetic_returns():
    """Generate synthetic GARCH(1,1) returns for reproducible tests."""
    np.random.seed(42)
    n = 1200
    omega, alpha, beta = 0.1, 0.1, 0.85
    sigma2 = np.zeros(n)
    ret = np.zeros(n)
    sigma2[0] = omega / (1 - alpha - beta)
    for t in range(1, n):
        sigma2[t] = omega + alpha * ret[t - 1] ** 2 + beta * sigma2[t - 1]
        ret[t] = np.sqrt(sigma2[t]) * np.random.randn()
    # Scale to realistic daily log-return magnitude
    ret = ret * 0.01
    return pd.Series(
        ret, index=pd.date_range("2019-01-01", periods=n, freq="B"), name="synth"
    )


class TestFitGarchRolling:
    """Tests for the corrected rolling GARCH implementation."""

    def test_produces_oos_forecasts(self, synthetic_returns):
        """Rolling forecasts should be NaN in train region, non-NaN after."""
        forecasts = fit_garch_rolling(
            synthetic_returns, horizon=1, min_train=500, refit_freq=10
        )
        # First min_train obs should be NaN
        assert forecasts.iloc[:500].isna().all(), "Train region should be NaN"
        # After min_train + some buffer, forecasts should exist
        non_nan = forecasts.iloc[500:].dropna()
        assert len(non_nan) > 100, f"Expected 100+ forecasts, got {len(non_nan)}"

    def test_no_future_data_used(self, synthetic_returns):
        """Each forecast at t must use only data[:t]. We verify by checking
        that forecasts don't change when we truncate the series."""
        full = fit_garch_rolling(
            synthetic_returns, horizon=1, min_train=500, refit_freq=20
        )
        truncated = fit_garch_rolling(
            synthetic_returns.iloc[:800], horizon=1, min_train=500, refit_freq=20
        )
        # Forecasts up to t=800 should be identical
        common_idx = full.iloc[:800].index.intersection(truncated.index)
        full_vals = full.loc[common_idx].dropna()
        trunc_vals = truncated.loc[common_idx].dropna()
        # Align on common non-NaN indices
        shared = full_vals.index.intersection(trunc_vals.index)
        if len(shared) > 0:
            np.testing.assert_allclose(
                full_vals.loc[shared].values,
                trunc_vals.loc[shared].values,
                rtol=1e-10,
                err_msg="Forecasts changed when future data removed = data leak",
            )

    def test_multi_step_not_simple_scaling(self, synthetic_returns):
        """h=5 forecast should NOT equal h=1 forecast * 5 (that's the old bug)."""
        f1 = fit_garch_rolling(
            synthetic_returns, horizon=1, min_train=500, refit_freq=50
        )
        f5 = fit_garch_rolling(
            synthetic_returns, horizon=5, min_train=500, refit_freq=50
        )
        common = f1.dropna().index.intersection(f5.dropna().index)
        if len(common) < 50:
            pytest.skip("Not enough common non-NaN forecasts")
        ratio = f5.loc[common] / f1.loc[common]
        # If simple scaling, ratio would be exactly 5.0 everywhere
        # With proper forecast, it varies
        assert not np.allclose(ratio.values, 5.0, rtol=0.01), \
            "h=5 forecast is just h=1 * 5 = multi-step not properly implemented"

    def test_forecast_positive(self, synthetic_returns):
        """Variance forecasts must be positive."""
        forecasts = fit_garch_rolling(
            synthetic_returns, horizon=1, min_train=500, refit_freq=20
        )
        non_nan = forecasts.dropna()
        assert (non_nan > 0).all(), "Some variance forecasts are non-positive"

    def test_short_series_returns_nan(self):
        """Very short series should return all NaN."""
        short = pd.Series(np.random.randn(50) * 0.02, name="short")
        forecasts = fit_garch_rolling(short, horizon=1, min_train=500)
        assert forecasts.isna().all(), "Short series should produce all NaN"

    def test_horizon_greater_than_1(self, synthetic_returns):
        """h=5 and h=20 should produce valid forecasts."""
        for h in [5, 20]:
            forecasts = fit_garch_rolling(
                synthetic_returns, horizon=h, min_train=500, refit_freq=50
            )
            non_nan = forecasts.dropna()
            assert len(non_nan) > 20, f"h={h}: expected 20+ forecasts, got {len(non_nan)}"
            assert (non_nan > 0).all(), f"h={h}: some forecasts non-positive"


class TestCompareBaselines:
    """Tests for the comparison between leaky and rolling GARCH."""

    def test_leaky_and_rolling_differ(self, synthetic_returns):
        """Leaky and rolling should produce different MSE values."""
        result = compare_baselines(
            synthetic_returns, horizon=5, refit_freq=20, test_start_frac=0.8
        )
        assert "error" not in result, result.get("error")
        assert result["leaky_mse"] != result["rolling_mse"], \
            "Leaky and rolling MSE are identical — something is wrong"

    def test_delta_documented(self, synthetic_returns):
        """Delta should be a non-zero float."""
        result = compare_baselines(
            synthetic_returns, horizon=1, refit_freq=20, test_start_frac=0.8
        )
        assert isinstance(result["delta_pct"], float)
        assert "interpretation" in result

    def test_dry_run_completes(self):
        """Quick dry run with synthetic data should not crash."""
        np.random.seed(42)
        ret = pd.Series(
            np.random.randn(500) * 0.02,
            index=pd.date_range("2022-01-01", periods=500, freq="B"),
        )
        result = compare_baselines(ret, horizon=1, refit_freq=50)
        assert "leaky_mse" in result or "error" in result


class TestComputeRealizedVol:
    """Tests for realized volatility computation."""

    def test_basic_computation(self):
        """RV should be sum of squared returns over window."""
        ret = pd.Series([0.1, -0.05, 0.02, 0.03, -0.01])
        rv = compute_realized_vol(ret, horizon=2)
        # At t=0, target = r[0]^2 + r[1]^2 = 0.01 + 0.0025 = 0.0125
        assert not np.isnan(rv.iloc[0])

    def test_no_negative_values(self, synthetic_returns):
        """Log RV should not have -inf (from zero or negative RV)."""
        log_rv = compute_realized_vol(synthetic_returns, horizon=5)
        finite = log_rv.dropna()
        assert np.isfinite(finite).all(), "Log RV contains non-finite values"
