"""Tests for realized_variance.py — RV / BV / r²-daily aggregations.

Covers Issue #834 M2 unit-test commitment:
- RV from intraday returns produces sane values
- HAR lag features have the correct Corsi (2009) structure
- Edge cases: empty series, partial days, single-day series
"""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from intraday_loader import synthesize_intraday, hourly_log_returns
from realized_variance import (
    daily_bipower_variation,
    daily_realized_variance,
    daily_realized_volatility,
    daily_squared_returns,
    har_lag_features,
    realized_variance_to_log,
)


@pytest.fixture
def synth_returns() -> pd.Series:
    ds = synthesize_intraday(n_days=60, obs_per_day=24, seed=7, annualized_vol=0.6)
    return hourly_log_returns(ds)


class TestDailyRealizedVariance:
    def test_n_days_matches_input(self, synth_returns):
        rv = daily_realized_variance(synth_returns)
        assert 55 <= len(rv) <= 60

    def test_rv_is_strictly_positive(self, synth_returns):
        rv = daily_realized_variance(synth_returns)
        assert (rv > 0).all()

    def test_rv_index_is_normalized_dates(self, synth_returns):
        rv = daily_realized_variance(synth_returns)
        assert isinstance(rv.index, pd.DatetimeIndex)
        assert (rv.index.normalize() == rv.index).all()
        assert rv.index.is_monotonic_increasing

    def test_rv_drops_partial_days(self):
        idx = pd.date_range("2020-01-01", periods=4, freq="h")
        rets = pd.Series([0.01, -0.01, 0.005, -0.005], index=idx)
        rv = daily_realized_variance(rets, min_obs_per_day=6)
        assert len(rv) == 0

    def test_rv_matches_manual_for_one_full_day(self):
        idx = pd.date_range("2020-01-01", periods=24, freq="h")
        rng = np.random.default_rng(0)
        rets = pd.Series(rng.normal(0, 0.01, 24), index=idx)
        rv = daily_realized_variance(rets, min_obs_per_day=6)
        assert len(rv) == 1
        assert rv.iloc[0] == pytest.approx((rets ** 2).sum())

    def test_requires_datetime_index(self):
        bad = pd.Series([0.1, 0.2, 0.3], index=[0, 1, 2])
        with pytest.raises(TypeError):
            daily_realized_variance(bad)


class TestRealizedVolatility:
    def test_rvol_is_sqrt_of_rv(self, synth_returns):
        rv = daily_realized_variance(synth_returns)
        rvol = daily_realized_volatility(synth_returns)
        np.testing.assert_allclose(rvol.values, np.sqrt(rv.values), rtol=1e-12)


class TestBipowerVariation:
    def test_bv_close_to_rv_for_continuous_path(self, synth_returns):
        rv = daily_realized_variance(synth_returns)
        bv = daily_bipower_variation(synth_returns)
        common = rv.index.intersection(bv.index)
        ratio = (bv.loc[common] / rv.loc[common]).median()
        assert 0.5 < ratio < 2.0

    def test_bv_drops_jump_contribution(self):
        idx = pd.date_range("2020-01-01", periods=24, freq="h")
        rets = np.zeros(24)
        rets[5] = 0.10
        rets_series = pd.Series(rets, index=idx)
        rv = daily_realized_variance(rets_series, min_obs_per_day=6)
        bv = daily_bipower_variation(rets_series, min_obs_per_day=6)
        assert bv.iloc[0] < rv.iloc[0]


class TestSquaredReturnsBaseline:
    def test_squared_returns_are_noisier_than_rv(self, synth_returns):
        # r²_daily = (Σ r_h)² and RV = Σ r_h². For zero-mean returns,
        # E[r²_daily] ≈ RV but Var(r²_daily) >> Var(RV) — RV is a much
        # smoother proxy of true integrated variance. This is the whole
        # point of using RV instead of r²_daily as the target.
        rv = daily_realized_variance(synth_returns)
        r2d = daily_squared_returns(synth_returns)
        common = rv.index.intersection(r2d.index)
        assert r2d.loc[common].std() > rv.loc[common].std() * 1.5

    def test_returns_are_aggregated_then_squared(self):
        idx = pd.date_range("2020-01-01", periods=24, freq="h")
        rets = pd.Series([0.01] * 24, index=idx)
        rv = daily_realized_variance(rets, min_obs_per_day=6)
        r2d = daily_squared_returns(rets, min_obs_per_day=6)
        assert rv.iloc[0] == pytest.approx(24 * 0.01 ** 2)
        assert r2d.iloc[0] == pytest.approx((24 * 0.01) ** 2)
        assert r2d.iloc[0] > rv.iloc[0]


class TestHarLagFeatures:
    def test_columns_are_corsi_three_horizons(self, synth_returns):
        rv = daily_realized_variance(synth_returns)
        feats = har_lag_features(rv)
        assert list(feats.columns) == ["rv_d", "rv_w", "rv_m"]

    def test_first_22_rows_have_nan_for_monthly(self, synth_returns):
        rv = daily_realized_variance(synth_returns)
        feats = har_lag_features(rv)
        assert feats["rv_m"].iloc[:22].isna().all()
        assert feats["rv_m"].iloc[22:].notna().all()

    def test_rv_w_is_5d_trailing_mean_of_lag1(self):
        rv = pd.Series(
            [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0],
            index=pd.date_range("2020-01-01", periods=10, freq="D"),
        )
        feats = har_lag_features(rv)
        assert feats["rv_d"].iloc[6] == pytest.approx(6.0)
        assert feats["rv_w"].iloc[6] == pytest.approx(np.mean([2.0, 3.0, 4.0, 5.0, 6.0]))

    def test_no_lookahead(self):
        rv = pd.Series(
            np.arange(50, dtype=float) + 1.0,
            index=pd.date_range("2020-01-01", periods=50, freq="D"),
        )
        feats = har_lag_features(rv)
        for t in range(22, 50):
            assert feats["rv_d"].iloc[t] == pytest.approx(rv.iloc[t - 1])
            assert feats["rv_w"].iloc[t] == pytest.approx(rv.iloc[t - 5:t].mean())
            assert feats["rv_m"].iloc[t] == pytest.approx(rv.iloc[t - 22:t].mean())


class TestLogTransform:
    def test_log_handles_zero_floor(self):
        rv = pd.Series([0.0, 1e-15, 1e-6, 1.0])
        log_rv = realized_variance_to_log(rv)
        assert np.isfinite(log_rv).all()
        assert log_rv.iloc[3] == pytest.approx(0.0)
