"""Tests for intraday_loader.py — synthetic + dataclass invariants.

Local file loaders (Bitstamp / Binance) are tested via integration in
`train_har_baseline.py` since they require external data on the G: drive.
Here we only test the pure-Python contract.
"""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from intraday_loader import IntradayDataset, hourly_log_returns, synthesize_intraday


class TestIntradayDataset:
    def test_init_rejects_non_datetime_index(self):
        df = pd.DataFrame({"close": [1.0, 2.0]}, index=[0, 1])
        with pytest.raises(TypeError):
            IntradayDataset("X", df, source="synthetic")

    def test_init_rejects_missing_close(self):
        idx = pd.date_range("2020-01-01", periods=2, freq="h")
        df = pd.DataFrame({"open": [1.0, 2.0]}, index=idx)
        with pytest.raises(ValueError):
            IntradayDataset("X", df, source="synthetic")

    def test_init_rejects_duplicate_timestamps(self):
        idx = pd.DatetimeIndex(["2020-01-01 00:00", "2020-01-01 00:00"])
        df = pd.DataFrame({"close": [1.0, 2.0]}, index=idx)
        with pytest.raises(ValueError):
            IntradayDataset("X", df, source="synthetic")

    def test_init_rejects_unsorted_index(self):
        idx = pd.DatetimeIndex(["2020-01-02", "2020-01-01"])
        df = pd.DataFrame({"close": [1.0, 2.0]}, index=idx)
        with pytest.raises(ValueError):
            IntradayDataset("X", df, source="synthetic")


class TestSynthesizeIntraday:
    def test_returns_correct_shape(self):
        ds = synthesize_intraday(n_days=10, obs_per_day=24, seed=0)
        assert len(ds.df) == 10 * 24
        assert ds.symbol == "SYN"
        assert ds.source == "synthetic"

    def test_seed_is_deterministic(self):
        a = synthesize_intraday(n_days=5, seed=42)
        b = synthesize_intraday(n_days=5, seed=42)
        np.testing.assert_array_equal(a.df["close"].values, b.df["close"].values)

    def test_seed_changes_path(self):
        a = synthesize_intraday(n_days=5, seed=0)
        b = synthesize_intraday(n_days=5, seed=1)
        assert not np.allclose(a.df["close"].values, b.df["close"].values)

    def test_close_strictly_positive(self):
        ds = synthesize_intraday(n_days=30, seed=0)
        assert (ds.df["close"] > 0).all()


class TestHourlyLogReturns:
    def test_length_is_n_minus_one(self):
        ds = synthesize_intraday(n_days=10, obs_per_day=24, seed=0)
        rets = hourly_log_returns(ds)
        assert len(rets) == 10 * 24 - 1

    def test_returns_have_zero_mean_approx_for_long_series(self):
        ds = synthesize_intraday(n_days=500, obs_per_day=24, seed=0, annualized_vol=0.6)
        rets = hourly_log_returns(ds)
        assert abs(rets.mean()) < 1e-3

    def test_returns_volatility_matches_annualized_input(self):
        ds = synthesize_intraday(n_days=500, obs_per_day=24, seed=0, annualized_vol=0.6)
        rets = hourly_log_returns(ds)
        ann_vol_observed = rets.std() * np.sqrt(365 * 24)
        assert 0.4 < ann_vol_observed < 0.8
