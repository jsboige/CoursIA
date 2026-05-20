"""Tests for data_sources.py — unified data fetching interface."""

from __future__ import annotations

import os
from pathlib import Path
from unittest.mock import MagicMock, patch

import numpy as np
import pandas as pd
import pytest

from data_sources import (
    DataRequest,
    DataResult,
    fetch_data,
    fetch_multi,
    list_providers,
    register_provider,
    _filter_date_range,
    _load_local_csv,
    _fred_frequency,
)


class TestDataRequest:
    def test_cache_path_deterministic(self):
        req1 = DataRequest(symbol="SPY", start="2020-01-01", end="2024-01-01")
        req2 = DataRequest(symbol="SPY", start="2020-01-01", end="2024-01-01")
        assert req1.cache_path() == req2.cache_path()

    def test_cache_path_differs_for_different_symbol(self):
        req1 = DataRequest(symbol="SPY", start="2020-01-01")
        req2 = DataRequest(symbol="QQQ", start="2020-01-01")
        assert req1.cache_path() != req2.cache_path()

    def test_default_dirs(self):
        req = DataRequest(symbol="SPY")
        assert req.data_dir.name == "yfinance"
        assert req.cache_dir.name == "cache"

    def test_custom_dirs(self, tmp_path):
        req = DataRequest(symbol="SPY", data_dir=tmp_path / "data", cache_dir=tmp_path / "cache")
        assert req.data_dir == tmp_path / "data"
        assert req.cache_dir == tmp_path / "cache"


class TestDataResult:
    def test_n_rows_computed(self):
        df = pd.DataFrame({"Close": [1, 2, 3]})
        result = DataResult(df=df, source_used="csv", from_cache=False, symbol="SPY")
        assert result.n_rows == 3

    def test_empty_df(self):
        df = pd.DataFrame({"Close": []})
        result = DataResult(df=df, source_used="csv", from_cache=False, symbol="SPY")
        assert result.n_rows == 0


class TestFilterDateRange:
    @pytest.fixture
    def sample_df(self):
        dates = pd.date_range("2020-01-01", periods=100, freq="B")
        return pd.DataFrame({"Close": np.random.randn(100)}, index=dates)

    def test_no_filter(self, sample_df):
        result = _filter_date_range(sample_df, None, None)
        assert len(result) == 100

    def test_start_filter(self, sample_df):
        result = _filter_date_range(sample_df, "2020-03-01", None)
        assert len(result) < 100
        assert result.index.min() >= pd.Timestamp("2020-03-01")

    def test_end_filter(self, sample_df):
        result = _filter_date_range(sample_df, None, "2020-02-01")
        assert len(result) < 100
        assert result.index.max() <= pd.Timestamp("2020-02-01")

    def test_both_filters(self, sample_df):
        result = _filter_date_range(sample_df, "2020-02-01", "2020-04-01")
        assert result.index.min() >= pd.Timestamp("2020-02-01")
        assert result.index.max() <= pd.Timestamp("2020-04-01")


class TestLoadLocalCSV:
    def test_load_existing_csv(self, tmp_path):
        dates = pd.date_range("2020-01-01", periods=50, freq="B")
        df = pd.DataFrame(
            {"Close": np.random.randn(50), "Volume": 1000},
            index=dates,
        )
        df.index.name = "Date"
        df.to_csv(tmp_path / "SPY_2020-01-01_2020-03-01.csv")

        req = DataRequest(symbol="SPY", data_dir=tmp_path, cache_dir=tmp_path)
        result = _load_local_csv(req)
        assert result is not None
        assert len(result) == 50

    def test_no_csv_returns_none(self, tmp_path):
        req = DataRequest(symbol="NONEXISTENT", data_dir=tmp_path, cache_dir=tmp_path)
        result = _load_local_csv(req)
        assert result is None

    def test_dash_to_underscore_variant(self, tmp_path):
        dates = pd.date_range("2020-01-01", periods=10, freq="B")
        df = pd.DataFrame({"Close": np.random.randn(10)}, index=dates)
        df.index.name = "Date"
        df.to_csv(tmp_path / "BTC_USD_2020-01-01_2020-01-15.csv")

        req = DataRequest(symbol="BTC-USD", data_dir=tmp_path, cache_dir=tmp_path)
        result = _load_local_csv(req)
        assert result is not None

    def test_date_filtering(self, tmp_path):
        dates = pd.date_range("2020-01-01", periods=100, freq="B")
        df = pd.DataFrame({"Close": np.random.randn(100)}, index=dates)
        df.index.name = "Date"
        df.to_csv(tmp_path / "SPY_2020-01-01_2020-06-01.csv")

        req = DataRequest(
            symbol="SPY", start="2020-03-01", end="2020-04-01",
            data_dir=tmp_path, cache_dir=tmp_path,
        )
        result = _load_local_csv(req)
        assert result is not None
        assert result.index.min() >= pd.Timestamp("2020-03-01")
        assert result.index.max() <= pd.Timestamp("2020-04-01")

    def test_deduplication(self, tmp_path):
        dates = pd.date_range("2020-01-01", periods=10, freq="B")
        df = pd.DataFrame({"Close": range(10)}, index=dates)
        df.index.name = "Date"
        df.to_csv(tmp_path / "SPY_2020_a.csv")
        df.to_csv(tmp_path / "SPY_2020_b.csv")

        req = DataRequest(symbol="SPY", data_dir=tmp_path, cache_dir=tmp_path)
        result = _load_local_csv(req)
        assert result is not None
        assert len(result) == 10  # deduplicated


class TestFredFrequency:
    def test_daily(self):
        assert _fred_frequency("1d") == "d"

    def test_weekly(self):
        assert _fred_frequency("1wk") == "w"

    def test_monthly(self):
        assert _fred_frequency("1mo") == "m"

    def test_quarterly(self):
        assert _fred_frequency("3mo") == "q"

    def test_annual(self):
        assert _fred_frequency("1y") == "a"

    def test_unknown_defaults_daily(self):
        assert _fred_frequency("5m") == "d"


class TestFetchDataFromCSV:
    def test_fetch_from_local_csv(self, tmp_path):
        dates = pd.date_range("2020-01-01", periods=50, freq="B")
        df = pd.DataFrame(
            {"Close": np.random.randn(50), "Volume": 1000},
            index=dates,
        )
        df.index.name = "Date"
        df.to_csv(tmp_path / "SPY_2020-01-01_2020-03-01.csv")

        result = fetch_data("SPY", data_dir=tmp_path, cache_dir=tmp_path, use_cache=False)
        assert len(result) == 50


class TestFetchDataCache:
    def test_cache_round_trip(self, tmp_path):
        dates = pd.date_range("2020-01-01", periods=50, freq="B")
        df = pd.DataFrame({"Close": np.random.randn(50)}, index=dates)
        df.index.name = "Date"
        df.to_csv(tmp_path / "SPY_2020-01-01_2020-03-01.csv")

        # First fetch: reads CSV, writes cache
        result1 = fetch_data("SPY", data_dir=tmp_path, cache_dir=tmp_path / "cache", use_cache=True)
        assert len(result1) == 50

        # Second fetch: reads from cache (no CSV needed)
        result2 = fetch_data("SPY", data_dir=tmp_path / "nonexistent", cache_dir=tmp_path / "cache", use_cache=True)
        assert len(result2) == 50


class TestFetchMulti:
    def test_multiple_symbols(self, tmp_path):
        for symbol in ["SPY", "QQQ"]:
            dates = pd.date_range("2020-01-01", periods=20, freq="B")
            df = pd.DataFrame({"Close": np.random.randn(20)}, index=dates)
            df.index.name = "Date"
            df.to_csv(tmp_path / f"{symbol}_2020-01-01_2020-02-01.csv")

        results = fetch_multi(["SPY", "QQQ", "MISSING"], data_dir=tmp_path, cache_dir=tmp_path)
        assert "SPY" in results
        assert "QQQ" in results
        assert "MISSING" not in results


class TestProviderRegistry:
    def test_default_providers(self):
        providers = list_providers()
        assert "yfinance" in providers
        assert "fred" in providers

    def test_register_custom_provider(self):
        def mock_fetch(req):
            return pd.DataFrame({"Close": [42]}, index=pd.date_range("2020-01-01", periods=1))

        register_provider("mock", mock_fetch)
        assert "mock" in list_providers()

    def test_register_overwrite(self):
        call_count = 0

        def fetch_v1(req):
            nonlocal call_count
            call_count = 1
            return pd.DataFrame()

        def fetch_v2(req):
            nonlocal call_count
            call_count = 2
            return pd.DataFrame()

        register_provider("versioned", fetch_v1)
        register_provider("versioned", fetch_v2)
        assert list_providers().count("versioned") == 1


class TestSourceCSVRaisesWhenMissing:
    def test_source_csv_raises(self, tmp_path):
        with pytest.raises(FileNotFoundError, match="No CSV files found"):
            fetch_data("MISSING", source="csv", data_dir=tmp_path, cache_dir=tmp_path)
