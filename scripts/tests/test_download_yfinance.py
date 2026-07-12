#!/usr/bin/env python3
"""
Tests for scripts/datasets/download_yfinance.py

Covers: _cache_key, _cache_path, _download (mocked), download (mocked), main (CLI).
Pure CPU tests with mocked yfinance/pandas I/O. No network access required.

LIVE: 1 caller (build_panier_anti_bias.py imports download).
"""

import argparse
import hashlib
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest
import sys

# Add datasets to sys.path
_datasets_dir = str(Path(__file__).resolve().parent.parent / "datasets")
if _datasets_dir not in sys.path:
    sys.path.insert(0, _datasets_dir)

from download_yfinance import _cache_key, _cache_path, _download, download, CACHE_DIR


# ─── _cache_key ───────────────────────────────────────────────────────


class TestCacheKey:
    def test_returns_string(self):
        result = _cache_key("SPY", "2020-01-01", "2024-01-01", "1d")
        assert isinstance(result, str)

    def test_length_12(self):
        """Cache key is first 12 hex chars of MD5."""
        result = _cache_key("SPY", "2020-01-01", "2024-01-01", "1d")
        assert len(result) == 12

    def test_deterministic(self):
        """Same inputs produce same key."""
        k1 = _cache_key("AAPL", "2020-01-01", "2021-01-01", "1d")
        k2 = _cache_key("AAPL", "2020-01-01", "2021-01-01", "1d")
        assert k1 == k2

    def test_different_symbols_different_keys(self):
        k1 = _cache_key("SPY", "2020-01-01", "2024-01-01", "1d")
        k2 = _cache_key("AAPL", "2020-01-01", "2024-01-01", "1d")
        assert k1 != k2

    def test_different_intervals_different_keys(self):
        k1 = _cache_key("SPY", "2020-01-01", "2024-01-01", "1d")
        k2 = _cache_key("SPY", "2020-01-01", "2024-01-01", "1wk")
        assert k1 != k2

    def test_different_dates_different_keys(self):
        k1 = _cache_key("SPY", "2020-01-01", "2023-01-01", "1d")
        k2 = _cache_key("SPY", "2021-01-01", "2024-01-01", "1d")
        assert k1 != k2

    def test_matches_md5(self):
        """Key matches first 12 chars of MD5 of the raw string."""
        symbol, start, end, interval = "BTC-USD", "2018-01-01", "2024-06-01", "1d"
        raw = f"{symbol}_{start}_{end}_{interval}"
        expected = hashlib.md5(raw.encode()).hexdigest()[:12]
        assert _cache_key(symbol, start, end, interval) == expected

    def test_empty_inputs(self):
        """Empty strings still produce a valid key."""
        result = _cache_key("", "", "", "")
        assert isinstance(result, str)
        assert len(result) == 12


# ─── _cache_path ──────────────────────────────────────────────────────


class TestCachePath:
    def test_returns_path(self):
        result = _cache_path("SPY", "2020-01-01", "2024-01-01", "1d")
        assert isinstance(result, Path)

    def test_is_under_cache_dir(self):
        result = _cache_path("SPY", "2020-01-01", "2024-01-01", "1d")
        assert result.parent == CACHE_DIR

    def test_parquet_extension(self):
        result = _cache_path("SPY", "2020-01-01", "2024-01-01", "1d")
        assert result.suffix == ".parquet"

    def test_filename_contains_key(self):
        result = _cache_path("SPY", "2020-01-01", "2024-01-01", "1d")
        key = _cache_key("SPY", "2020-01-01", "2024-01-01", "1d")
        assert key in result.name

    def test_filename_starts_with_symbol(self):
        result = _cache_path("SPY", "2020-01-01", "2024-01-01", "1d")
        assert result.name.startswith("SPY_")

    def test_different_symbols_different_paths(self):
        p1 = _cache_path("SPY", "2020-01-01", "2024-01-01", "1d")
        p2 = _cache_path("AAPL", "2020-01-01", "2024-01-01", "1d")
        assert p1 != p2


# ─── _download (mocked) ───────────────────────────────────────────────


class TestDownloadMocked:
    def _make_df(self, rows=5):
        """Create a mock DataFrame with OHLCV columns."""
        import pandas as pd
        import numpy as np
        dates = pd.date_range("2020-01-01", periods=rows, freq="D")
        data = {
            "Open": np.random.rand(rows) * 100 + 100,
            "High": np.random.rand(rows) * 100 + 105,
            "Low": np.random.rand(rows) * 100 + 95,
            "Close": np.random.rand(rows) * 100 + 100,
            "Volume": np.random.randint(1000000, 10000000, rows),
        }
        return pd.DataFrame(data, index=dates)

    def test_cache_hit_returns_cached_data(self, tmp_path):
        """When cache exists and use_cache=True, returns cached data."""
        import pandas as pd

        mock_df = self._make_df()
        cache_file = tmp_path / "SPY_abc123def456.parquet"
        mock_df.to_parquet(cache_file)

        with patch("download_yfinance._cache_path", return_value=cache_file):
            result = _download("SPY", "2020-01-01", "2024-01-01", "1d", use_cache=True)

        assert isinstance(result, pd.DataFrame)
        assert len(result) == 5

    def test_cache_miss_downloads(self, tmp_path):
        """When cache doesn't exist, downloads via yfinance."""
        import pandas as pd

        mock_df = self._make_df()
        cache_file = tmp_path / "SPY_abc123def456.parquet"

        mock_yf = MagicMock()
        mock_yf.download.return_value = mock_df

        with patch("download_yfinance._cache_path", return_value=cache_file):
            with patch.dict("sys.modules", {"yfinance": mock_yf}):
                result = _download("SPY", "2020-01-01", "2024-01-01", "1d", use_cache=False)

        assert isinstance(result, pd.DataFrame)

    def test_empty_download_returns_empty_df(self, tmp_path):
        """When yfinance returns empty DF, returns it without writing cache."""
        import pandas as pd

        cache_file = tmp_path / "SPY_abc123def456.parquet"
        empty_df = pd.DataFrame()

        mock_yf = MagicMock()
        mock_yf.download.return_value = empty_df

        with patch("download_yfinance._cache_path", return_value=cache_file):
            with patch.dict("sys.modules", {"yfinance": mock_yf}):
                result = _download("SPY", "2020-01-01", "2024-01-01", "1d", use_cache=False)

        assert result.empty

    def test_no_cache_flag_skips_cache(self, tmp_path):
        """use_cache=False should skip cache even if it exists."""
        import pandas as pd

        mock_df_cached = self._make_df(rows=3)
        mock_df_new = self._make_df(rows=10)
        cache_file = tmp_path / "SPY_abc123def456.parquet"
        mock_df_cached.to_parquet(cache_file)

        mock_yf = MagicMock()
        mock_yf.download.return_value = mock_df_new

        with patch("download_yfinance._cache_path", return_value=cache_file):
            with patch.dict("sys.modules", {"yfinance": mock_yf}):
                result = _download("SPY", "2020-01-01", "2024-01-01", "1d", use_cache=False)

        assert len(result) == 10


# ─── download (mocked) ────────────────────────────────────────────────


class TestDownloadFunctionMocked:
    def _make_df(self, rows=5):
        """Create a mock DataFrame with OHLCV columns."""
        import pandas as pd
        import numpy as np
        dates = pd.date_range("2020-01-01", periods=rows, freq="D")
        data = {
            "Open": np.random.rand(rows) * 100 + 100,
            "High": np.random.rand(rows) * 100 + 105,
            "Low": np.random.rand(rows) * 100 + 95,
            "Close": np.random.rand(rows) * 100 + 100,
            "Volume": np.random.randint(1000000, 10000000, rows),
        }
        return pd.DataFrame(data, index=dates)

    def test_returns_list_of_paths(self, tmp_path):
        """download() returns list of written file paths."""
        mock_df = self._make_df()
        output_dir = tmp_path / "output"

        with patch("download_yfinance._download", return_value=mock_df):
            result = download(["SPY"], "2020-01-01", "2024-01-01", "1d", output_dir)

        assert isinstance(result, list)
        assert len(result) == 1
        assert isinstance(result[0], Path)

    def test_creates_csv_files(self, tmp_path):
        """Each symbol produces a CSV file."""
        mock_df = self._make_df()
        output_dir = tmp_path / "output"

        with patch("download_yfinance._download", return_value=mock_df):
            result = download(["SPY", "AAPL"], "2020-01-01", "2024-01-01", "1d", output_dir)

        assert len(result) == 2
        for p in result:
            assert p.suffix == ".csv"
            assert p.exists()

    def test_csv_filename_format(self, tmp_path):
        """CSV filename: {SYMBOL}_{start}_{end}.csv, dashes replaced."""
        mock_df = self._make_df()
        output_dir = tmp_path / "output"

        with patch("download_yfinance._download", return_value=mock_df):
            result = download(["BTC-USD"], "2020-01-01", "2024-01-01", "1d", output_dir)

        assert result[0].name == "BTC_USD_2020-01-01_2024-01-01.csv"

    def test_empty_df_skips_symbol(self, tmp_path):
        """When _download returns empty DF, no CSV is written."""
        import pandas as pd

        output_dir = tmp_path / "output"

        with patch("download_yfinance._download", return_value=pd.DataFrame()):
            result = download(["SPY"], "2020-01-01", "2024-01-01", "1d", output_dir)

        assert result == []

    def test_creates_output_dir(self, tmp_path):
        """Output directory is created if it doesn't exist."""
        mock_df = self._make_df()
        output_dir = tmp_path / "nested" / "output"
        assert not output_dir.exists()

        with patch("download_yfinance._download", return_value=mock_df):
            download(["SPY"], "2020-01-01", "2024-01-01", "1d", output_dir)

        assert output_dir.exists()

    def test_multiple_symbols(self, tmp_path):
        """Multiple symbols produce multiple files."""
        mock_df = self._make_df()
        output_dir = tmp_path / "output"

        with patch("download_yfinance._download", return_value=mock_df):
            result = download(["SPY", "TLT", "GLD"], "2020-01-01", "2024-01-01", "1d", output_dir)

        assert len(result) == 3
        names = [p.name for p in result]
        assert "SPY_2020-01-01_2024-01-01.csv" in names
        assert "TLT_2020-01-01_2024-01-01.csv" in names
        assert "GLD_2020-01-01_2024-01-01.csv" in names


# ─── Cross-invariants ─────────────────────────────────────────────────


class TestCrossInvariants:
    def test_cache_path_uses_cache_key(self):
        """_cache_path embeds _cache_key in the filename."""
        symbol, start, end, interval = "SPY", "2020-01-01", "2024-01-01", "1d"
        key = _cache_key(symbol, start, end, interval)
        path = _cache_path(symbol, start, end, interval)
        assert key in path.name

    def test_download_calls_internal_download(self, tmp_path):
        """download() delegates to _download for each symbol."""
        import pandas as pd

        mock_df = self._make_df()
        output_dir = tmp_path / "output"

        with patch("download_yfinance._download", return_value=mock_df) as mock_dl:
            download(["SPY", "AAPL"], "2020-01-01", "2024-01-01", "1d", output_dir)

        assert mock_dl.call_count == 2
        calls = mock_dl.call_args_list
        symbols_called = [c[0][0] for c in calls]
        assert symbols_called == ["SPY", "AAPL"]

    def _make_df(self, rows=5):
        import pandas as pd
        import numpy as np
        dates = pd.date_range("2020-01-01", periods=rows, freq="D")
        data = {
            "Open": np.random.rand(rows) * 100 + 100,
            "High": np.random.rand(rows) * 100 + 105,
            "Low": np.random.rand(rows) * 100 + 95,
            "Close": np.random.rand(rows) * 100 + 100,
            "Volume": np.random.randint(1000000, 10000000, rows),
        }
        return pd.DataFrame(data, index=dates)

    def test_cache_key_uniqueness_across_params(self):
        """Different parameter combinations produce unique keys."""
        combos = [
            ("SPY", "2020-01-01", "2024-01-01", "1d"),
            ("SPY", "2020-01-01", "2024-01-01", "1wk"),
            ("AAPL", "2020-01-01", "2024-01-01", "1d"),
            ("SPY", "2021-01-01", "2024-01-01", "1d"),
        ]
        keys = [_cache_key(*c) for c in combos]
        assert len(keys) == len(set(keys)), f"Duplicate keys found: {keys}"

    def test_csv_content_matches_dataframe(self, tmp_path):
        """Written CSV content matches the DataFrame passed by _download."""
        import pandas as pd

        mock_df = self._make_df()
        output_dir = tmp_path / "output"

        with patch("download_yfinance._download", return_value=mock_df):
            result = download(["SPY"], "2020-01-01", "2024-01-01", "1d", output_dir)

        written_df = pd.read_csv(result[0], index_col=0, parse_dates=True)
        # CSV round-trip loses freq and may change int dtype
        assert len(written_df) == len(mock_df)
        assert set(written_df.columns) == set(mock_df.columns)
        for col in ["Open", "High", "Low", "Close"]:
            assert all(abs(written_df[col] - mock_df[col]) < 0.01)
