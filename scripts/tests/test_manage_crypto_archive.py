"""Tests for scripts/datasets/manage_crypto_archive.py

Covers: update_archive mixed-date-type handling.

Regression test: pd.read_csv yields string dates from the existing archive while
_download_binance_historical yields datetime.date objects, so a naive concat produced a
mixed-type "date" column that raised
"TypeError: '<' not supported between instances of 'datetime.date' and 'str'" in sort_values.
The fix normalizes the column with pd.to_datetime(...).dt.date before dedup/sort.

Pure computation on CPU. The network download is monkeypatched (no yfinance/network needed).
"""

import sys
from datetime import date
from pathlib import Path

import pandas as pd
import pytest

# Add scripts/datasets to sys.path so we can import the module by file.
_datasets = str(Path(__file__).resolve().parent.parent / "datasets")
if _datasets not in sys.path:
    sys.path.insert(0, _datasets)

import importlib.util

_spec = importlib.util.spec_from_file_location(
    "manage_crypto_archive", Path(_datasets) / "manage_crypto_archive.py"
)
mca = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(mca)


def _mock_new_rows():
    """Mimic _download_binance_historical output: date column as datetime.date objects."""
    return pd.DataFrame(
        {
            "date": [date(2024, 12, 30), date(2024, 12, 31), date(2025, 1, 1)],
            "open": [94800, 95100, 95300],
            "high": [95500, 95800, 96000],
            "low": [94000, 94500, 94700],
            "close": [95200, 95300, 95700],
            "volume": [1.2e9, 1.0e9, 1.1e9],
        }
    )


def _write_old_archive(path: Path):
    """Mimic an existing archive as read back by pd.read_csv: string dates."""
    pd.DataFrame(
        {
            "date": ["2024-12-28", "2024-12-29", "2024-12-30"],
            "open": [95000, 95500, 94800],
            "high": [96000, 96500, 95500],
            "low": [94500, 95000, 94000],
            "close": [95500, 94800, 95200],
            "volume": [1.0e9, 1.1e9, 1.2e9],
        }
    ).to_csv(path, index=False)


class TestUpdateArchiveMixedDateTypes:
    """update_archive must merge CSV-read string dates with downloaded date objects."""

    def test_update_succeeds_with_mixed_types(self, monkeypatch, tmp_path):
        monkeypatch.setattr(mca, "_download_binance_historical",
                            lambda symbol, start, end: _mock_new_rows())
        archive = tmp_path / "BTC_USDT_archive.csv"
        _write_old_archive(archive)

        # Before the fix this raised TypeError in sort_values.
        result = mca.update_archive("BTC", tmp_path)
        assert result == archive

        df = pd.read_csv(archive)
        # 3 old + 3 new - 1 overlap (2024-12-30)
        assert len(df) == 5

    def test_update_dedups_overlap_and_sorts(self, monkeypatch, tmp_path):
        monkeypatch.setattr(mca, "_download_binance_historical",
                            lambda symbol, start, end: _mock_new_rows())
        archive = tmp_path / "BTC_USDT_archive.csv"
        _write_old_archive(archive)

        mca.update_archive("BTC", tmp_path)
        df = pd.read_csv(archive)

        dates = pd.to_datetime(df["date"]).tolist()
        assert dates == sorted(dates), "dates must be sorted ascending"
        assert (df["date"].astype(str) == "2024-12-30").sum() == 1, "overlap must be deduped"

    def test_update_no_new_data(self, monkeypatch, tmp_path):
        monkeypatch.setattr(mca, "_download_binance_historical",
                            lambda symbol, start, end: pd.DataFrame())
        archive = tmp_path / "BTC_USDT_archive.csv"
        _write_old_archive(archive)

        assert mca.update_archive("BTC", tmp_path) is None

    def test_update_missing_archive(self, tmp_path):
        # No existing CSV -> graceful None, no exception.
        assert mca.update_archive("BTC", tmp_path) is None
