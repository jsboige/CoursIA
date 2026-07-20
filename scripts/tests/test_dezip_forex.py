#!/usr/bin/env python3
"""
Tests for scripts/datasets/dezip_forex.py

Covers the pure-logic functions that transform FXCM forex archives:
- ``list_contents``: parse an outer zip's namelist and group nested zips by
  resolution (daily / hourly / minute).
- ``extract_inner_csv``: read a zip-within-zip, parse the bid/ask OHLCV CSV,
  and compute mid-price OHLCV + spread.

No network access required: tests build synthetic zip fixtures in memory
(``io.BytesIO``) and on ``tmp_path``. The financial transform (mid-price,
spread) is the highest-value coverage — it pins the OHLCV derivation that
feeds downstream QuantConnect datasets.

LIVE callers: extract_resolution / main (CLI) — I/O orchestration, not pure
logic, out of scope for unit tests.

Run with: pytest scripts/tests/test_dezip_forex.py -v
"""

import io
import sys
import zipfile
from pathlib import Path

import pandas as pd
import pytest

# Add datasets to sys.path
_datasets_dir = str(Path(__file__).resolve().parent.parent / "datasets")
if _datasets_dir not in sys.path:
    sys.path.insert(0, _datasets_dir)

from dezip_forex import list_contents, extract_inner_csv  # noqa: E402


# ─── fixtures ─────────────────────────────────────────────────────────

# 11-column FXCM bid/ask OHLCV row: datetime + 5 bid + 5 ask.
# Datetime format is "%Y%m%d %H:%M" per extract_inner_csv.
_CSV_ROW = "20230102 10:00,1.0600,1.0605,1.0595,1.0602,10,1.0602,1.0607,1.0597,1.0604,8"


def _make_inner_zip_bytes(csv_rows: list[str]) -> bytes:
    """Build a zip in memory containing one 'data.csv' file with the given rows."""
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
        zf.writestr("data.csv", "\n".join(csv_rows))
    return buf.getvalue()


def _make_outer_zip_with_inner(inner_path: str, inner_csv_rows: list[str]) -> zipfile.ZipFile:
    """Build an outer zip holding an inner zip at ``inner_path``; return it opened.

    The caller is responsible for closing the returned ZipFile (or rely on GC).
    """
    outer_buf = io.BytesIO()
    inner_bytes = _make_inner_zip_bytes(inner_csv_rows)
    with zipfile.ZipFile(outer_buf, "w", zipfile.ZIP_DEFLATED) as outer:
        outer.writestr(inner_path, inner_bytes)
    outer_buf.seek(0)
    return zipfile.ZipFile(outer_buf, "r")


# ─── extract_inner_csv ────────────────────────────────────────────────


class TestExtractInnerCsv:
    """extract_inner_csv: zip-within-zip CSV extraction + mid-price transform."""

    def test_mid_price_is_average_of_bid_ask(self):
        """open/high/low/close mid columns == mean of bid and ask columns."""
        zf = _make_outer_zip_with_inner("EURUSD/daily/EURUSD.zip", [_CSV_ROW])
        df = extract_inner_csv(zf, "EURUSD/daily/EURUSD.zip")
        zf.close()

        assert len(df) == 1
        # Mid open = (bid_open 1.0600 + ask_open 1.0602) / 2 = 1.0601
        assert df.loc[0, "open"] == pytest.approx((1.0600 + 1.0602) / 2)
        # Mid close = (1.0602 + 1.0604) / 2 = 1.0603
        assert df.loc[0, "close"] == pytest.approx((1.0602 + 1.0604) / 2)
        assert df.loc[0, "high"] == pytest.approx((1.0605 + 1.0607) / 2)
        assert df.loc[0, "low"] == pytest.approx((1.0595 + 1.0597) / 2)

    def test_spread_is_ask_minus_bid_close(self):
        """spread == ask_close - bid_close."""
        zf = _make_outer_zip_with_inner("GBPUSD/daily/GBPUSD.zip", [_CSV_ROW])
        df = extract_inner_csv(zf, "GBPUSD/daily/GBPUSD.zip")
        zf.close()

        # spread = ask_close 1.0604 - bid_close 1.0602 = 0.0002
        assert df.loc[0, "spread"] == pytest.approx(1.0604 - 1.0602)

    def test_datetime_parsed_to_timestamp(self):
        """The raw 'datetime' column is parsed into a pandas Timestamp and dropped."""
        zf = _make_outer_zip_with_inner("NZDUSD/daily/NZDUSD.zip", [_CSV_ROW])
        df = extract_inner_csv(zf, "NZDUSD/daily/NZDUSD.zip")
        zf.close()

        assert "datetime" not in df.columns
        assert "timestamp" in df.columns
        assert df.loc[0, "timestamp"] == pd.Timestamp("2023-01-02 10:00")

    def test_empty_inner_zip_returns_empty_dataframe(self):
        """An inner zip with NO csv file -> empty DataFrame (logged warning), no crash."""
        # Inner zip containing only a readme.txt, no .csv
        inner_buf = io.BytesIO()
        with zipfile.ZipFile(inner_buf, "w") as z:
            z.writestr("readme.txt", "no data here")
        outer_buf = io.BytesIO()
        with zipfile.ZipFile(outer_buf, "w") as outer:
            outer.writestr("empty/daily/empty.zip", inner_buf.getvalue())
        outer_buf.seek(0)

        zf = zipfile.ZipFile(outer_buf, "r")
        df = extract_inner_csv(zf, "empty/daily/empty.zip")
        zf.close()

        assert df.empty
        assert isinstance(df, pd.DataFrame)

    def test_multiple_rows_preserve_order(self):
        """Multiple CSV rows are parsed in order, each with its own mid-price."""
        rows = [
            "20230102 10:00,1.0000,1.0010,0.9990,1.0005,10,1.0002,1.0012,0.9992,1.0007,8",
            "20230102 11:00,2.0000,2.0010,1.9990,2.0005,10,2.0002,2.0012,1.9992,2.0007,8",
        ]
        zf = _make_outer_zip_with_inner("EURUSD/hour/EURUSD.zip", rows)
        df = extract_inner_csv(zf, "EURUSD/hour/EURUSD.zip")
        zf.close()

        assert len(df) == 2
        assert df.loc[0, "open"] == pytest.approx((1.0000 + 1.0002) / 2)
        assert df.loc[1, "open"] == pytest.approx((2.0000 + 2.0002) / 2)


# ─── list_contents ────────────────────────────────────────────────────


class TestListContents:
    """list_contents: group nested zips in an outer archive by resolution."""

    def _write_outer(self, path: Path, nested_names: list[str]) -> Path:
        """Write an outer zip whose namelist is the given (fake) nested-zip names.

        The nested entries need not be valid zips — list_contents only reads
        the namelist, it does not open the inner archives.
        """
        with zipfile.ZipFile(path, "w") as zf:
            for name in nested_names:
                zf.writestr(name, b"placeholder")
        return path

    def test_groups_by_resolution(self, tmp_path):
        """Daily/hour/minute nested-zip names are routed to the correct bucket.

        Note: ``list_contents`` has a ``len(parts) < 4`` guard — nested-zip
        paths must be at least 4 segments deep (e.g. ``FXCM/EURUSD/daily/EURUSD.zip``);
        shallower paths are silently filtered (see test_shallow_path_filtered).
        """
        zip_path = tmp_path / "forex.zip"
        self._write_outer(zip_path, [
            "FXCM/EURUSD/daily/EURUSD.zip",
            "FXCM/GBPUSD/daily/GBPUSD.zip",
            "FXCM/EURUSD/hour/EURUSD_20230101.zip",
            "FXCM/EURUSD/minute/20230101/EURUSD.zip",
        ])

        result = list_contents(str(zip_path))

        assert len(result["daily"]) == 2
        assert len(result["hourly"]) == 1
        assert len(result["minute"]) == 1
        # daily entries carry the pair name (file stem without .zip)
        pairs = {item["pair"] for item in result["daily"]}
        assert pairs == {"EURUSD", "GBPUSD"}

    def test_empty_zip_returns_empty_buckets(self, tmp_path):
        """An outer zip with no nested .zip entries -> all buckets empty."""
        zip_path = tmp_path / "empty.zip"
        with zipfile.ZipFile(zip_path, "w") as zf:
            zf.writestr("readme.txt", "not a nested zip")

        result = list_contents(str(zip_path))

        assert result == {"daily": [], "hourly": [], "minute": []}

    def test_non_zip_entries_ignored(self, tmp_path):
        """Entries not ending in .zip (csv, txt) are not counted as nested zips."""
        zip_path = tmp_path / "mixed.zip"
        self._write_outer(zip_path, [
            "FXCM/EURUSD/daily/EURUSD.zip",
            "FXCM/EURUSD/daily/EURUSD.csv",  # not a nested zip -> ignored
            "notes.txt",
        ])

        result = list_contents(str(zip_path))

        assert len(result["daily"]) == 1

    def test_shallow_path_filtered(self, tmp_path):
        """A nested-zip path with fewer than 4 segments is silently filtered.

        ``list_contents`` splits the name on '/' and skips entries with
        ``len(parts) < 4``. A 3-segment path like ``EURUSD/daily/EURUSD.zip``
        is therefore NOT counted in any bucket — the contract requires paths
        deep enough to encode source/pair/resolution/file.
        """
        zip_path = tmp_path / "shallow.zip"
        self._write_outer(zip_path, [
            "EURUSD/daily/EURUSD.zip",  # only 3 parts -> filtered by the guard
        ])

        result = list_contents(str(zip_path))

        assert result == {"daily": [], "hourly": [], "minute": []}


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
