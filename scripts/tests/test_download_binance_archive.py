#!/usr/bin/env python3
"""
Tests for scripts/datasets/download_binance_archive.py

Covers the three pure-logic helpers used by the public `download` entry point:

    - `_build_url`             : URL composition (spot vs futures) + ValueError on
                                 unknown market
    - `_date_range_monthly`    : YYYY-MM list between two dates (inclusive) +
                                 December-year wrap edge case
    - `_date_range_daily`      : YYYY-MM-DD list between two dates (inclusive)

Pure CPU tests, no network access required.

LIVE callers: this module is imported by QuantConnect dataset builds and the
QC-Cloud notebook family; the URL + date-range layer is the contract that
downstream stitching (`stitch_crypto.py`) and backtest reproducibility depend
on.
"""

import sys
from datetime import datetime
from pathlib import Path

# Add datasets/ to sys.path so `from download_binance_archive import ...` works
# without requiring `pip install -e .`. Mirrors the convention used by
# sibling test files (test_download_yfinance.py, test_dezip_forex.py).
_DATASETS_DIR = str(Path(__file__).resolve().parent.parent / "datasets")
if _DATASETS_DIR not in sys.path:
    sys.path.insert(0, _DATASETS_DIR)

import pytest  # noqa: E402

from download_binance_archive import (  # noqa: E402
    BINANCE_BASE,
    _build_url,
    _date_range_daily,
    _date_range_monthly,
)


# ─────────────────────────────────────────────────────────────────────────
# _build_url: URL composition — must match the public archive layout
# (data.binance.vision) so 404s in live runs become easy to diagnose.
# ─────────────────────────────────────────────────────────────────────────


class TestBuildUrl:
    def test_spot_market(self):
        """Spot market -> /data/spot/<freq>/klines/<symbol>/<interval>/<file>."""
        url = _build_url("BTCUSDT", "spot", "1d", "2023-01", "monthly")
        assert url == (
            f"{BINANCE_BASE}/spot/monthly/klines/BTCUSDT/1d/"
            f"BTCUSDT-1d-2023-01.zip"
        )

    def test_futures_market_usdm(self):
        """Futures -> /data/futures/um/<freq>/klines/<symbol>/<interval>/<file>."""
        url = _build_url("ETHUSDT", "futures", "1h", "2023-06-15", "daily")
        assert url == (
            f"{BINANCE_BASE}/futures/um/daily/klines/ETHUSDT/1h/"
            f"ETHUSDT-1h-2023-06-15.zip"
        )

    def test_filename_uses_dash_separator(self):
        """Filename is <symbol>-<interval>-<date> with dash separator
        (matches Binance archive layout — slashes vs dashes matter here)."""
        url = _build_url("BNBUSDT", "spot", "5m", "2024-03-07", "daily")
        assert url.endswith("/BNBUSDT-5m-2024-03-07.zip")

    def test_unknown_market_raises(self):
        """Unknown market string -> ValueError (caught upstream as misconfig)."""
        with pytest.raises(ValueError, match="Unknown market"):
            _build_url("BTCUSDT", "options", "1d", "2023-01", "monthly")

    def test_preserves_case_of_symbol(self):
        """Symbol case passes through unchanged (caller upper-cases if needed)."""
        url_lower = _build_url("btcusdt", "spot", "1d", "2023-01", "monthly")
        url_upper = _build_url("BTCUSDT", "spot", "1d", "2023-01", "monthly")
        # Both produced URLs should contain the symbol verbatim.
        assert url_lower != url_upper  # case-sensitive paths
        assert "btcusdt" in url_lower
        assert "BTCUSDT" in url_upper


# ─────────────────────────────────────────────────────────────────────────
# _date_range_monthly: inclusive list of YYYY-MM buckets between two
# datetimes, with a December-year wrap edge case the implementation has to
# get right (off-by-one on `current.month == 12` is easy to introduce).
# ─────────────────────────────────────────────────────────────────────────


class TestDateRangeMonthly:
    def test_same_month_one_bucket(self):
        """start and end in the same month -> one YYYY-MM bucket."""
        start = datetime(2023, 5, 1)
        end = datetime(2023, 5, 31)
        dates = _date_range_monthly(start, end)
        assert dates == ["2023-05"]

    def test_consecutive_months(self):
        """Three consecutive months yield three buckets in order."""
        start = datetime(2023, 1, 1)
        end = datetime(2023, 3, 15)
        dates = _date_range_monthly(start, end)
        assert dates == ["2023-01", "2023-02", "2023-03"]

    def test_december_to_january_year_wrap(self):
        """Critical year-wrap edge case: Dec → Jan must bump the year,
        not loop at month=13 (which would crash strftime or skip Jan)."""
        start = datetime(2023, 12, 1)
        end = datetime(2024, 2, 28)
        dates = _date_range_monthly(start, end)
        assert dates == ["2023-12", "2024-01", "2024-02"]

    def test_inclusive_end_of_year(self):
        """End in Dec -> Dec bucket is included."""
        start = datetime(2023, 11, 5)
        end = datetime(2023, 12, 31)
        dates = _date_range_monthly(start, end)
        assert dates == ["2023-11", "2023-12"]

    def test_returns_string_format_yyyy_mm(self):
        """Each bucket is a YYYY-MM string (no day)."""
        start = datetime(2024, 6, 15)
        end = datetime(2024, 6, 20)
        assert _date_range_monthly(start, end) == ["2024-06"]

    def test_start_day_normalized_to_first_of_month(self):
        """start.day is ignored — only start.month / year matter.
        Verifies that 2023-05-31 yields the same list as 2023-05-01."""
        a = _date_range_monthly(datetime(2023, 5, 31), datetime(2023, 7, 1))
        b = _date_range_monthly(datetime(2023, 5, 1), datetime(2023, 7, 1))
        assert a == b == ["2023-05", "2023-06", "2023-07"]


# ─────────────────────────────────────────────────────────────────────────
# _date_range_daily: inclusive list of YYYY-MM-DD strings — drives the
# intra-month resolution for short-interval downloads (1m, 5m, 1h ...).
# ─────────────────────────────────────────────────────────────────────────


class TestDateRangeDaily:
    def test_same_day_one_bucket(self):
        """start == end -> one bucket."""
        d = datetime(2023, 1, 15)
        dates = _date_range_daily(d, d)
        assert dates == ["2023-01-15"]

    def test_consecutive_days(self):
        """Three days -> three buckets in order."""
        start = datetime(2023, 1, 1)
        end = datetime(2023, 1, 3)
        assert _date_range_daily(start, end) == ["2023-01-01", "2023-01-02", "2023-01-03"]

    def test_month_boundary_inclusive(self):
        """Last day of Jan + first day of Feb both included."""
        start = datetime(2023, 1, 31)
        end = datetime(2023, 2, 1)
        assert _date_range_daily(start, end) == ["2023-01-31", "2023-02-01"]

    def test_year_boundary_inclusive(self):
        """Dec 31 + Jan 1 — the year-wrap edge case for the daily path."""
        start = datetime(2023, 12, 31)
        end = datetime(2024, 1, 1)
        assert _date_range_daily(start, end) == ["2023-12-31", "2024-01-01"]

    def test_format_is_iso_yyyy_mm_dd(self):
        """Each bucket is YYYY-MM-DD ISO format (matches Binance naming)."""
        dates = _date_range_daily(datetime(2024, 6, 5), datetime(2024, 6, 7))
        assert all(len(d) == 10 and d[4] == "-" and d[7] == "-" for d in dates)
        assert dates == ["2024-06-05", "2024-06-06", "2024-06-07"]

    def test_long_window_count_matches_timedelta(self):
        """N-day window yields N buckets (sanity check for off-by-one on
        inclusive end). 10 days inclusive -> 10 buckets."""
        start = datetime(2023, 3, 1)
        end = datetime(2023, 3, 10)
        dates = _date_range_daily(start, end)
        assert len(dates) == 10
        assert dates[0] == "2023-03-01"
        assert dates[-1] == "2023-03-10"


# ─────────────────────────────────────────────────────────────────────────
# Integration-shaped tests: pure helpers compose without needing I/O.
# These pin the contract that downstream stitching relies on.
# ─────────────────────────────────────────────────────────────────────────


class TestHelpersCompose:
    def test_monthly_url_for_first_month_in_range(self):
        """End-to-end shape (no network): spot 1d over 2 months
        yields 2 URLs, the first pointing at 2023-01's archive."""
        start = datetime(2023, 1, 1)
        end = datetime(2023, 2, 28)
        date_list = _date_range_monthly(start, end)
        urls = [
            _build_url("BTCUSDT", "spot", "1d", d, "monthly")
            for d in date_list
        ]
        assert len(urls) == 2
        assert "BTCUSDT-1d-2023-01.zip" in urls[0]
        assert "BTCUSDT-1d-2023-02.zip" in urls[1]
        # Both end at /data/spot/monthly/klines/BTCUSDT/1d/
        for url in urls:
            assert url.startswith(f"{BINANCE_BASE}/spot/monthly/klines/BTCUSDT/1d/")

    def test_daily_url_for_first_day_in_range(self):
        """1h intra-day: daily path over 3 days -> 3 URLs, ISO date format."""
        start = datetime(2024, 5, 10)
        end = datetime(2024, 5, 12)
        date_list = _date_range_daily(start, end)
        urls = [
            _build_url("ETHUSDT", "spot", "1h", d, "daily")
            for d in date_list
        ]
        assert urls == [
            f"{BINANCE_BASE}/spot/daily/klines/ETHUSDT/1h/ETHUSDT-1h-2024-05-10.zip",
            f"{BINANCE_BASE}/spot/daily/klines/ETHUSDT/1h/ETHUSDT-1h-2024-05-11.zip",
            f"{BINANCE_BASE}/spot/daily/klines/ETHUSDT/1h/ETHUSDT-1h-2024-05-12.zip",
        ]
