#!/usr/bin/env python3
"""Pytest suite for `QuantConnect/shared/data_cache.py`.

Co-located with the module under `shared/`. CPU-only, no network, no real
yfinance download. The module imports stdlib + pandas + yfinance at top level;
yfinance is not installed on this worker, so a fake `yfinance` module is injected
into `sys.modules` BEFORE the module is loaded via importlib. The fake's
`download` returns a canned DataFrame so the cache hit/miss/stale-fallback logic
is exercised against real Parquet files written into tmp_path.

The module is the smart-cache helper for yfinance downloads (stores Parquet to
avoid re-downloading across Papermill runs) consumed by the partner-course
quant-trading notebooks and had 0 dedicated Python test coverage before this PR.
"""
from __future__ import annotations

import importlib.util
import sys
import time
from pathlib import Path
from types import ModuleType

import numpy as np
import pandas as pd
import pytest

# --------------------------------------------------------------------------
# Build a fake `yfinance` module and inject it BEFORE loading data_cache.
# --------------------------------------------------------------------------


class _FakeYFinance:
    """Fake yfinance. `download` returns a canned OHLCV DataFrame.

    The canned frame can be configured per-test via `FakeYFinance.response` or
    `FakeYFinance.side_effect` (an exception to raise).
    """

    response: pd.DataFrame | None = None
    side_effect: Exception | None = None

    @staticmethod
    def download(ticker, start=None, end=None, progress=False):
        if _FakeYFinance.side_effect is not None:
            exc = _FakeYFinance.side_effect
            _FakeYFinance.side_effect = None
            raise exc
        if _FakeYFinance.response is not None:
            return _FakeYFinance.response.copy()
        # Default: a small 3-day Close frame.
        idx = pd.date_range("2024-01-01", periods=3, freq="D")
        return pd.DataFrame({"Close": [10.0, 11.0, 12.0]}, index=idx)


@pytest.fixture(autouse=True)
def _reset_yf_fake():
    """Reset the fake yfinance state between tests."""
    _FakeYFinance.response = None
    _FakeYFinance.side_effect = None
    yield
    _FakeYFinance.response = None
    _FakeYFinance.side_effect = None


# Inject fake yfinance into sys.modules, then load data_cache by path.
sys.modules.setdefault("yfinance", _FakeYFinance)
_MODULE_PATH = Path(__file__).resolve().parent / "data_cache.py"
_spec = importlib.util.spec_from_file_location("data_cache_under_test", _MODULE_PATH)
dc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(dc)


# --------------------------------------------------------------------------
# _cache_path — pure filename derivation
# --------------------------------------------------------------------------


def test_cache_path_basic():
    p = dc._cache_path("SPY", "2024-01-01", "2024-12-31", "Close", Path("/tmp/c"))
    assert p.name == "SPY_20240101_20241231_Close.parquet"


def test_cache_path_strips_dashes_from_dates():
    p = dc._cache_path("AAPL", "2020-01-01", "2020-01-02", "Adj Close", Path("/c"))
    assert "20200101" in p.name
    assert "20200102" in p.name
    # Column with a space is kept verbatim (quirk, pinned).
    assert "Adj Close" in p.name


def test_cache_path_sanitizes_caret_and_slash():
    # ^VIX -> IDX_VIX ; ticker with slash -> underscore.
    p1 = dc._cache_path("^VIX", "2024-01-01", "2024-01-02", "Close", Path("/c"))
    assert p1.name.startswith("IDX_VIX_")
    p2 = dc._cache_path("BRK/B", "2024-01-01", "2024-01-02", "Close", Path("/c"))
    assert p2.name.startswith("BRK_B_")


def test_cache_path_under_provided_dir(tmp_path):
    p = dc._cache_path("SPY", "2024-01-01", "2024-01-02", "Close", tmp_path)
    assert p.parent == tmp_path


# --------------------------------------------------------------------------
# _age_days — pure time math (mocked clock)
# --------------------------------------------------------------------------


def test_age_days_zero_for_just_written_file(tmp_path, monkeypatch):
    f = tmp_path / "x.parquet"
    f.write_bytes(b"")
    # Force time.time to return the file's mtime -> age 0.
    mtime = f.stat().st_mtime
    monkeypatch.setattr(dc.time, "time", lambda: mtime)
    assert dc._age_days(f) == pytest.approx(0.0)


def test_age_days_one_day_old(tmp_path, monkeypatch):
    f = tmp_path / "x.parquet"
    f.write_bytes(b"")
    mtime = f.stat().st_mtime
    monkeypatch.setattr(dc.time, "time", lambda: mtime + 86400)
    assert dc._age_days(f) == pytest.approx(1.0)


# --------------------------------------------------------------------------
# get_yf_data — cache hit / miss / stale fallback
# --------------------------------------------------------------------------


def test_get_yf_data_cache_miss_downloads_and_writes_parquet(tmp_path):
    series = dc.get_yf_data("SPY", "2024-01-01", "2024-01-03", "Close",
                            cache_dir=str(tmp_path), verbose=False)
    assert isinstance(series, pd.Series)
    assert len(series) == 3
    # Parquet written under the cache dir.
    expected = tmp_path / "SPY_20240101_20240103_Close.parquet"
    assert expected.exists()


def test_get_yf_data_cache_hit_skips_download(tmp_path, monkeypatch):
    # First call: miss -> download + write.
    dc.get_yf_data("SPY", "2024-01-01", "2024-01-03", "Close",
                   cache_dir=str(tmp_path), verbose=False)
    # Sabotage download: if called again, raise. A cache hit must NOT call it.
    call_count = {"n": 0}

    def _boom(*a, **k):
        call_count["n"] += 1
        raise AssertionError("download must not be called on cache hit")

    monkeypatch.setattr(_FakeYFinance, "download", staticmethod(_boom))
    series = dc.get_yf_data("SPY", "2024-01-01", "2024-01-03", "Close",
                            cache_dir=str(tmp_path), verbose=False)
    assert call_count["n"] == 0
    assert len(series) == 3


def test_get_yf_data_stale_fallback_on_download_failure(tmp_path, monkeypatch):
    # Prime the cache with a real file.
    dc.get_yf_data("SPY", "2024-01-01", "2024-01-03", "Close",
                   cache_dir=str(tmp_path), verbose=False)
    # Now make download raise; the stale cache must be returned, not propagated.
    _FakeYFinance.side_effect = RuntimeError("network down")
    series = dc.get_yf_data("SPY", "2024-01-01", "2024-01-03", "Close",
                            cache_dir=str(tmp_path), verbose=False)
    assert len(series) == 3


def test_get_yf_data_raises_when_download_fails_and_no_cache(tmp_path, monkeypatch):
    _FakeYFinance.side_effect = RuntimeError("network down")
    with pytest.raises(RuntimeError, match="network down"):
        dc.get_yf_data("NOPE", "2024-01-01", "2024-01-03", "Close",
                       cache_dir=str(tmp_path), verbose=False)


def test_get_yf_data_raises_value_error_on_empty_download(tmp_path, monkeypatch):
    _FakeYFinance.response = pd.DataFrame()
    with pytest.raises(ValueError, match="Aucune donnee"):
        dc.get_yf_data("EMPTY", "2024-01-01", "2024-01-03", "Close",
                       cache_dir=str(tmp_path), verbose=False)


def test_get_yf_data_max_age_days_expires_cache(tmp_path, monkeypatch):
    dc.get_yf_data("SPY", "2024-01-01", "2024-01-03", "Close",
                   cache_dir=str(tmp_path), verbose=False)
    cached = tmp_path / "SPY_20240101_20240103_Close.parquet"
    # Push the file mtime 10 days into the past, and freeze the clock at "now".
    old_mtime = cached.stat().st_mtime - 10 * 86400
    import os as _os
    _os.utime(cached, (old_mtime, old_mtime))
    monkeypatch.setattr(dc.time, "time", lambda: old_mtime + 10 * 86400)
    # max_age_days=5 -> cache (10d old) expired -> must re-download.
    download_calls = {"n": 0}
    orig = _FakeYFinance.download.__func__ if hasattr(_FakeYFinance.download, "__func__") else _FakeYFinance.download

    def _counting(*a, **k):
        download_calls["n"] += 1
        return orig(*a, **k)

    monkeypatch.setattr(_FakeYFinance, "download", staticmethod(_counting))
    dc.get_yf_data("SPY", "2024-01-01", "2024-01-03", "Close",
                   cache_dir=str(tmp_path), max_age_days=5, verbose=False)
    assert download_calls["n"] == 1


def test_get_yf_data_creates_cache_dir_if_missing(tmp_path):
    nested = tmp_path / "deep" / "cache"
    assert not nested.exists()
    dc.get_yf_data("SPY", "2024-01-01", "2024-01-03", "Close",
                   cache_dir=str(nested), verbose=False)
    assert nested.exists()


# --------------------------------------------------------------------------
# get_yf_batch — multi-ticker assembly + skip-on-error
# --------------------------------------------------------------------------


def test_get_yf_batch_assembles_columns_per_ticker(tmp_path):
    df = dc.get_yf_batch(["SPY", "QQQ"], "2024-01-01", "2024-01-03",
                         cache_dir=str(tmp_path), verbose=False)
    assert isinstance(df, pd.DataFrame)
    assert set(df.columns) == {"SPY", "QQQ"}
    assert len(df) == 3


def test_get_yf_batch_skips_failing_ticker(tmp_path, monkeypatch):
    # SPY downloads fine; NOPE raises (no cache, empty not forced -> we make
    # download raise for NOPE only).
    def _selective(ticker, start=None, end=None, progress=False):
        if ticker == "NOPE":
            raise RuntimeError("no data")
        idx = pd.date_range("2024-01-01", periods=3, freq="D")
        return pd.DataFrame({"Close": [1.0, 2.0, 3.0]}, index=idx)

    monkeypatch.setattr(_FakeYFinance, "download", staticmethod(_selective))
    df = dc.get_yf_batch(["SPY", "NOPE"], "2024-01-01", "2024-01-03",
                         cache_dir=str(tmp_path), verbose=False)
    # NOPE skipped -> only SPY column.
    assert list(df.columns) == ["SPY"]


def test_get_yf_batch_empty_input_returns_empty_dataframe(tmp_path):
    df = dc.get_yf_batch([], "2024-01-01", "2024-01-03",
                         cache_dir=str(tmp_path), verbose=False)
    assert isinstance(df, pd.DataFrame)
    assert df.empty


# --------------------------------------------------------------------------
# clear_cache
# --------------------------------------------------------------------------


def test_clear_cache_removes_parquets_and_returns_names(tmp_path):
    for name in ("a.parquet", "b.parquet", "notes.txt"):
        (tmp_path / name).write_bytes(b"x")
    removed = dc.clear_cache(cache_dir=str(tmp_path))
    assert sorted(removed) == ["a.parquet", "b.parquet"]
    # Non-parquet file preserved.
    assert (tmp_path / "notes.txt").exists()
    assert not (tmp_path / "a.parquet").exists()


def test_clear_cache_missing_dir_returns_empty(tmp_path):
    missing = tmp_path / "nope"
    assert dc.clear_cache(cache_dir=str(missing)) == []


def test_clear_cache_empty_dir_returns_empty(tmp_path):
    assert dc.clear_cache(cache_dir=str(tmp_path)) == []
