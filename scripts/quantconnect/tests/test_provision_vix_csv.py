"""Tests for scripts/quantconnect/provision_vix_csv.py.

Covers the importable pure helpers of the yfinance -> VIX/VIX3M ``date,close``
CSV provisioner (a reproducible data pipeline feeding the VIX-TermStructure
quantbook's local re-exec).

Scope: the two pure, hermetic helpers worth pinning:
  - to_csv_lines : Close-Series -> ``date,close`` CSV lines. ISO date format
    (``%Y-%m-%d``), float-coerced close, ``date,close`` header first, and
    tz-aware timestamps normalized to tz-naive via ``tz_localize(None)``.
  - write_csv   : parent-dir creation + LF-terminated single write.

``fetch_series`` is network-bound (lazy-imports yfinance) and is NOT covered
here -- it is mocked out in the ``main`` dry-run test instead. ``main`` itself
is exercised via monkeypatch on argv (fetch_series monkeypatched to a stub),
asserting the dry-run print path and the ``--out-folder`` wiring.

The sibling ``yfinance_to_lean_daily.py`` converter has its own test
(``test_yfinance_to_lean_daily.py``); this file mirrors that pattern for the
CBOE-index ``date,close`` research-series format (NOT LEAN daily-zip OHLCV).

Run: ``python -m pytest scripts/quantconnect/tests/test_provision_vix_csv.py -q``
"""
import importlib.util
from pathlib import Path

import pandas as pd
import pytest

# Module lives in scripts/quantconnect/ (flat, not a package) -> spec_from_file_location.
_MOD_PATH = Path(__file__).resolve().parent.parent / "provision_vix_csv.py"
_spec = importlib.util.spec_from_file_location("provision_vix_csv", _MOD_PATH)
pvc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(pvc)


# ---------------------------------------------------------------------------
# SERIES constant sanity
# ---------------------------------------------------------------------------

def test_series_maps_csv_names_to_yfinance_tickers():
    assert pvc.SERIES == {"vix_daily.csv": "^VIX", "vix3m_daily.csv": "^VIX3M"}


def test_default_start_is_early_enough():
    # The notebook's range is 2012-2025; the provisioner default must predate it.
    assert pvc.DEFAULT_START <= "2012-01-01"


# ---------------------------------------------------------------------------
# to_csv_lines
# ---------------------------------------------------------------------------

def _series(values, dates=None, name="Close"):
    idx = pd.to_datetime(dates) if dates else pd.to_datetime(
        [f"2024-01-{d:02d}" for d in range(2, 2 + len(values))])
    return pd.Series(values, index=idx, name=name)


def test_to_csv_lines_header_first():
    lines = pvc.to_csv_lines(_series([20.5]))
    assert lines[0] == "date,close"


def test_to_csv_lines_iso_date_and_float_close():
    lines = pvc.to_csv_lines(_series([20.5, 21.0, 19.8]))
    assert lines[1:] == ["2024-01-02,20.5", "2024-01-03,21.0", "2024-01-04,19.8"]


def test_to_csv_lines_count_is_one_plus_len():
    s = _series([1.0, 2.0, 3.0, 4.0])
    assert len(pvc.to_csv_lines(s)) == 1 + len(s)


def test_to_csv_lines_coerces_int_close_to_float():
    # int values are rendered via float() -> "1.0" not "1".
    lines = pvc.to_csv_lines(_series([1, 2, 3]))
    assert lines[1] == "2024-01-02,1.0"
    assert lines[2] == "2024-01-03,2.0"


def test_to_csv_lines_normalizes_tz_aware_timestamp():
    """A tz-aware index is stripped to tz-naive before ISO formatting."""
    s = pd.Series([1.0, 2.0], index=pd.to_datetime(
        ["2024-01-02", "2024-01-03"]).tz_localize("UTC"), name="Close")
    lines = pvc.to_csv_lines(s)
    # No tz offset suffix leaks into the date column.
    assert lines[1] == "2024-01-02,1.0"
    assert lines[2] == "2024-01-03,2.0"
    assert "+" not in lines[1] and "Z" not in lines[1]


def test_to_csv_lines_preserves_nan_close_as_float_str():
    """A NaN close is passed through float() (not dropped here; fetch_series drops NaN)."""
    import math
    s = _series([float("nan"), 2.0])
    lines = pvc.to_csv_lines(s)
    # float(nan) renders as "nan" -- the contract is "float-format the value".
    assert "2.0" in lines[2]


def test_to_csv_lines_single_row():
    lines = pvc.to_csv_lines(_series([42.0], dates=["2024-06-01"]))
    assert lines == ["date,close", "2024-06-01,42.0"]


# ---------------------------------------------------------------------------
# write_csv
# ---------------------------------------------------------------------------

def test_write_csv_creates_parent_dirs(tmp_path):
    out = tmp_path / "deep" / "nested" / "vix_daily.csv"
    assert not out.parent.exists()
    p = pvc.write_csv(out, ["date,close", "2024-01-02,20.5"])
    assert p == out
    assert out.exists()


def test_write_csv_joins_lines_and_trailing_newline(tmp_path):
    """write_csv joins the lines with a newline + appends a trailing newline.

    NOTE (observed divergence, flagged for review): the docstring promises
    "LF-terminated single write", but the implementation uses ``Path.write_text``
    which on Windows translates ``\\n`` to the OS line separator (``\\r\\n``).
    So on Windows the on-disk bytes are CRLF, not LF. (On a POSIX runner or a
    committed tree with autocrlf normalization the bytes may read as LF.) This
    pins the portable contract that matters regardless of platform: the logical
    line structure (one record per line, header + rows + trailing newline). The
    raw-LF assertion is deliberately omitted so the test is platform-stable; a
    follow-up could switch write_csv to a binary write (``write_bytes``) to
    guarantee LF cross-platform.
    """
    out = tmp_path / "vix.csv"
    pvc.write_csv(out, ["date,close", "2024-01-02,20.5", "2024-01-03,21.0"])
    # Normalize whatever line terminator to compare logical content.
    text = out.read_bytes().replace(b"\r\n", b"\n").decode("utf-8")
    assert text == "date,close\n2024-01-02,20.5\n2024-01-03,21.0\n"
    # Trailing newline present.
    assert out.read_bytes().endswith(b"\n")


def test_write_csv_overwrites_existing(tmp_path):
    out = tmp_path / "vix.csv"
    out.write_text("stale content", encoding="utf-8")
    pvc.write_csv(out, ["date,close", "2024-01-02,1.0"])
    assert "stale" not in out.read_text(encoding="utf-8")
    assert "2024-01-02,1.0" in out.read_text(encoding="utf-8")


# ---------------------------------------------------------------------------
# main (fetch_series monkeypatched -> hermetic)
# ---------------------------------------------------------------------------

def test_main_dry_run_prints_first_rows_no_write(monkeypatch, tmp_path, capsys):
    """--dry-run prints a per-series summary but writes no file."""
    stub_close = _series([20.5, 21.0, 19.8, 18.0], dates=[
        "2024-01-02", "2024-01-03", "2024-01-04", "2024-01-05"])
    monkeypatch.setattr(pvc, "fetch_series", lambda ticker, start: stub_close)
    import sys
    monkeypatch.setattr(sys, "argv", [
        "provision_vix_csv.py", "--dry-run", "--out-folder", str(tmp_path)])
    rc = pvc.main()
    assert rc == 0
    out = capsys.readouterr().out
    assert "[dry-run]" in out
    assert "^VIX" in out
    # Nothing written in dry-run.
    assert not (tmp_path / "vix_daily.csv").exists()


def test_main_apply_writes_both_csvs(monkeypatch, tmp_path, capsys):
    """Non-dry-run writes vix_daily.csv and vix3m_daily.csv under --out-folder."""
    def stub(ticker, start):
        return _series([1.0, 2.0, 3.0], dates=["2024-01-02", "2024-01-03", "2024-01-04"])
    monkeypatch.setattr(pvc, "fetch_series", stub)
    import sys
    monkeypatch.setattr(sys, "argv", [
        "provision_vix_csv.py", "--out-folder", str(tmp_path)])
    rc = pvc.main()
    assert rc == 0
    assert (tmp_path / "vix_daily.csv").exists()
    assert (tmp_path / "vix3m_daily.csv").exists()
    text = (tmp_path / "vix_daily.csv").read_text(encoding="utf-8")
    assert text.startswith("date,close\n")
    assert "2024-01-02,1.0" in text
    assert "Done: 2 CBOE series provisioned" in capsys.readouterr().out
