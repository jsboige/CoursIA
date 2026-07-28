"""Tests for check_data_freshness.py — QC local data staleness detection (#8734)."""

import sys
import zipfile
from datetime import date
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_data_freshness import parse_qc_date, scan_zip, find_workspace


# --- parse_qc_date ---

class TestParseQcDate:
    def test_standard_with_time(self):
        assert parse_qc_date("20210331 00:00") == date(2021, 3, 31)

    def test_date_only(self):
        assert parse_qc_date("20180704") == date(2018, 7, 4)

    def test_crypto_quote_filename_not_a_date(self):
        assert parse_qc_date("btcusdt_quote") is None

    def test_garbage(self):
        assert parse_qc_date("not-a-date") is None

    def test_wrong_length(self):
        assert parse_qc_date("2021") is None

    def test_invalid_calendar(self):
        # 8 digits but not a real date.
        assert parse_qc_date("20211301") is None


# --- scan_zip ---

def _write_daily_zip(path: Path, rows: list[str]) -> None:
    """Write a QC-style daily zip (one CSV, no header, 'YYYYMMDD HH:MM,o,h,l,c,v')."""
    path.parent.mkdir(parents=True, exist_ok=True)
    csv = "\n".join(rows).encode("utf-8")
    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as z:
        z.writestr(path.stem + ".csv", csv)


class TestScanZip:
    def test_full_range(self, tmp_path):
        z = tmp_path / "spy.zip"
        _write_daily_zip(z, [
            "20150102 00:00,200.0,201.0,199.0,200.5,1000",
            "20251231 00:00,400.0,401.0,399.0,400.5,2000",
        ])
        first, last, count = scan_zip(z)
        assert first == date(2015, 1, 2)
        assert last == date(2025, 12, 31)
        assert count == 2

    def test_single_row(self, tmp_path):
        z = tmp_path / "foo.zip"
        _write_daily_zip(z, ["20200615 00:00,1,2,0,1,10"])
        first, last, count = scan_zip(z)
        assert first == date(2020, 6, 15)
        assert last == date(2020, 6, 15)
        assert count == 1

    def test_empty_zip(self, tmp_path):
        z = tmp_path / "empty.zip"
        _write_daily_zip(z, [])
        first, last, count = scan_zip(z)
        assert first is None and last is None and count == 0

    def test_bad_zip(self, tmp_path):
        z = tmp_path / "broken.zip"
        z.write_bytes(b"not a zip")
        first, last, count = scan_zip(z)
        assert first is None and last is None and count == 0

    def test_no_csv_member(self, tmp_path):
        z = tmp_path / "notes.zip"
        with zipfile.ZipFile(z, "w") as zf:
            zf.writestr("readme.txt", "hello")
        first, last, count = scan_zip(z)
        assert first is None and last is None and count == 0


# --- end-to-end main() classification (STALE vs FRESH) ---

class TestEndToEnd:
    def _build_workspace(self, tmp_path: Path) -> Path:
        ws = tmp_path / "lean-workspace"
        ws.mkdir(parents=True)
        (ws / "lean.json").write_text("{}")
        # FRESH: ends inside the 6-month window (today).
        _write_daily_zip(ws / "data" / "crypto" / "binance" / "daily" / "btcusdt.zip", [
            "20200101 00:00,1,1,1,1,1",
            f"{date.today():%Y%m%d} 00:00,1,1,1,1,1",
        ])
        # STALE: ends 2021 (equity snapshot).
        _write_daily_zip(ws / "data" / "equity" / "usa" / "daily" / "spy.zip", [
            "20150102 00:00,1,1,1,1,1",
            "20210331 00:00,1,1,1,1,1",
        ])
        return ws

    def test_fresh_and_stale_detected(self, tmp_path, capsys):
        import check_data_freshness as cdf
        ws = self._build_workspace(tmp_path)
        rc = cdf.main([str(ws)])
        out = capsys.readouterr().out
        assert "btcusdt" in out and "FRESH" in out
        assert "spy" in out and "STALE" in out
        assert "1 FRESH, 1 STALE" in out
        assert rc == 1  # stale present -> gate fails

    def test_no_fail_returns_zero(self, tmp_path, capsys):
        import check_data_freshness as cdf
        ws = self._build_workspace(tmp_path)
        rc = cdf.main([str(ws), "--no-fail"])
        assert rc == 0

    def test_min_year_filter(self, tmp_path, capsys):
        import check_data_freshness as cdf
        ws = self._build_workspace(tmp_path)
        # Require data from 2027 on: both tickers stale (btcusdt ends today-2026, spy ends 2021).
        rc = cdf.main([str(ws), "--min-year", "2027"])
        out = capsys.readouterr().out
        assert "2 STALE" in out
        assert rc == 1


# --- find_workspace ---

class TestFindWorkspace:
    def test_finds_ancestor(self, tmp_path):
        ws = tmp_path / "ws"
        ws.mkdir(parents=True)
        (ws / "lean.json").write_text("{}")
        (ws / "data").mkdir()
        deep = ws / "projects" / "DL-LSTM-Researcher"
        deep.mkdir(parents=True)
        assert find_workspace(deep) == ws.resolve()

    def test_none_when_absent(self, tmp_path):
        assert find_workspace(tmp_path) is None
