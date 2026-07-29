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
        first, last, count, flat_tail = scan_zip(z)
        assert first == date(2015, 1, 2)
        assert last == date(2025, 12, 31)
        assert count == 2
        assert flat_tail is False  # 2 rows < default 60-bar window; varied closes anyway

    def test_single_row(self, tmp_path):
        z = tmp_path / "foo.zip"
        _write_daily_zip(z, ["20200615 00:00,1,2,0,1,10"])
        first, last, count, flat_tail = scan_zip(z)
        assert first == date(2020, 6, 15)
        assert last == date(2020, 6, 15)
        assert count == 1

    def test_empty_zip(self, tmp_path):
        z = tmp_path / "empty.zip"
        _write_daily_zip(z, [])
        first, last, count, flat_tail = scan_zip(z)
        assert first is None and last is None and count == 0

    def test_bad_zip(self, tmp_path):
        z = tmp_path / "broken.zip"
        z.write_bytes(b"not a zip")
        first, last, count, flat_tail = scan_zip(z)
        assert first is None and last is None and count == 0

    def test_no_csv_member(self, tmp_path):
        z = tmp_path / "notes.zip"
        with zipfile.ZipFile(z, "w") as zf:
            zf.writestr("readme.txt", "hello")
        first, last, count, flat_tail = scan_zip(z)
        assert first is None and last is None and count == 0


# --- flat-tail / forward-fill detection (#8734 litmus, data layer) ---

class TestFlatTail:
    def _row(self, d: str, close: str) -> str:
        return f"{d} 00:00,1,2,0,{close},100"

    def test_forward_filled_tail_detected(self, tmp_path):
        """A zip whose last 60 closes are identical -> flat_tail True (forward-fill)."""
        z = tmp_path / "spy.zip"
        rows = [self._row(f"2015010{n}", f"{200 + n}.0") for n in range(1, 6)]  # 5 varied
        rows += [self._row(f"2021{m:02d}15", "396.33") for m in range(1, 13)]  # 12 constant
        rows += [self._row(f"2022{m:02d}15", "396.33") for m in range(1, 13)]  # 12 constant
        rows += [self._row(f"2023{m:02d}15", "396.33") for m in range(1, 13)]  # 12 constant
        rows += [self._row(f"2024{m:02d}15", "396.33") for m in range(1, 13)]  # 12 constant
        rows += [self._row(f"2025{m:02d}15", "396.33") for m in range(1, 13)]  # 12 constant = 60 const total
        _write_daily_zip(z, rows)
        first, last, count, flat_tail = scan_zip(z, flat_tail_bars=60)
        assert count == 5 + 60
        assert last == date(2025, 12, 15)  # date looks current...
        assert flat_tail is True  # ...but the tail is a forward-filled constant

    def test_varied_tail_not_flagged(self, tmp_path):
        """Realistic varied closes in the tail -> flat_tail False."""
        z = tmp_path / "spy.zip"
        rows = [self._row(f"2025{m:02d}15", f"{300 + m}.5") for m in range(1, 13)] * 5  # 60 varied-ish
        _write_daily_zip(z, rows)
        _, _, _, flat_tail = scan_zip(z, flat_tail_bars=60)
        assert flat_tail is False

    def test_short_zip_not_flagged(self, tmp_path):
        """Fewer rows than the window -> cannot conclude, no false positive."""
        z = tmp_path / "thin.zip"
        _write_daily_zip(z, [self._row("20250101", "1.0"), self._row("20250102", "1.0")])
        _, _, count, flat_tail = scan_zip(z, flat_tail_bars=60)
        assert count == 2
        assert flat_tail is False

    def test_disabled_when_zero(self, tmp_path):
        """flat_tail_bars=0 disables the check."""
        z = tmp_path / "spy.zip"
        _write_daily_zip(z, [self._row(f"2025010{n}", "396.33") for n in range(1, 10)])
        _, _, _, flat_tail = scan_zip(z, flat_tail_bars=0)
        assert flat_tail is False


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

    def test_degenerate_flat_tail_flagged(self, tmp_path, capsys):
        """A ticker with a current date but a constant tail -> DEGENERATE, exit 1.

        This is the #8734 failure mode the date-check misses: the last date
        looks fresh, but Lean forward-fill (or a vendor pad) left a flat tail
        that produces invalid metrics.
        """
        import check_data_freshness as cdf
        ws = tmp_path / "lean-workspace"
        ws.mkdir(parents=True)
        (ws / "lean.json").write_text("{}")
        # 60 constant-close bars, ending this year (date-fresh) -- the flat tail.
        rows = [
            f"2021{m:02d}15 00:00,1,2,0,396.33,0" for m in range(1, 13)
        ] + [
            f"2022{m:02d}15 00:00,1,2,0,396.33,0" for m in range(1, 13)
        ] + [
            f"2023{m:02d}15 00:00,1,2,0,396.33,0" for m in range(1, 13)
        ] + [
            f"2024{m:02d}15 00:00,1,2,0,396.33,0" for m in range(1, 13)
        ] + [
            f"2026{m:02d}15 00:00,1,2,0,396.33,0" for m in range(1, 13)
        ]  # 60 bars, last = 2026-12-15 (fresh), all close 396.33
        _write_daily_zip(ws / "data" / "equity" / "usa" / "daily" / "padded.zip", rows)
        rc = cdf.main([str(ws), "--flat-tail-bars", "60"])
        out = capsys.readouterr().out
        assert "padded" in out and "DEGENERATE" in out
        assert "FLAT TAIL" in out
        assert rc == 1  # degenerate -> gate fails


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
