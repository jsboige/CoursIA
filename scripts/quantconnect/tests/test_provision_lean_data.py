"""Offline unit tests for provision_lean_data.py (no network, no yfinance).

Validates manifest parsing, dest resolution, the idempotent skip-when-fresh, and
the cabled freshness gate -- without touching the network. A fake converter
writes small in-memory LEAN daily zips so ``provision_universe`` + ``run_gate``
are exercised end-to-end. The real yfinance path is documented in the module
docstring (and exercised at dev time); it is not invoked here.
"""

import json
import sys
import zipfile
from datetime import date, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from provision_lean_data import (  # noqa: E402
    is_fresh,
    load_manifest,
    provision_universe,
    resolve_dest,
    run_gate,
)

MANIFEST = Path(__file__).resolve().parent.parent / "lean_universes.manifest.json"


def _write_zip(dest: Path, ticker: str, last_iso: str, n_bars: int = 3) -> None:
    """Write a tiny valid LEAN daily zip for ``ticker`` ending at ``last_iso`` (YYYYMMDD)."""
    dest = Path(dest)
    dest.mkdir(parents=True, exist_ok=True)
    y, m, d = int(last_iso[:4]), int(last_iso[4:6]), int(last_iso[6:8])
    lines = []
    for i in range(n_bars):
        dt = date(y, m, d) - timedelta(days=n_bars - 1 - i)
        lines.append(f"{dt:%Y%m%d} 00:00,100000,101000,99000,100500,1000")
    low = ticker.lower()
    with zipfile.ZipFile(dest / f"{low}.zip", "w") as zf:
        zf.writestr(f"{low}.csv", "\n".join(lines) + "\n")


class TestLoadManifest:
    def test_loads_real_manifest(self):
        m = load_manifest(MANIFEST)
        assert m["version"] == 1
        assert "turn_of_month" in m["universes"]
        assert "ema_cross_alpha" in m["universes"]
        assert m["freshness_min_year"] >= 2024

    def test_missing_file_raises(self, tmp_path):
        with pytest.raises(FileNotFoundError):
            load_manifest(tmp_path / "does_not_exist.json")

    def test_universes_have_required_fields(self):
        m = load_manifest(MANIFEST)
        for name, spec in m["universes"].items():
            assert spec["tickers"], f"{name} has no tickers"
            assert "start" in spec, f"{name} missing start"
            assert "regen_date" in spec, f"{name} missing regen_date"

    def test_rejects_bad_version(self, tmp_path):
        bad = tmp_path / "bad.json"
        bad.write_text(json.dumps({"version": 99, "universes": {}}))
        with pytest.raises(ValueError):
            load_manifest(bad)


class TestResolveDest:
    def test_explicit_dest_wins(self, tmp_path):
        assert resolve_dest(tmp_path, None) == tmp_path

    def test_workspace_resolves_daily_subdir(self, tmp_path):
        ws = tmp_path / "ws"
        assert resolve_dest(None, ws) == ws / "data" / "equity" / "usa" / "daily"


class TestIsFresh:
    def test_fresh_zip(self, tmp_path):
        _write_zip(tmp_path, "SPY", "20260101")
        assert is_fresh(tmp_path / "spy.zip", 2024) is True

    def test_stale_zip(self, tmp_path):
        _write_zip(tmp_path, "SPY", "20210101")
        assert is_fresh(tmp_path / "spy.zip", 2024) is False

    def test_missing_zip_not_fresh(self, tmp_path):
        assert is_fresh(tmp_path / "nope.zip", 2024) is False


class TestProvisionUniverse:
    @staticmethod
    def _fake_converter(calls):
        def _conv(ticker, dest, start, end, dry_run=False):
            _write_zip(dest, ticker, "20260101")
            calls.append(ticker)
            return 3
        return _conv

    def test_provisions_missing_tickers(self, tmp_path):
        calls = []
        spec = {"tickers": ["SPY", "QQQ"], "start": "2005-01-01", "end": None}
        results = provision_universe(spec, tmp_path, force=False, min_year=2024,
                                     converter=self._fake_converter(calls))
        assert calls == ["SPY", "QQQ"]
        assert all(r[1] == "provisioned" for r in results)

    def test_skips_when_fresh(self, tmp_path):
        _write_zip(tmp_path, "SPY", "20260101")  # already fresh
        calls = []
        spec = {"tickers": ["SPY"], "start": "2005-01-01", "end": None}
        results = provision_universe(spec, tmp_path, force=False, min_year=2024,
                                     converter=self._fake_converter(calls))
        assert calls == []  # converter never called -- skipped
        assert results[0][1].startswith("skip")

    def test_force_redownloads_even_if_fresh(self, tmp_path):
        _write_zip(tmp_path, "SPY", "20260101")
        calls = []
        spec = {"tickers": ["SPY"], "start": "2005-01-01", "end": None}
        provision_universe(spec, tmp_path, force=True, min_year=2024,
                           converter=self._fake_converter(calls))
        assert calls == ["SPY"]

    def test_stale_zip_triggers_redownload(self, tmp_path):
        _write_zip(tmp_path, "SPY", "20210101")  # present but STALE
        calls = []
        spec = {"tickers": ["SPY"], "start": "2005-01-01", "end": None}
        results = provision_universe(spec, tmp_path, force=False, min_year=2024,
                                     converter=self._fake_converter(calls))
        assert calls == ["SPY"]  # stale -> re-provisioned
        assert results[0][1] == "provisioned"


class TestRunGate:
    def test_all_fresh(self, tmp_path):
        _write_zip(tmp_path, "SPY", "20260101")
        _write_zip(tmp_path, "QQQ", "20260101")
        rows = run_gate(tmp_path, ["spy", "qqq"], 2024)
        assert all(not stale for _, _, _, stale in rows)

    def test_detects_stale(self, tmp_path):
        _write_zip(tmp_path, "SPY", "20260101")
        _write_zip(tmp_path, "QQQ", "20210101")  # stale
        rows = run_gate(tmp_path, ["spy", "qqq"], 2024)
        stale = {t: s for t, _, _, s in rows}
        assert stale["spy"] is False
        assert stale["qqq"] is True

    def test_missing_ticker_is_stale(self, tmp_path):
        rows = run_gate(tmp_path, ["nope"], 2024)
        assert rows[0][3] is True  # missing -> stale
