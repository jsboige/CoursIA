"""Tests for qc_quantbook_execute.py — workspace_root, find_lean, and the
#8734 data-quality pre-flight (extract_requested_symbols / preflight_data_quality)."""

import json
import os
import sys
import zipfile
from datetime import date
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from qc_quantbook_execute import (
    workspace_root,
    find_lean,
    LEAN_BIN_CANDIDATES,
    extract_requested_symbols,
    preflight_data_quality,
)


# --- workspace_root ---


class TestWorkspaceRoot:
    def test_finds_lean_json(self, tmp_path):
        """Should find lean.json in parent directory."""
        ws = tmp_path / "workspace"
        project = ws / "project"
        project.mkdir(parents=True)
        (ws / "lean.json").write_text("{}", encoding="utf-8")
        result = workspace_root(project)
        assert result == ws.resolve()

    def test_finds_in_grandparent(self, tmp_path):
        """Should traverse up multiple levels."""
        ws = tmp_path / "workspace"
        deep = ws / "src" / "project"
        deep.mkdir(parents=True)
        (ws / "lean.json").write_text("{}", encoding="utf-8")
        result = workspace_root(deep)
        assert result == ws.resolve()

    def test_not_found_raises(self, tmp_path):
        """Should raise RuntimeError when no lean.json found."""
        deep = tmp_path / "a" / "b" / "c"
        deep.mkdir(parents=True)
        with pytest.raises(RuntimeError, match="No lean.json"):
            workspace_root(deep)

    def test_current_dir_has_lean_json(self, tmp_path):
        """If the directory itself has lean.json, return it."""
        (tmp_path / "lean.json").write_text("{}", encoding="utf-8")
        result = workspace_root(tmp_path)
        assert result == tmp_path.resolve()


# --- find_lean ---


class TestFindLean:
    def test_env_var_override(self, tmp_path, monkeypatch):
        """LEAN_CLI env var should take precedence."""
        fake_lean = tmp_path / "fake_lean.exe"
        fake_lean.write_text("fake", encoding="utf-8")
        monkeypatch.setenv("LEAN_CLI", str(fake_lean))
        assert find_lean() == str(fake_lean)

    def test_env_var_nonexistent_falls_through(self, monkeypatch):
        """LEAN_CLI pointing to nonexistent file falls through to candidates/which."""
        monkeypatch.setenv("LEAN_CLI", "/nonexistent/path/lean")
        # Falls through to candidate search, then shutil.which
        # May find lean via shutil.which if installed, or raise RuntimeError
        try:
            result = find_lean()
            assert isinstance(result, str)
        except RuntimeError:
            pass  # Also acceptable if lean not installed

    def test_no_env_no_candidates_graceful(self, monkeypatch):
        """When no LEAN_CLI, candidates may not exist. Result depends on install."""
        monkeypatch.delenv("LEAN_CLI", raising=False)
        try:
            result = find_lean()
            assert isinstance(result, str)
        except RuntimeError:
            pass  # Expected when lean is not installed


# --- #8734 data-quality pre-flight ---


def _nb(cells):
    """Build a minimal notebook dict from (type, source) tuples."""
    return {"cells": [{"cell_type": t, "source": s, "metadata": {}} for t, s in cells],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _write_daily_zip(path: Path, rows: list[str]) -> None:
    """Write a QC-style daily zip (one CSV, no header, 'YYYYMMDD HH:MM,o,h,l,c,v')."""
    path.parent.mkdir(parents=True, exist_ok=True)
    csv = "\n".join(rows).encode("utf-8")
    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as z:
        z.writestr(path.stem + ".csv", csv)


class TestExtractRequestedSymbols:
    def test_equity_python_and_csharp(self, tmp_path):
        nb = tmp_path / "research.ipynb"
        nb.write_text(json.dumps(_nb([
            ("code", 'qb.add_equity("SPY", Resolution.Daily)'),
            ("code", 'self.AddEquity("qqq")'),
        ])), encoding="utf-8")
        syms = extract_requested_symbols(nb)
        assert syms["equity"] == {"SPY", "QQQ"}

    def test_asset_class_split(self, tmp_path):
        nb = tmp_path / "research.ipynb"
        nb.write_text(json.dumps(_nb([
            ("code", 'qb.AddEquity("SPY")'),
            ("code", 'qb.AddForex("EURUSD")'),
            ("code", 'qb.AddCrypto("BTCUSD")'),
        ])), encoding="utf-8")
        syms = extract_requested_symbols(nb)
        assert syms["equity"] == {"SPY"}
        assert syms["forex"] == {"EURUSD"}
        assert syms["crypto"] == {"BTCUSD"}

    def test_ignores_markdown_and_comments(self, tmp_path):
        """Markdown cells and plain strings must not be mined as data requests."""
        nb = tmp_path / "research.ipynb"
        nb.write_text(json.dumps(_nb([
            ("markdown", 'We call qb.AddEquity("SPY") here.'),
            ("code", '# demo: self.AddEquity("DUMMY")\nprice = "100"'),
            ("code", 'qb.add_equity("REAL")'),
        ])), encoding="utf-8")
        syms = extract_requested_symbols(nb)
        assert syms["equity"] == {"REAL"}  # markdown + comment excluded

    def test_missing_notebook_returns_empty(self, tmp_path):
        syms = extract_requested_symbols(tmp_path / "nope.ipynb")
        assert all(len(v) == 0 for v in syms.values())

    def test_malformed_json_returns_empty(self, tmp_path):
        nb = tmp_path / "broken.ipynb"
        nb.write_text("{not json", encoding="utf-8")
        syms = extract_requested_symbols(nb)
        assert all(len(v) == 0 for v in syms.values())


class TestPreflightDataQuality:
    def _ws(self, tmp_path: Path) -> Path:
        ws = tmp_path / "ws"
        (ws / "data").mkdir(parents=True)
        (ws / "lean.json").write_text("{}", encoding="utf-8")
        return ws

    def test_degenerate_flagged(self, tmp_path):
        ws = self._ws(tmp_path)
        # 60 identical closes ending today -> DEGENERATE (#8734 signature).
        today = date.today().year
        rows = [f"{today}{m:02d}15 00:00,1,2,0,396.33,0" for m in range(1, 13)] * 5
        _write_daily_zip(ws / "data" / "equity" / "usa" / "daily" / "SPY.zip", rows)
        n, msgs = preflight_data_quality(
            ws, {"equity": {"SPY"}, "forex": set(), "crypto": set()}, flat_tail_bars=60)
        assert n == 1
        assert any("DEGENERATE" in m for m in msgs)

    def test_stale_flagged(self, tmp_path):
        ws = self._ws(tmp_path)
        _write_daily_zip(ws / "data" / "equity" / "usa" / "daily" / "SPY.zip", [
            "20150102 00:00,1,2,0,100.5,1000",
            "20210331 00:00,1,2,0,200.5,1000",
        ])
        n, msgs = preflight_data_quality(
            ws, {"equity": {"SPY"}, "forex": set(), "crypto": set()}, flat_tail_bars=60)
        assert n == 1
        assert any("STALE" in m for m in msgs)

    def test_fresh_not_flagged(self, tmp_path):
        ws = self._ws(tmp_path)
        today = date.today()
        rows = [f"{today.year}{m:02d}15 00:00,1,2,0,{300 + m}.5,1000" for m in range(1, 13)]
        _write_daily_zip(ws / "data" / "equity" / "usa" / "daily" / "SPY.zip", rows)
        n, msgs = preflight_data_quality(
            ws, {"equity": {"SPY"}, "forex": set(), "crypto": set()}, flat_tail_bars=60)
        assert n == 0 and msgs == []

    def test_missing_symbol_not_flagged(self, tmp_path):
        """Absence is NOT flagged by the pre-flight (provisioning is separate, #8724)."""
        ws = self._ws(tmp_path)
        n, msgs = preflight_data_quality(
            ws, {"equity": {"NOPE"}, "forex": set(), "crypto": set()}, flat_tail_bars=60)
        assert n == 0 and msgs == []

    def test_only_requested_symbols_scanned(self, tmp_path):
        """A degenerate zip for a NON-requested ticker must not flag."""
        ws = self._ws(tmp_path)
        today = date.today().year
        rows = [f"{today}{m:02d}15 00:00,1,2,0,396.33,0" for m in range(1, 13)] * 5
        _write_daily_zip(ws / "data" / "equity" / "usa" / "daily" / "DEAD.zip", rows)
        n, msgs = preflight_data_quality(
            ws, {"equity": {"SPY"}, "forex": set(), "crypto": set()}, flat_tail_bars=60)
        assert n == 0  # SPY absent, DEAD not requested -> nothing flagged

    def test_flat_tail_disabled_when_zero(self, tmp_path):
        """flat_tail_bars=0 disables the DEGENERATE check (STALE still applies if old)."""
        ws = self._ws(tmp_path)
        today = date.today().year
        rows = [f"{today}{m:02d}15 00:00,1,2,0,396.33,0" for m in range(1, 13)] * 5
        _write_daily_zip(ws / "data" / "equity" / "usa" / "daily" / "SPY.zip", rows)
        n, _ = preflight_data_quality(
            ws, {"equity": {"SPY"}, "forex": set(), "crypto": set()}, flat_tail_bars=0)
        assert n == 0  # date is current, flat-tail check disabled -> OK
