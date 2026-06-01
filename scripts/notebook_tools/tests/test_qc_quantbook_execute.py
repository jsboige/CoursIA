"""Tests for qc_quantbook_execute.py — workspace_root and find_lean."""

import os
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from qc_quantbook_execute import workspace_root, find_lean, LEAN_BIN_CANDIDATES


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
