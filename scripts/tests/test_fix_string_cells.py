"""Tests for scripts/notebook_tools/fix_string_cells.py — string-to-list cell converter.

Tests focus on pure functions: convert_string_to_list, fix_list_newlines,
fix_notebook. Uses tmp_path for filesystem isolation.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
from fix_string_cells import convert_string_to_list, fix_list_newlines, fix_notebook


# ---------------------------------------------------------------------------
# convert_string_to_list
# ---------------------------------------------------------------------------

class TestConvertStringToList:
    def test_simple_multiline(self):
        result = convert_string_to_list("a\nb\nc")
        assert result == ["a\n", "b\n", "c"]

    def test_single_line_no_newline(self):
        result = convert_string_to_list("hello")
        assert result == ["hello"]

    def test_empty_string(self):
        result = convert_string_to_list("")
        assert result == [""]

    def test_already_list(self):
        src = ["a\n", "b\n", "c"]
        assert convert_string_to_list(src) == src

    def test_already_list_empty(self):
        assert convert_string_to_list([]) == []

    def test_trailing_newline(self):
        result = convert_string_to_list("a\nb\n")
        assert result == ["a\n", "b\n", ""]

    def test_only_newlines(self):
        result = convert_string_to_list("\n\n")
        assert result == ["\n", "\n", ""]


# ---------------------------------------------------------------------------
# fix_list_newlines
# ---------------------------------------------------------------------------

class TestFixListNewlines:
    def test_correct_list_unchanged(self):
        src = ["a\n", "b\n", "c"]
        assert fix_list_newlines(src) == src

    def test_fix_missing_newlines(self):
        src = ["a", "b", "c"]
        result = fix_list_newlines(src)
        assert result == ["a\n", "b\n", "c"]

    def test_single_line_unchanged(self):
        src = ["hello"]
        assert fix_list_newlines(src) == src

    def test_empty_list_unchanged(self):
        assert fix_list_newlines([]) == []

    def test_partial_fix(self):
        src = ["a\n", "b", "c"]
        result = fix_list_newlines(src)
        assert result == ["a\n", "b\n", "c"]

    def test_last_line_no_newline_unchanged(self):
        """Last line should NOT get a trailing newline (nbformat convention)."""
        src = ["a\n", "b\n", "c"]
        result = fix_list_newlines(src)
        assert result[-1] == "c"
        assert not result[-1].endswith("\n")

    def test_empty_lines_preserved(self):
        src = ["\n", "\n", ""]
        assert fix_list_newlines(src) == src

    def test_two_lines_needs_fix(self):
        src = ["a", "b"]
        result = fix_list_newlines(src)
        assert result == ["a\n", "b"]

    def test_two_lines_already_ok(self):
        src = ["a\n", "b"]
        assert fix_list_newlines(src) == src


# ---------------------------------------------------------------------------
# fix_notebook
# ---------------------------------------------------------------------------

class TestFixNotebook:
    def _write_nb(self, path: Path, cells: list[dict]) -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        path.write_text(json.dumps(nb), encoding="utf-8")
        return path

    def test_fix_string_cell(self, tmp_path):
        path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": "a\nb\nc", "outputs": [], "execution_count": None}
        ])
        result = fix_notebook(path)
        assert result is True
        data = json.loads(path.read_text(encoding="utf-8"))
        assert data["cells"][0]["source"] == ["a\n", "b\n", "c"]

    def test_fix_missing_newlines(self, tmp_path):
        path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": ["a", "b", "c"], "outputs": [], "execution_count": None}
        ])
        result = fix_notebook(path)
        assert result is True
        data = json.loads(path.read_text(encoding="utf-8"))
        assert data["cells"][0]["source"] == ["a\n", "b\n", "c"]

    def test_no_change_needed(self, tmp_path):
        path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": ["a\n", "b\n", "c"], "outputs": [], "execution_count": None}
        ])
        result = fix_notebook(path)
        assert result is False

    def test_dry_run_no_write(self, tmp_path):
        path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": "a\nb", "outputs": [], "execution_count": None}
        ])
        original = path.read_text(encoding="utf-8")
        result = fix_notebook(path, dry_run=True)
        assert result is True
        # File unchanged
        assert path.read_text(encoding="utf-8") == original

    def test_mixed_cells(self, tmp_path):
        path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": "string_source", "outputs": [], "execution_count": None},
            {"cell_type": "markdown", "source": ["ok\n", "line"], "metadata": {}},
            {"cell_type": "code", "source": ["missing", "newlines"], "outputs": [], "execution_count": None},
        ])
        result = fix_notebook(path)
        assert result is True
        data = json.loads(path.read_text(encoding="utf-8"))
        # Cell 0: string -> list
        assert isinstance(data["cells"][0]["source"], list)
        # Cell 1: already ok
        assert data["cells"][1]["source"] == ["ok\n", "line"]
        # Cell 2: fixed newlines
        assert data["cells"][2]["source"] == ["missing\n", "newlines"]

    def test_empty_source_not_modified(self, tmp_path):
        path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": "", "outputs": [], "execution_count": None}
        ])
        # Empty string is falsy, so fix_notebook skips it (no change)
        result = fix_notebook(path)
        assert result is False

    def test_none_source_not_modified(self, tmp_path):
        path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": None, "outputs": [], "execution_count": None}
        ])
        result = fix_notebook(path)
        assert result is False

    def test_missing_source_key_not_modified(self, tmp_path):
        path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "outputs": [], "execution_count": None}
        ])
        result = fix_notebook(path)
        assert result is False

    def test_output_trailing_newline(self, tmp_path):
        """Saved file should end with a trailing newline."""
        path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": "x", "outputs": [], "execution_count": None}
        ])
        fix_notebook(path)
        content = path.read_text(encoding="utf-8")
        assert content.endswith("\n")
