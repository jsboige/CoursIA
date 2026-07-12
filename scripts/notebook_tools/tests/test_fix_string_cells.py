"""Tests for scripts/notebook_tools/fix_string_cells.py — STRING→LIST cell converter.

Tests focus on pure functions: convert_string_to_list, fix_list_newlines,
fix_notebook — covering conversion logic, nbformat conventions, edge cases.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from fix_string_cells import convert_string_to_list, fix_list_newlines, fix_notebook


# ---------------------------------------------------------------------------
# convert_string_to_list
# ---------------------------------------------------------------------------

class TestConvertStringToList:
    """Tests for STRING source → LIST format conversion."""

    def test_string_multiline(self):
        """Multi-line string -> list with \\n on non-last lines."""
        result = convert_string_to_list("line1\nline2\nline3")
        assert result == ["line1\n", "line2\n", "line3"]

    def test_string_single_line(self):
        """Single-line string -> single-element list without \\n."""
        result = convert_string_to_list("only line")
        assert result == ["only line"]

    def test_string_empty(self):
        """Empty string -> single-element list with empty string."""
        result = convert_string_to_list("")
        assert result == [""]

    def test_string_trailing_newline(self):
        """String ending with \\n -> last element is empty string."""
        result = convert_string_to_list("a\nb\n")
        assert result == ["a\n", "b\n", ""]

    def test_string_two_lines(self):
        result = convert_string_to_list("first\nsecond")
        assert result == ["first\n", "second"]

    def test_list_passthrough(self):
        """If source is already a list, return unchanged."""
        src = ["line1\n", "line2"]
        result = convert_string_to_list(src)
        assert result is src

    def test_list_empty_passthrough(self):
        """Empty list passed through as-is."""
        assert convert_string_to_list([]) == []

    def test_string_code_cell_content(self):
        """Realistic code cell content."""
        code = "import os\nimport sys\nprint('hello')"
        result = convert_string_to_list(code)
        assert result == ["import os\n", "import sys\n", "print('hello')"]

    def test_string_blank_lines(self):
        """String with blank intermediate lines."""
        result = convert_string_to_list("a\n\nc")
        assert result == ["a\n", "\n", "c"]


# ---------------------------------------------------------------------------
# fix_list_newlines
# ---------------------------------------------------------------------------

class TestFixListNewlines:
    """Tests for fixing LIST cells missing trailing \\n on non-last lines."""

    def test_already_correct(self):
        """List with correct \\n on non-last lines -> unchanged."""
        src = ["line1\n", "line2\n", "line3"]
        result = fix_list_newlines(src)
        assert result == src

    def test_missing_newlines(self):
        """List with missing \\n -> fixed."""
        src = ["line1", "line2", "line3"]
        result = fix_list_newlines(src)
        assert result == ["line1\n", "line2\n", "line3"]

    def test_single_element(self):
        """Single-element list -> unchanged (no non-last lines)."""
        src = ["only line"]
        result = fix_list_newlines(src)
        assert result is src

    def test_empty_list(self):
        """Empty list -> unchanged."""
        result = fix_list_newlines([])
        assert result == []

    def test_two_elements_missing_nl(self):
        """Two elements, first missing \\n."""
        src = ["first", "second"]
        result = fix_list_newlines(src)
        assert result == ["first\n", "second"]

    def test_two_elements_correct(self):
        """Two elements, first has \\n -> unchanged."""
        src = ["first\n", "second"]
        result = fix_list_newlines(src)
        assert result == src

    def test_partial_missing(self):
        """Some lines missing \\n, some correct."""
        src = ["line1\n", "line2", "line3"]
        result = fix_list_newlines(src)
        assert result == ["line1\n", "line2\n", "line3"]

    def test_empty_line_in_middle(self):
        """Empty string in middle of list (no \\n to add)."""
        src = ["line1", "", "line3"]
        result = fix_list_newlines(src)
        # Empty line has nothing to append \n to
        assert result == ["line1\n", "\n", "line3"]

    def test_last_line_has_newline_unchanged(self):
        """If last line has \\n, non-last lines correct -> unchanged."""
        src = ["a\n", "b\n", "c\n"]
        result = fix_list_newlines(src)
        assert result == src


# ---------------------------------------------------------------------------
# fix_notebook
# ---------------------------------------------------------------------------

class TestFixNotebook:
    """Tests for fix_notebook — file-level fix with write-back."""

    def _write_nb(self, path: Path, cells: list[dict]) -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        path.write_text(json.dumps(nb), encoding="utf-8")
        return path

    def test_string_cell_converted(self, tmp_path):
        """Notebook with STRING source cell -> converted and written."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": "a\nb\nc", "outputs": [], "execution_count": 1},
        ])
        modified = fix_notebook(nb_path)
        assert modified is True

        with open(nb_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        assert data["cells"][0]["source"] == ["a\n", "b\n", "c"]

    def test_list_cell_already_correct(self, tmp_path):
        """Notebook with correct LIST source -> no changes."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": ["a\n", "b"], "outputs": [], "execution_count": 1},
        ])
        modified = fix_notebook(nb_path)
        assert modified is False

    def test_list_cell_missing_newlines(self, tmp_path):
        """Notebook with LIST missing \\n -> fixed."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": ["a", "b", "c"], "outputs": [], "execution_count": 1},
        ])
        modified = fix_notebook(nb_path)
        assert modified is True

        with open(nb_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        assert data["cells"][0]["source"] == ["a\n", "b\n", "c"]

    def test_dry_run_no_write(self, tmp_path):
        """dry_run=True -> detect changes but don't write."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": "hello\nworld", "outputs": [], "execution_count": 1},
        ])
        original = nb_path.read_text(encoding="utf-8")
        modified = fix_notebook(nb_path, dry_run=True)
        assert modified is True
        assert nb_path.read_text(encoding="utf-8") == original

    def test_multiple_cells_mixed(self, tmp_path):
        """Mix of STRING and correct LIST cells."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": "line1\nline2", "outputs": [], "execution_count": 1},
            {"cell_type": "markdown", "source": ["# Title\n", "Text"], "metadata": {}},
            {"cell_type": "code", "source": ["a\n", "b"], "outputs": [], "execution_count": 2},
        ])
        modified = fix_notebook(nb_path)
        assert modified is True

        with open(nb_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        assert data["cells"][0]["source"] == ["line1\n", "line2"]
        assert data["cells"][1]["source"] == ["# Title\n", "Text"]
        assert data["cells"][2]["source"] == ["a\n", "b"]

    def test_no_cells(self, tmp_path):
        """Notebook with no cells -> no changes."""
        nb_path = self._write_nb(tmp_path / "empty.ipynb", [])
        modified = fix_notebook(nb_path)
        assert modified is False

    def test_empty_source_not_touched(self, tmp_path):
        """Cell with empty string source -> not modified (empty string passed through)."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": "", "outputs": [], "execution_count": None},
        ])
        modified = fix_notebook(nb_path)
        # Empty string source is falsy (if source:) check -> no modification
        assert modified is False

    def test_output_file_trailing_newline(self, tmp_path):
        """Written file ends with trailing newline."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": "x = 1\ny = 2", "outputs": [], "execution_count": 1},
        ])
        fix_notebook(nb_path)
        content = nb_path.read_text(encoding="utf-8")
        assert content.endswith("\n")

    def test_markdown_string_cell_converted(self, tmp_path):
        """Markdown cells with STRING source are also converted."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "markdown", "source": "# Title\nSome text", "metadata": {}},
        ])
        modified = fix_notebook(nb_path)
        assert modified is True

        with open(nb_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        assert data["cells"][0]["source"] == ["# Title\n", "Some text"]

    def test_single_element_list_not_touched(self, tmp_path):
        """Single-element LIST -> fix_list_newlines skips (len <= 1)."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": ["single line"], "outputs": [], "execution_count": 1},
        ])
        modified = fix_notebook(nb_path)
        assert modified is False

    def test_unicode_content(self, tmp_path):
        """Unicode content in STRING cells handled correctly."""
        nb_path = self._write_nb(tmp_path / "test.ipynb", [
            {"cell_type": "code", "source": "print('héllo\nwörld')", "outputs": [], "execution_count": 1},
        ])
        modified = fix_notebook(nb_path)
        assert modified is True

        with open(nb_path, "r", encoding="utf-8") as f:
            data = json.load(f)
        assert data["cells"][0]["source"] == ["print('héllo\n", "wörld')"]
