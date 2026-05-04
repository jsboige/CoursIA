"""Tests for fix_string_cells.py — string-to-list conversion and newline fixing."""

import json
import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from fix_string_cells import convert_string_to_list, fix_list_newlines, fix_notebook


class TestConvertStringToList:

    def test_simple_string(self):
        result = convert_string_to_list("a\nb\nc")
        assert result == ["a\n", "b\n", "c"]

    def test_single_line(self):
        result = convert_string_to_list("hello")
        assert result == ["hello"]

    def test_empty_string(self):
        result = convert_string_to_list("")
        assert result == [""]

    def test_trailing_newline(self):
        result = convert_string_to_list("line1\nline2\n")
        assert result == ["line1\n", "line2\n", ""]

    def test_already_list_passthrough(self):
        src = ["a\n", "b\n"]
        result = convert_string_to_list(src)
        assert result is src

    def test_multiline_code(self):
        result = convert_string_to_list("import os\nimport sys\nprint('hi')")
        assert result == ["import os\n", "import sys\n", "print('hi')"]


class TestFixListNewlines:

    def test_correct_list_unchanged(self):
        src = ["a\n", "b\n", "c"]
        assert fix_list_newlines(src) is src

    def test_missing_newlines_fixed(self):
        src = ["a", "b", "c"]
        result = fix_list_newlines(src)
        assert result == ["a\n", "b\n", "c"]

    def test_single_element_unchanged(self):
        src = ["single line"]
        assert fix_list_newlines(src) is src

    def test_empty_list_unchanged(self):
        assert fix_list_newlines([]) == []

    def test_partial_fix(self):
        src = ["a\n", "b", "c"]
        result = fix_list_newlines(src)
        assert result == ["a\n", "b\n", "c"]

    def test_empty_line_in_middle_not_fixed(self):
        """Empty lines ('') don't end with \\n but are falsy — not flagged."""
        src = ["a\n", "", "c"]
        result = fix_list_newlines(src)
        # The function checks `if line and not line.endswith('\n')` — empty
        # string is falsy, so it's not considered "needs fixing"
        assert result == ["a\n", "", "c"]


class TestFixNotebook:

    def _write_nb(self, cells, tmp_path, name="test.ipynb"):
        nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
        p = tmp_path / name
        p.write_text(json.dumps(nb), encoding="utf-8")
        return p

    def test_fix_string_cell(self, tmp_path):
        cells = [{"cell_type": "code", "source": "line1\nline2"}]
        p = self._write_nb(cells, tmp_path)
        assert fix_notebook(p)
        data = json.loads(p.read_text(encoding="utf-8"))
        assert isinstance(data["cells"][0]["source"], list)

    def test_fix_missing_newlines(self, tmp_path):
        cells = [{"cell_type": "code", "source": ["a", "b", "c"]}]
        p = self._write_nb(cells, tmp_path)
        assert fix_notebook(p)
        data = json.loads(p.read_text(encoding="utf-8"))
        assert data["cells"][0]["source"] == ["a\n", "b\n", "c"]

    def test_no_changes_needed(self, tmp_path):
        cells = [{"cell_type": "code", "source": ["a\n", "b\n"]}]
        p = self._write_nb(cells, tmp_path)
        assert not fix_notebook(p)

    def test_dry_run_no_write(self, tmp_path):
        cells = [{"cell_type": "code", "source": "string source"}]
        p = self._write_nb(cells, tmp_path)
        original = p.read_text(encoding="utf-8")
        assert fix_notebook(p, dry_run=True)
        assert p.read_text(encoding="utf-8") == original

    def test_empty_source_string_no_change(self, tmp_path):
        """Empty string source is falsy — fix_notebook skips it."""
        cells = [{"cell_type": "code", "source": ""}]
        p = self._write_nb(cells, tmp_path)
        # source="" is falsy, so the `if source and isinstance(source, str)`
        # guard doesn't trigger — no fix applied
        assert not fix_notebook(p)

    def test_markdown_cell_string_fixed(self, tmp_path):
        cells = [{"cell_type": "markdown", "source": "# Title\nSome text"}]
        p = self._write_nb(cells, tmp_path)
        assert fix_notebook(p)
        data = json.loads(p.read_text(encoding="utf-8"))
        assert isinstance(data["cells"][0]["source"], list)
