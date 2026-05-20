"""Tests for notebook_lint.py — C.1, C.2, structure, metadata checks."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent))
from notebook_lint import (
    _is_in_docstring,
    check_c1,
    check_c2,
    check_metadata,
    check_structure,
    lint_notebook,
)


def _nb(cells: list[dict], **meta) -> dict:
    """Build a minimal notebook dict."""
    return {
        "cells": cells,
        "metadata": {
            "kernelspec": {"display_name": "Python 3", "name": "python3"},
            **meta,
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _code(source: str, execution_count: int = 1, outputs: list | None = None) -> dict:
    """Build a code cell with newline-terminated source elements (like real notebooks)."""
    lines = source.split("\n")
    # Real notebook cells have \n at end of each element except the last
    elements = [line + "\n" for line in lines[:-1]] + [lines[-1]]
    return {
        "cell_type": "code",
        "source": elements,
        "execution_count": execution_count,
        "outputs": outputs or [{"output_type": "execute_result", "data": {"text/plain": ["ok"]}}],
        "metadata": {},
    }


def _md(source: str) -> dict:
    """Build a markdown cell with newline-terminated source elements."""
    lines = source.split("\n")
    elements = [line + "\n" for line in lines[:-1]] + [lines[-1]]
    return {
        "cell_type": "markdown",
        "source": elements,
        "metadata": {},
    }


# --- _is_in_docstring tests ---

class TestIsInDocstring:
    def test_no_docstring(self):
        in_doc, is_inside = _is_in_docstring("x = 1", False)
        assert in_doc is False
        assert is_inside is False

    def test_opening_docstring(self):
        in_doc, is_inside = _is_in_docstring('    """doc', False)
        assert in_doc is True
        assert is_inside is True

    def test_closing_docstring(self):
        in_doc, is_inside = _is_in_docstring('    doc"""', True)
        assert in_doc is False
        assert is_inside is True  # was inside at start of line

    def test_full_line_docstring(self):
        in_doc, is_inside = _is_in_docstring('    """full doc"""', False)
        # 2 triple-quotes on same line = even count = no toggle
        assert in_doc is False
        assert is_inside is False

    def test_multiline_docstring_track(self):
        state = False
        state, inside = _is_in_docstring('"""start', state)
        assert state is True
        assert inside is True
        state, inside = _is_in_docstring("middle line", state)
        assert state is True
        assert inside is True
        state, inside = _is_in_docstring('end"""', state)
        assert state is False
        assert inside is True  # was inside at start of line

    def test_single_quotes(self):
        state = False
        state, inside = _is_in_docstring("'''start", state)
        assert state is True
        assert inside is True
        state, inside = _is_in_docstring("end'''", state)
        assert state is False

    def test_nested_different_quotes(self):
        """Double quotes inside single-quoted docstring should not toggle."""
        state = False
        state, _ = _is_in_docstring("'''start", state)
        assert state is True
        state, _ = _is_in_docstring('  has """ inside', state)
        # """ inside ''' docstring toggles state — known edge case
        # This test documents current behavior, not ideal behavior
        assert state is False  # toggled off by """ inside '''


# --- C.1 tests ---

class TestCheckC1:
    def test_clean_notebook(self):
        nb = _nb([
            _md("# Title"),
            _code("x = 1\ny = 2\nprint(x + y)"),
        ])
        assert check_c1(nb) == []

    def test_raise_not_implemented(self):
        nb = _nb([
            _md("# Title"),
            _code("raise NotImplementedError('TODO')"),
        ])
        violations = check_c1(nb)
        assert len(violations) == 1
        assert violations[0]["pattern"] == "raise NotImplementedError"

    def test_assert_false(self):
        nb = _nb([
            _code("assert False"),
        ])
        violations = check_c1(nb)
        assert len(violations) == 1
        assert violations[0]["pattern"] == "assert False"

    def test_divide_by_zero(self):
        nb = _nb([
            _code("x = 1/0"),
        ])
        violations = check_c1(nb)
        assert len(violations) == 1
        assert violations[0]["pattern"] == "1/0"

    def test_commented_error_not_flagged(self):
        nb = _nb([
            _code("# raise NotImplementedError('skip')"),
        ])
        assert check_c1(nb) == []

    def test_docstring_error_not_flagged(self):
        # _code splits on \n, adding \n per element — mimics real notebooks
        nb = _nb([
            _code('"""\nThis example shows 1/0 error\n"""'),
        ])
        violations = check_c1(nb)
        assert all(v["pattern"] != "1/0" for v in violations)

    def test_legitimate_code_not_flagged(self):
        nb = _nb([
            _code("result = 10 / 2  # not 1/0"),
            _code("assert len(data) > 0"),
            _code("raise ValueError('bad input')"),
        ])
        violations = check_c1(nb)
        assert len(violations) == 0

    def test_markdown_cells_skipped(self):
        nb = _nb([
            _md("Some text with raise NotImplementedError in it"),
        ])
        assert check_c1(nb) == []


# --- C.2 tests ---

class TestCheckC2:
    def test_executed_notebook(self):
        nb = _nb([
            _code("x = 1", execution_count=1),
        ])
        assert check_c2(nb) == []

    def test_unexecuted_cell(self):
        nb = _nb([
            _code("x = 1", execution_count=None),
        ])
        violations = check_c2(nb)
        assert len(violations) == 1
        assert violations[0]["reason"] == "missing execution_count"

    def test_empty_cell_skipped(self):
        nb = _nb([
            _code("", execution_count=None),
        ])
        assert check_c2(nb) == []

    def test_comment_only_cell_skipped(self):
        nb = _nb([
            _code("# Just a comment\n# Another comment", execution_count=None),
        ])
        assert check_c2(nb) == []

    def test_mixed_executed_unexecuted(self):
        nb = _nb([
            _code("x = 1", execution_count=1),
            _code("y = 2", execution_count=None),
            _code("z = 3", execution_count=3),
        ])
        violations = check_c2(nb)
        assert len(violations) == 1
        assert violations[0]["cell_index"] == 1


# --- Structure tests ---

class TestCheckStructure:
    def test_well_structured(self):
        nb = _nb([
            _md("# Title"),
            _code("x = 1"),
            _md("## Section"),
            _code("y = 2"),
        ])
        assert check_structure(nb) == []

    def test_empty_code_cell(self):
        nb = _nb([
            _code(""),
        ])
        violations = check_structure(nb)
        assert any(v["reason"] == "empty code cell" for v in violations)

    def test_consecutive_code_cells(self):
        cells = [_md("# Title")] + [_code(f"x_{i} = {i}") for i in range(8)]
        nb = _nb(cells)
        violations = check_structure(nb)
        streak_violations = [v for v in violations if "consecutive" in v["reason"]]
        assert len(streak_violations) > 0


# --- Metadata tests ---

class TestCheckMetadata:
    def test_valid_metadata(self):
        nb = _nb([_md("# My Notebook")])
        assert check_metadata(nb) == []

    def test_missing_kernel(self):
        nb = _nb([_md("# Title")])
        nb["metadata"] = {}
        violations = check_metadata(nb)
        assert any(v["reason"] == "no kernel defined" for v in violations)

    def test_missing_title(self):
        nb = _nb([_code("x = 1")])
        violations = check_metadata(nb)
        assert any(v["reason"] == "no title heading found" for v in violations)


# --- Integration: lint_notebook ---

class TestLintNotebook:
    def test_nonexistent_file(self, tmp_path):
        result = lint_notebook(tmp_path / "nonexistent.ipynb", {"c1", "c2"})
        assert "error" in result

    def test_invalid_json(self, tmp_path):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("not json{{{{", encoding="utf-8")
        result = lint_notebook(bad, {"c1"})
        assert "error" in result

    def test_clean_notebook(self, tmp_path):
        nb = _nb([
            _md("# Title"),
            _code("x = 1", execution_count=1),
        ])
        p = tmp_path / "clean.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        result = lint_notebook(p, {"c1", "c2", "structure", "meta"})
        assert result["violations"] == []
