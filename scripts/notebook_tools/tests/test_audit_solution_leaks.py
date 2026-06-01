"""Tests for audit_solution_leaks.py — solution leak pattern detection."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from audit_solution_leaks import (
    detect_function_body_leak,
    detect_commented_solution_leak,
    detect_preresolved_cells,
    get_cells_after_exercice_md,
    audit_notebook,
)


def _code(source: str) -> dict:
    """Build a code cell."""
    lines = source.split("\n")
    elements = [line + "\n" for line in lines[:-1]] + [lines[-1]]
    return {
        "cell_type": "code",
        "source": elements,
        "execution_count": 1,
        "outputs": [],
        "metadata": {},
    }


def _md(source: str) -> dict:
    """Build a markdown cell."""
    lines = source.split("\n")
    elements = [line + "\n" for line in lines[:-1]] + [lines[-1]]
    return {
        "cell_type": "markdown",
        "source": elements,
        "metadata": {},
    }


def _nb(cells: list[dict]) -> dict:
    """Build a minimal notebook dict."""
    return {
        "cells": cells,
        "metadata": {
            "kernelspec": {"display_name": "Python 3", "name": "python3"},
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write_nb(tmp_path: Path, name: str, nb: dict) -> str:
    """Write a notebook to disk and return the path string."""
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return str(p)


# --- detect_function_body_leak ---


class TestDetectFunctionBodyLeak:
    def test_stub_pass_no_leak(self):
        lines = ["def f(x):", "    pass"]
        assert detect_function_body_leak(lines) == []

    def test_stub_return_none_no_leak(self):
        lines = ["def f(x):", "    return None"]
        assert detect_function_body_leak(lines) == []

    def test_stub_return_none_todo_no_leak(self):
        lines = ["def f(x):", "    return None  # TODO etudiant"]
        assert detect_function_body_leak(lines) == []

    def test_stub_print_no_leak(self):
        lines = ["def f(x):", '    print("Exercice a completer")']
        assert detect_function_body_leak(lines) == []

    def test_stub_return_empty_no_leak(self):
        lines = ["def f(x):", "    return []"]
        assert detect_function_body_leak(lines) == []

    def test_function_with_4_logic_lines_is_leak(self):
        """4 logic lines > 3 => MEDIUM leak."""
        lines = [
            "def solve(data):",
            "    a = data[0]",
            "    b = data[1]",
            "    c = a + b",
            "    return c * 2",
        ]
        leaks = detect_function_body_leak(lines)
        assert len(leaks) == 1
        assert leaks[0]["type"] == "function_body_leak"
        assert leaks[0]["func_name"] == "solve"
        assert leaks[0]["logic_lines"] == 4
        assert leaks[0]["severity"] == "MEDIUM"

    def test_function_with_6_logic_lines_is_high(self):
        """6 logic lines > 5 => HIGH severity."""
        lines = [
            "def compute(arr):",
            "    total = 0",
            "    for x in arr:",
            "        total += x ** 2",
            "    mean = total / len(arr)",
            "    result = mean * 2",
            "    return result",
        ]
        leaks = detect_function_body_leak(lines)
        assert len(leaks) == 1
        assert leaks[0]["severity"] == "HIGH"

    def test_two_functions_one_leak(self):
        lines = [
            "def clean(x):",
            "    pass",
            "",
            "def solve(data):",
            "    a = data[0]",
            "    b = data[1]",
            "    c = a + b",
            "    return c * 2",
        ]
        leaks = detect_function_body_leak(lines)
        assert len(leaks) == 1
        assert leaks[0]["func_name"] == "solve"

    def test_3_logic_lines_not_leak(self):
        """Exactly 3 logic lines is NOT a leak (threshold is >3)."""
        lines = [
            "def f(x):",
            "    a = x + 1",
            "    b = a * 2",
            "    return b",
        ]
        assert detect_function_body_leak(lines) == []

    def test_comment_lines_not_counted(self):
        lines = [
            "def f(x):",
            "    # step 1",
            "    # step 2",
            "    # step 3",
            "    # step 4",
            "    a = x + 1",
            "    b = a * 2",
            "    return b",
        ]
        # 3 logic lines (a=, b=, return b) => NOT a leak
        assert detect_function_body_leak(lines) == []

    def test_docstring_not_counted(self):
        lines = [
            "def f(x):",
            '    """Long docstring."""',
            "    a = x + 1",
            "    b = a * 2",
            "    return b",
        ]
        assert detect_function_body_leak(lines) == []


# --- detect_commented_solution_leak ---


class TestDetectCommentedSolutionLeak:
    def test_no_comments_no_leak(self):
        lines = ["x = 1", "y = 2"]
        assert detect_commented_solution_leak(lines) == []

    def test_short_comment_block_no_leak(self):
        """<=3 comment lines with code-like content => no leak."""
        lines = [
            "# result = 1",
            "# expected = 2",
            "# answer = 3",
        ]
        assert detect_commented_solution_leak(lines) == []

    def test_long_comment_block_with_code_is_leak(self):
        """>3 comment lines with code-like content => MEDIUM leak."""
        lines = [
            "# result = 1",
            "# expected = 2",
            "# answer = 3",
            "# correct = 4",
        ]
        leaks = detect_commented_solution_leak(lines)
        assert len(leaks) == 1
        assert leaks[0]["type"] == "commented_solution_leak"
        assert leaks[0]["lines"] == 4
        assert leaks[0]["severity"] == "MEDIUM"

    def test_control_flow_comments_are_leak(self):
        """Mix of control flow + assignment comments => leak when >3 match."""
        lines = [
            "# for i in range(10):",
            "#     if data[i] > 0:",
            "#         total += data[i]",
            "# return result",
            "# expected = total",
        ]
        leaks = detect_commented_solution_leak(lines)
        # 3 lines match control flow (for, if, return) + 1 matches result/expected
        # Actually: line 5 "# expected = total" matches m1 (expected=)
        # Lines 1,2,4 match m3 (for/if/return). Line 3 does not match any pattern.
        # So 4 out of 5 match => block of 4 matching lines > 3 => leak
        assert len(leaks) >= 1

    def test_non_code_comments_not_leak(self):
        lines = [
            "# This is a note",
            "# Another note",
            "# Yet another",
            "# And one more",
        ]
        # These don't match code-like patterns
        assert detect_commented_solution_leak(lines) == []

    def test_shebang_not_counted(self):
        lines = [
            "#!/usr/bin/env python3",
            "# result = 1",
            "# expected = 2",
            "# answer = 3",
        ]
        # Only 3 code-like comments (shebang excluded) => no leak
        assert detect_commented_solution_leak(lines) == []


# --- detect_preresolved_cells ---


class TestDetectPreresolvedCells:
    def test_no_solution_marker_no_leak(self):
        cells = [_code("x = 1\ny = 2")]
        assert detect_preresolved_cells(cells) == []

    def test_solution_marker_short_code_no_leak(self):
        """# Solution with <=3 code lines => no leak."""
        cells = [_code("# Solution\nx = 1\ny = 2")]
        assert detect_preresolved_cells(cells) == []

    def test_solution_marker_long_code_is_leak(self):
        """# Solution with >3 code lines => LOW leak."""
        cells = [_code(
            "# Solution\n"
            "a = 10\n"
            "b = 20\n"
            "c = 30\n"
            "result = a + b + c\n"
        )]
        leaks = detect_preresolved_cells(cells)
        assert len(leaks) == 1
        assert leaks[0]["type"] == "preresolved_cell"
        assert leaks[0]["severity"] == "LOW"

    def test_exemple_resolu_is_detected(self):
        cells = [_code(
            "# Exemple resolu\n"
            "a = 10\n"
            "b = 20\n"
            "c = 30\n"
            "result = a + b + c\n"
        )]
        leaks = detect_preresolved_cells(cells)
        assert len(leaks) == 1

    def test_markdown_cells_skipped(self):
        cells = [_md("# Solution\nComplete answer here")]
        assert detect_preresolved_cells(cells) == []


# --- get_cells_after_exercice_md ---


class TestGetCellsAfterExerciceMd:
    def test_code_cell_following_md(self):
        cells = [
            _md("## Exercice 1\nSolve it."),
            _code("x = 1"),
            _code("y = 2"),
        ]
        result = get_cells_after_exercice_md(cells, 0)
        assert len(result) == 2
        assert result[0][0] == 1
        assert result[1][0] == 2

    def test_stops_at_next_exercice_header(self):
        cells = [
            _md("## Exercice 1\nSolve it."),
            _code("x = 1"),
            _md("## Exercice 2\nAnother."),
            _code("y = 2"),
        ]
        result = get_cells_after_exercice_md(cells, 0)
        assert len(result) == 1

    def test_stops_at_markdown_heading(self):
        cells = [
            _md("## Exercice 1\nSolve it."),
            _code("x = 1"),
            _md("# Section Title"),
            _code("y = 2"),
        ]
        result = get_cells_after_exercice_md(cells, 0)
        assert len(result) == 1

    def test_max_4_cells_checked(self):
        cells = [
            _md("## Exercice 1\nSolve it."),
            _code("a = 1"),
            _code("b = 2"),
            _code("c = 3"),
            _code("d = 4"),
            _code("e = 5"),
        ]
        result = get_cells_after_exercice_md(cells, 0)
        # range(start+1, min(start+5, len)) => range(1, 5) => indices 1,2,3,4
        assert len(result) == 4

    def test_no_code_cells(self):
        cells = [
            _md("## Exercice 1\nSolve it."),
            _md("Some hint"),
            _md("Another hint"),
        ]
        result = get_cells_after_exercice_md(cells, 0)
        assert len(result) == 0


# --- audit_notebook ---


class TestAuditNotebook:
    def test_clean_notebook_no_leaks(self, tmp_path):
        nb = _nb([
            _md("## Exercice 1\nSolve it."),
            _code("pass"),
        ])
        p = _write_nb(tmp_path, "clean.ipynb", nb)
        assert audit_notebook(p) == []

    def test_function_body_leak_in_exercice(self, tmp_path):
        nb = _nb([
            _md("## Exercice 1\nSolve it."),
            _code("# Exercice 1\ndef solve(data):\n    a = data[0]\n    b = data[1]\n    c = a + b\n    return c * 2"),
        ])
        p = _write_nb(tmp_path, "leak.ipynb", nb)
        leaks = audit_notebook(p)
        function_leaks = [l for l in leaks if l["type"] == "function_body_leak"]
        assert len(function_leaks) >= 1

    def test_invalid_json_returns_empty(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        p.write_text("not valid json{{{", encoding="utf-8")
        assert audit_notebook(str(p)) == []

    def test_preresolved_detected(self, tmp_path):
        nb = _nb([
            _code("# Solution\na = 10\nb = 20\nc = 30\nresult = a + b + c\n"),
        ])
        p = _write_nb(tmp_path, "resolved.ipynb", nb)
        leaks = audit_notebook(p)
        preresolved = [l for l in leaks if l["type"] == "preresolved_cell"]
        assert len(preresolved) == 1

    def test_exemple_resolu_skipped_in_exercice_context(self, tmp_path):
        """# Exemple resolu should be skipped from function body leak checks."""
        nb = _nb([
            _md("## Exercice 1\nSolve it."),
            _code("# Exemple resolu\ndef example(data):\n    a = data[0]\n    b = data[1]\n    c = a + b\n    return c * 2"),
        ])
        p = _write_nb(tmp_path, "exemple.ipynb", nb)
        leaks = audit_notebook(p)
        function_leaks = [l for l in leaks if l["type"] == "function_body_leak"]
        assert len(function_leaks) == 0
