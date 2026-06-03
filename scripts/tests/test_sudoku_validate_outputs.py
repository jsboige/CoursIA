"""Tests for scripts/notebook_tools/sudoku_validate_outputs.py — Sudoku output validation.

Tests focus on pure functions: classify_kernel, and validate_notebook using
temporary notebook fixtures. No real filesystem I/O on production notebooks.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
from sudoku_validate_outputs import classify_kernel, validate_notebook


# ---------------------------------------------------------------------------
# Helpers — minimal notebook structures
# ---------------------------------------------------------------------------

def _make_notebook(cells, kernelspec=None):
    """Build a minimal .ipynb dict."""
    nb = {
        "nbformat": 4,
        "nbformat_minor": 5,
        "metadata": {},
        "cells": cells,
    }
    if kernelspec:
        nb["metadata"]["kernelspec"] = kernelspec
    return nb


def _code_cell(source, execution_count=1, outputs=None, cell_index=0):
    """Build a code cell."""
    if isinstance(source, str):
        source = [source]
    return {
        "cell_type": "code",
        "source": source,
        "execution_count": execution_count,
        "outputs": outputs or [],
        "metadata": {},
        "cell_id": str(cell_index),
    }


def _markdown_cell(source="text"):
    """Build a markdown cell."""
    return {
        "cell_type": "markdown",
        "source": [source],
        "metadata": {},
        "cell_id": "md",
    }


def _write_nb(tmp_path, nb_dict, name="test.ipynb"):
    """Write notebook dict to temp file and return path."""
    p = tmp_path / name
    p.write_text(json.dumps(nb_dict), encoding="utf-8")
    return str(p)


# ---------------------------------------------------------------------------
# classify_kernel
# ---------------------------------------------------------------------------

class TestClassifyKernel:
    def test_dotnet_kernel(self):
        assert classify_kernel({"kernel": ".NET (C#)"}) == "dotnet"

    def test_dotnet_fsharp(self):
        assert classify_kernel({"kernel": ".NET (F#)"}) == "dotnet"

    def test_csharp_name(self):
        assert classify_kernel({"kernel": "csharp"}) == "dotnet"

    def test_fsharp_name(self):
        assert classify_kernel({"kernel": "fsharp"}) == "dotnet"

    def test_python_kernel(self):
        assert classify_kernel({"kernel": "Python 3"}) == "python"

    def test_python3_ipykernel(self):
        """'python' is a substring of 'python3' → classified as python."""
        assert classify_kernel({"kernel": "python3"}) == "python"

    def test_unknown_kernel(self):
        assert classify_kernel({"kernel": "lean4"}) == "other"

    def test_empty_kernel(self):
        assert classify_kernel({"kernel": ""}) == "other"

    def test_missing_kernel_key(self):
        assert classify_kernel({}) == "other"

    def test_case_insensitive(self):
        assert classify_kernel({"kernel": ".NET (CSHARP)"}) == "dotnet"


# ---------------------------------------------------------------------------
# validate_notebook — basic structure
# ---------------------------------------------------------------------------

class TestValidateNotebookBasic:
    def test_valid_clean_notebook(self, tmp_path):
        """Clean notebook with no issues."""
        nb = _make_notebook(
            [_code_cell("print('hello')", execution_count=1, outputs=[{"output_type": "stream", "text": ["hello\n"]}])],
            kernelspec={"name": ".NET (C#)", "language": "C#"},
        )
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert "error" not in result
        assert result["total_code_cells"] == 1
        assert result["code_with_exec"] == 1
        assert result["issues"]["null_exec_count"] == []
        assert result["issues"]["error_outputs"] == []
        assert result["issues"]["forbidden_patterns"] == []

    def test_markdown_cells_ignored(self, tmp_path):
        """Markdown cells should not be counted as code cells."""
        nb = _make_notebook(
            [_markdown_cell("# Title"), _markdown_cell("text"), _code_cell("x = 1", execution_count=1)],
        )
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["total_code_cells"] == 1

    def test_mixed_cells(self, tmp_path):
        nb = _make_notebook([
            _markdown_cell("# Title"),
            _code_cell("x = 1", execution_count=1),
            _markdown_cell("Explanation"),
            _code_cell("y = 2", execution_count=2),
        ])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["total_code_cells"] == 2
        assert result["code_with_exec"] == 2

    def test_invalid_json(self, tmp_path):
        """Invalid JSON should return error dict."""
        p = tmp_path / "bad.ipynb"
        p.write_text("not valid json {{{", encoding="utf-8")
        result = validate_notebook(str(p))
        assert "error" in result
        assert "Invalid JSON" in result["error"]

    def test_empty_notebook(self, tmp_path):
        """Notebook with no cells."""
        nb = _make_notebook([])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["total_code_cells"] == 0
        assert result["code_with_exec"] == 0


# ---------------------------------------------------------------------------
# validate_notebook — null execution_count
# ---------------------------------------------------------------------------

class TestValidateNullExecCount:
    def test_null_exec_count_flagged(self, tmp_path):
        """Code cell with execution_count=None and non-empty source."""
        nb = _make_notebook([_code_cell("x = 1", execution_count=None)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert len(result["issues"]["null_exec_count"]) == 1

    def test_null_exec_count_empty_source_not_flagged(self, tmp_path):
        """Empty source cell with null exec_count should not be flagged."""
        nb = _make_notebook([_code_cell("", execution_count=None)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["issues"]["null_exec_count"] == []

    def test_null_exec_count_whitespace_source_not_flagged(self, tmp_path):
        nb = _make_notebook([_code_cell("   \n  ", execution_count=None)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["issues"]["null_exec_count"] == []

    def test_valid_exec_count_not_flagged(self, tmp_path):
        nb = _make_notebook([_code_cell("x = 1", execution_count=1)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["issues"]["null_exec_count"] == []


# ---------------------------------------------------------------------------
# validate_notebook — empty outputs
# ---------------------------------------------------------------------------

class TestValidateEmptyOutputs:
    def test_empty_outputs_flagged(self, tmp_path):
        """Code cell with non-empty source but no outputs."""
        nb = _make_notebook([_code_cell("x = 1", execution_count=1, outputs=[])])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert len(result["issues"]["empty_outputs"]) == 1

    def test_with_outputs_not_flagged(self, tmp_path):
        nb = _make_notebook([_code_cell("print('hi')", execution_count=1, outputs=[{"output_type": "stream", "text": ["hi\n"]}])])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["issues"]["empty_outputs"] == []

    def test_empty_source_empty_outputs_not_flagged(self, tmp_path):
        """Empty source with empty outputs = not flagged."""
        nb = _make_notebook([_code_cell("", execution_count=1)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["issues"]["empty_outputs"] == []


# ---------------------------------------------------------------------------
# validate_notebook — error outputs
# ---------------------------------------------------------------------------

class TestValidateErrorOutputs:
    def test_error_output_flagged(self, tmp_path):
        nb = _make_notebook([_code_cell("1/0", execution_count=1, outputs=[
            {"output_type": "error", "ename": "ZeroDivisionError", "evalue": "division by zero"},
        ])])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert len(result["issues"]["error_outputs"]) == 1
        cell_idx, ename, evalue = result["issues"]["error_outputs"][0]
        assert ename == "ZeroDivisionError"
        assert "division by zero" in evalue

    def test_no_error_not_flagged(self, tmp_path):
        nb = _make_notebook([_code_cell("x = 1", execution_count=1, outputs=[
            {"output_type": "execute_result", "data": {"text/plain": ["1"]}},
        ])])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["issues"]["error_outputs"] == []

    def test_multiple_errors_only_first_per_cell(self, tmp_path):
        """Only first error output per cell is recorded."""
        nb = _make_notebook([_code_cell("bad code", execution_count=1, outputs=[
            {"output_type": "error", "ename": "Error1", "evalue": "first"},
            {"output_type": "error", "ename": "Error2", "evalue": "second"},
        ])])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert len(result["issues"]["error_outputs"]) == 1
        assert result["issues"]["error_outputs"][0][1] == "Error1"


# ---------------------------------------------------------------------------
# validate_notebook — forbidden patterns (C.1 compliance)
# ---------------------------------------------------------------------------

class TestValidateForbiddenPatterns:
    def test_raise_not_implemented_error(self, tmp_path):
        nb = _make_notebook([_code_cell("raise NotImplementedError('TODO')", execution_count=1)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert len(result["issues"]["forbidden_patterns"]) == 1
        assert "raise NotImplementedError" in result["issues"]["forbidden_patterns"][0][1]

    def test_assert_false(self, tmp_path):
        nb = _make_notebook([_code_cell("assert False, 'not done'", execution_count=1)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert len(result["issues"]["forbidden_patterns"]) == 1
        assert "assert False" in result["issues"]["forbidden_patterns"][0][1]

    def test_division_by_zero_literal(self, tmp_path):
        nb = _make_notebook([_code_cell("x = 1/0", execution_count=1)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert len(result["issues"]["forbidden_patterns"]) == 1
        assert "1/0" in result["issues"]["forbidden_patterns"][0][1]

    def test_division_by_zero_with_spaces(self, tmp_path):
        """1 / 0 should also be caught."""
        nb = _make_notebook([_code_cell("x = 1 / 0", execution_count=1)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert len(result["issues"]["forbidden_patterns"]) == 1

    def test_comment_with_1_slash_0_triggers(self, tmp_path):
        """# ... 1/0 in a comment DOES trigger — the regex doesn't exclude # comments with spaces."""
        nb = _make_notebook([_code_cell("# This evaluates 1/0 to test", execution_count=1)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        # The regex (?<![#\w])1\s*/\s*0(?!\w) does NOT match because '#' before '1'
        # is checked via lookbehind (?<![#\w]), but '# This evaluates ' has a space
        # between '#' and '1/0', so the lookbehind checks 's' (from 'evaluates ')
        # which passes the negative lookbehind. The regex DOES match.
        assert len(result["issues"]["forbidden_patterns"]) == 1

    def test_inline_comment_1_slash_0_not_triggered(self, tmp_path):
        """#1/0 (no space) should NOT trigger due to lookbehind (?<![#])."""
        nb = _make_notebook([_code_cell("#1/0", execution_count=1)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["issues"]["forbidden_patterns"] == []

    def test_not_triggered_by_10(self, tmp_path):
        """10 (number ten) should NOT trigger 1/0 regex."""
        nb = _make_notebook([_code_cell("x = 10", execution_count=1)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["issues"]["forbidden_patterns"] == []

    def test_not_triggered_by_100(self, tmp_path):
        """100 should NOT trigger 1/0 regex."""
        nb = _make_notebook([_code_cell("x = 100", execution_count=1)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["issues"]["forbidden_patterns"] == []

    def test_multiple_forbidden_in_one_cell(self, tmp_path):
        nb = _make_notebook([_code_cell("raise NotImplementedError()\nassert False", execution_count=1)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert len(result["issues"]["forbidden_patterns"]) == 1
        cell_idx, patterns = result["issues"]["forbidden_patterns"][0]
        assert len(patterns) == 2

    def test_clean_code_no_forbidden(self, tmp_path):
        nb = _make_notebook([_code_cell("x = 42\nprint(x)", execution_count=1)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["issues"]["forbidden_patterns"] == []


# ---------------------------------------------------------------------------
# validate_notebook — kernel metadata
# ---------------------------------------------------------------------------

class TestValidateKernelMetadata:
    def test_kernel_extracted(self, tmp_path):
        nb = _make_notebook([_code_cell("x=1", execution_count=1)], kernelspec={"name": ".NET (C#)", "language": "C#"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["kernel"] == ".NET (C#)"
        assert result["kernel_lang"] == "C#"

    def test_no_kernelspec(self, tmp_path):
        nb = _make_notebook([_code_cell("x=1", execution_count=1)])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["kernel"] == "unknown"
        assert result["kernel_lang"] == "unknown"


# ---------------------------------------------------------------------------
# validate_notebook — multiple cells with mixed issues
# ---------------------------------------------------------------------------

class TestValidateMultipleCells:
    def test_mixed_issues_across_cells(self, tmp_path):
        nb = _make_notebook([
            _code_cell("clean = True", execution_count=1, outputs=[{"output_type": "stream", "text": ["ok"]}]),
            _code_cell("raise NotImplementedError()", execution_count=2, outputs=[]),  # forbidden + empty outputs
            _code_cell("not_executed = True", execution_count=None),  # null exec count
            _markdown_cell("text"),
            _code_cell("bad = 1/0", execution_count=3, outputs=[
                {"output_type": "error", "ename": "ZeroDivisionError", "evalue": "division by zero"},
            ]),  # forbidden + error
        ])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["total_code_cells"] == 4
        # Cell 1: forbidden (raise NotImplementedError) + empty_outputs
        assert len(result["issues"]["forbidden_patterns"]) == 2  # cell 1 and cell 3
        assert len(result["issues"]["empty_outputs"]) >= 1
        # Cell 2: null exec count
        assert len(result["issues"]["null_exec_count"]) == 1
        # Cell 3: forbidden (1/0) + error
        assert len(result["issues"]["error_outputs"]) == 1
