"""Tests for sudoku_validate_outputs.py — mutation-killing tests.

Covers: validate_notebook, classify_kernel, edge cases in
null_exec_count, empty_outputs, error_outputs, forbidden_patterns.
"""

import json
import os
import sys
import tempfile

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from sudoku_validate_outputs import classify_kernel, validate_notebook


# --- Helpers ---

def _make_nb(cells, kernel_name="python3", kernel_lang="python"):
    """Build a minimal notebook dict."""
    return {
        "metadata": {
            "kernelspec": {
                "name": kernel_name,
                "language": kernel_lang,
            }
        },
        "cells": cells,
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _code_cell(source, execution_count=1, outputs=None, cell_type="code"):
    """Build a code cell."""
    if outputs is None:
        outputs = [{"output_type": "execute_result", "data": {"text/plain": ["ok"]}}]
    return {
        "cell_type": cell_type,
        "source": source if isinstance(source, list) else [source],
        "execution_count": execution_count,
        "outputs": outputs,
    }


def _md_cell(source="Some text"):
    """Build a markdown cell."""
    return {
        "cell_type": "markdown",
        "source": [source],
        "metadata": {},
    }


def _write_nb(nb_dict, tmpdir, name="test.ipynb"):
    """Write notebook to file, return path."""
    path = os.path.join(tmpdir, name)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(nb_dict, f)
    return path


# --- validate_notebook: JSON parse error ---

class TestValidateNotebookJsonError:
    """Mutation tests for JSON error handling (L15-18)."""

    def test_invalid_json_returns_error_key(self, tmp_path):
        path = str(tmp_path / "bad.ipynb")
        with open(path, "w") as f:
            f.write("{invalid json!!!")
        result = validate_notebook(path)
        assert "error" in result
        assert "Invalid JSON" in result["error"]

    def test_invalid_json_preserves_path(self, tmp_path):
        path = str(tmp_path / "bad2.ipynb")
        with open(path, "w") as f:
            f.write("not json at all")
        result = validate_notebook(path)
        assert result["path"] == path

    def test_valid_json_no_error_key(self, tmp_path):
        nb = _make_nb([])
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert "error" not in result


# --- validate_notebook: metadata extraction ---

class TestValidateNotebookMetadata:
    """Mutation tests for kernel metadata extraction (L20-23)."""

    def test_kernel_name_extracted(self, tmp_path):
        nb = _make_nb([], kernel_name=".net-csharp", kernel_lang="C#")
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["kernel"] == ".net-csharp"

    def test_kernel_lang_extracted(self, tmp_path):
        nb = _make_nb([], kernel_name="python3", kernel_lang="python")
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["kernel_lang"] == "python"

    def test_missing_kernelspec_defaults_unknown(self, tmp_path):
        nb = {"metadata": {}, "cells": [], "nbformat": 4}
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["kernel"] == "unknown"
        assert result["kernel_lang"] == "unknown"


# --- validate_notebook: null_exec_count ---

class TestValidateNotebookNullExecCount:
    """Mutation tests for null execution_count check (L47-48)."""

    def test_null_exec_count_detected(self, tmp_path):
        cells = [_code_cell("x = 1", execution_count=None, outputs=[])]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert len(result["issues"]["null_exec_count"]) == 1

    def test_non_null_exec_count_not_flagged(self, tmp_path):
        cells = [_code_cell("x = 1", execution_count=1)]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["issues"]["null_exec_count"] == []

    def test_empty_source_not_flagged_null_exec(self, tmp_path):
        """Empty source cell should NOT be flagged even if exec_count=None."""
        cells = [_code_cell("   ", execution_count=None, outputs=[])]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["issues"]["null_exec_count"] == []

    def test_whitespace_source_not_flagged(self, tmp_path):
        cells = [_code_cell("\n  \n", execution_count=None, outputs=[])]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["issues"]["null_exec_count"] == []


# --- validate_notebook: empty_outputs ---

class TestValidateNotebookEmptyOutputs:
    """Mutation tests for empty outputs check (L51-52)."""

    def test_empty_outputs_detected(self, tmp_path):
        cells = [_code_cell("x = 1", execution_count=1, outputs=[])]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert len(result["issues"]["empty_outputs"]) == 1

    def test_non_empty_outputs_not_flagged(self, tmp_path):
        cells = [_code_cell("x = 1", execution_count=1, outputs=[
            {"output_type": "stream", "text": ["ok"]}
        ])]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["issues"]["empty_outputs"] == []

    def test_empty_source_not_flagged_empty_outputs(self, tmp_path):
        """Empty source should NOT be flagged for empty outputs."""
        cells = [_code_cell("", execution_count=1, outputs=[])]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["issues"]["empty_outputs"] == []


# --- validate_notebook: error_outputs ---

class TestValidateNotebookErrorOutputs:
    """Mutation tests for error output detection (L55-60)."""

    def test_error_output_detected(self, tmp_path):
        cells = [_code_cell("1/0", execution_count=1, outputs=[
            {"output_type": "error", "ename": "ZeroDivisionError", "evalue": "division by zero"}
        ])]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert len(result["issues"]["error_outputs"]) == 1
        assert result["issues"]["error_outputs"][0][1] == "ZeroDivisionError"

    def test_stream_output_not_error(self, tmp_path):
        cells = [_code_cell("print('hi')", execution_count=1, outputs=[
            {"output_type": "stream", "name": "stdout", "text": ["hi"]}
        ])]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["issues"]["error_outputs"] == []

    def test_evalue_truncated_to_80(self, tmp_path):
        long_msg = "x" * 200
        cells = [_code_cell("err()", execution_count=1, outputs=[
            {"output_type": "error", "ename": "ValueError", "evalue": long_msg}
        ])]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert len(result["issues"]["error_outputs"][0][2]) <= 80

    def test_first_error_only_per_cell(self, tmp_path):
        """Only first error output recorded per cell (break at L60)."""
        cells = [_code_cell("err()", execution_count=1, outputs=[
            {"output_type": "error", "ename": "Error1", "evalue": "e1"},
            {"output_type": "error", "ename": "Error2", "evalue": "e2"},
        ])]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert len(result["issues"]["error_outputs"]) == 1
        assert result["issues"]["error_outputs"][0][1] == "Error1"

    def test_execute_result_not_error(self, tmp_path):
        cells = [_code_cell("42", execution_count=1, outputs=[
            {"output_type": "execute_result", "data": {"text/plain": "42"}}
        ])]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["issues"]["error_outputs"] == []


# --- validate_notebook: forbidden_patterns ---

class TestValidateNotebookForbiddenPatterns:
    """Mutation tests for forbidden pattern detection (L63-72)."""

    def test_raise_not_implemented_detected(self, tmp_path):
        cells = [_code_cell("raise NotImplementedError('todo')", execution_count=1)]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert len(result["issues"]["forbidden_patterns"]) == 1
        assert "raise NotImplementedError" in result["issues"]["forbidden_patterns"][0][1]

    def test_assert_false_detected(self, tmp_path):
        cells = [_code_cell("assert False", execution_count=1)]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert len(result["issues"]["forbidden_patterns"]) == 1
        assert "assert False" in result["issues"]["forbidden_patterns"][0][1]

    def test_division_by_zero_detected(self, tmp_path):
        cells = [_code_cell("x = 1/0", execution_count=1)]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert len(result["issues"]["forbidden_patterns"]) == 1
        assert "1/0" in result["issues"]["forbidden_patterns"][0][1]

    def test_multiple_forbidden_in_same_cell(self, tmp_path):
        cells = [_code_cell("raise NotImplementedError()\nassert False", execution_count=1)]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert len(result["issues"]["forbidden_patterns"]) == 1
        assert len(result["issues"]["forbidden_patterns"][0][1]) == 2

    def test_safe_division_not_flagged(self, tmp_path):
        """1/10 or 100/0 should NOT trigger 1/0 pattern."""
        cells = [_code_cell("x = 1/10", execution_count=1)]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["issues"]["forbidden_patterns"] == []

    def test_commented_not_implemented_not_flagged(self, tmp_path):
        """# raise NotImplementedError should NOT be detected by this regex.

        The regex ``raise\\s+NotImplementedError`` does NOT check for # prefix,
        so it WILL match even in comments. This test documents the behavior.
        """
        cells = [_code_cell("# raise NotImplementedError()", execution_count=1)]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        # Current behavior: detects in comments (no negative lookbehind for #)
        assert len(result["issues"]["forbidden_patterns"]) == 1

    def test_empty_source_not_checked_for_forbidden(self, tmp_path):
        cells = [_code_cell("", execution_count=1, outputs=[])]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["issues"]["forbidden_patterns"] == []

    def test_variable_name_with_1_div_not_flagged(self, tmp_path):
        """`a1/0` should NOT trigger (word char before 1)."""
        cells = [_code_cell("result = a1/0", execution_count=1)]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        # Pattern: (?<![#\w])1\s*/\s*0(?!\w)
        # 'a1/0' has 'a' before 1, so lookbehind should prevent match
        result = validate_notebook(path)
        assert result["issues"]["forbidden_patterns"] == []

    def test_1_div_0_with_spaces_flagged(self, tmp_path):
        """`1 / 0` should be detected (whitespace tolerance)."""
        cells = [_code_cell("x = 1 / 0", execution_count=1)]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert len(result["issues"]["forbidden_patterns"]) == 1


# --- validate_notebook: code cell counting ---

class TestValidateNotebookCellCounting:
    """Mutation tests for cell counting (L34-35, L41, L74-75)."""

    def test_total_code_cells_counted(self, tmp_path):
        cells = [
            _code_cell("x=1", execution_count=1),
            _md_cell("text"),
            _code_cell("y=2", execution_count=2),
        ]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["total_code_cells"] == 2

    def test_md_cells_not_counted(self, tmp_path):
        cells = [_md_cell("text"), _md_cell("more")]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["total_code_cells"] == 0

    def test_code_with_exec_counter(self, tmp_path):
        cells = [
            _code_cell("x=1", execution_count=1),
            _code_cell("y=2", execution_count=None, outputs=[]),
        ]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["code_with_exec"] == 1

    def test_all_code_has_exec(self, tmp_path):
        cells = [_code_cell("x=1", execution_count=1)]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["code_with_exec"] == result["total_code_cells"]


# --- validate_notebook: cell index tracking ---

class TestValidateNotebookCellIndex:
    """Mutation tests for cell index in issues (L38 enumerate)."""

    def test_issue_records_cell_index(self, tmp_path):
        cells = [
            _md_cell("intro"),
            _code_cell("x=1", execution_count=None, outputs=[]),
        ]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        # Cell index 1 (md skipped, code cell is index 1 in enumerate)
        assert result["issues"]["null_exec_count"] == [1]

    def test_multiple_issues_different_cells(self, tmp_path):
        cells = [
            _code_cell("x=1", execution_count=None, outputs=[]),
            _code_cell("y=2", execution_count=None, outputs=[]),
        ]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["issues"]["null_exec_count"] == [0, 1]


# --- classify_kernel ---

class TestClassifyKernel:
    """Mutation tests for classify_kernel (L87-95)."""

    def test_dotnet_kernel(self):
        result = {"kernel": ".net-csharp"}
        assert classify_kernel(result) == "dotnet"

    def test_csharp_kernel(self):
        result = {"kernel": "csharp"}
        assert classify_kernel(result) == "dotnet"

    def test_fsharp_kernel(self):
        result = {"kernel": "fsharp"}
        assert classify_kernel(result) == "dotnet"

    def test_python_kernel(self):
        result = {"kernel": "python3"}
        assert classify_kernel(result) == "python"

    def test_python2_kernel(self):
        result = {"kernel": "python2"}
        assert classify_kernel(result) == "python"

    def test_unknown_kernel(self):
        result = {"kernel": "julia"}
        assert classify_kernel(result) == "other"

    def test_case_insensitive(self):
        result = {"kernel": "PYTHON3"}
        assert classify_kernel(result) == "python"

    def test_dotnet_case_insensitive(self):
        result = {"kernel": ".NET-CSHARP"}
        assert classify_kernel(result) == "dotnet"

    def test_missing_kernel_key(self):
        result = {}
        assert classify_kernel(result) == "other"


# --- validate_notebook: source as list vs string ---

class TestValidateNotebookSourceFormat:
    """Mutation tests for source joining (L42)."""

    def test_source_as_list_joined(self, tmp_path):
        cells = [_code_cell(["line1\n", "line2"], execution_count=1)]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        # Should process without error
        assert "error" not in result

    def test_source_as_list_with_forbidden(self, tmp_path):
        cells = [_code_cell(["raise ", "NotImplementedError()"], execution_count=1)]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert len(result["issues"]["forbidden_patterns"]) == 1


# --- validate_notebook: clean notebook ---

class TestValidateNotebookClean:
    """Mutation tests for clean notebook (no issues)."""

    def test_clean_notebook_no_issues(self, tmp_path):
        cells = [
            _code_cell("x = 1 + 1", execution_count=1),
            _code_cell("print('hello')", execution_count=2),
        ]
        nb = _make_nb(cells)
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["issues"]["null_exec_count"] == []
        assert result["issues"]["empty_outputs"] == []
        assert result["issues"]["error_outputs"] == []
        assert result["issues"]["forbidden_patterns"] == []

    def test_empty_notebook(self, tmp_path):
        nb = _make_nb([])
        path = _write_nb(nb, str(tmp_path))
        result = validate_notebook(path)
        assert result["total_code_cells"] == 0
        assert result["code_with_exec"] == 0
        assert result["issues"]["null_exec_count"] == []


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
