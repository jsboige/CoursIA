"""Tests for scripts/notebook_tools/validate_pr_notebooks.py — PR notebook validation.

Tests focus on: get_kernel_name, validate_notebook (H.1/H.3/C.1 checks),
and SKIP_EXEC_KERNELS / QC_CLOUD_PATHS behavior. Uses tmp_path fixtures.
No filesystem I/O on production files.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
from validate_pr_notebooks import (
    QC_CLOUD_PATHS,
    SKIP_EXEC_KERNELS,
    get_kernel_name,
    validate_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_nb(cells, kernelspec=None, nbformat=4):
    """Build a minimal .ipynb dict."""
    nb = {"nbformat": nbformat, "nbformat_minor": 5, "metadata": {}, "cells": cells}
    if kernelspec:
        nb["metadata"]["kernelspec"] = kernelspec
    return nb


def _code_cell(source, execution_count=1, outputs=None):
    """Build a code cell."""
    return {
        "cell_type": "code",
        "source": [source] if isinstance(source, str) else source,
        "execution_count": execution_count,
        "outputs": outputs or [],
        "metadata": {},
    }


def _md_cell(source):
    """Build a markdown cell."""
    return {
        "cell_type": "markdown",
        "source": [source] if isinstance(source, str) else source,
        "metadata": {},
    }


def _write_nb(tmp_path, nb_dict, name="test.ipynb"):
    """Write notebook dict to temp file and return Path."""
    p = tmp_path / name
    p.write_text(json.dumps(nb_dict), encoding="utf-8")
    return p


# ---------------------------------------------------------------------------
# get_kernel_name
# ---------------------------------------------------------------------------

class TestGetKernelName:
    def test_python3_kernel(self, tmp_path):
        nb = _make_nb([], kernelspec={"name": "python3", "language": "python"})
        path = _write_nb(tmp_path, nb)
        assert get_kernel_name(path) == "python3"

    def test_dotnet_csharp(self, tmp_path):
        nb = _make_nb([], kernelspec={"name": ".net-csharp", "language": "C#"})
        path = _write_nb(tmp_path, nb)
        assert get_kernel_name(path) == ".net-csharp"

    def test_lean4(self, tmp_path):
        nb = _make_nb([], kernelspec={"name": "lean4", "language": "lean"})
        path = _write_nb(tmp_path, nb)
        assert get_kernel_name(path) == "lean4"

    def test_no_kernelspec_defaults_python3(self, tmp_path):
        nb = _make_nb([])
        path = _write_nb(tmp_path, nb)
        assert get_kernel_name(path) == "python3"

    def test_invalid_json(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        p.write_text("not json {{{", encoding="utf-8")
        assert get_kernel_name(p) == "unknown"


# ---------------------------------------------------------------------------
# validate_notebook — clean notebook
# ---------------------------------------------------------------------------

class TestValidateClean:
    def test_clean_python_notebook(self, tmp_path):
        nb = _make_nb([
            _code_cell("x = 1\nprint(x)", execution_count=1,
                       outputs=[{"output_type": "stream", "text": ["1"]}]),
        ], kernelspec={"name": "python3"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is True
        assert result["total_code"] == 1
        assert result["errors"] == []

    def test_clean_dotnet_notebook(self, tmp_path):
        """Clean .NET notebook — execution_count null is advisory (skip_exec)."""
        nb = _make_nb([
            _code_cell("Console.WriteLine(\"hi\")", execution_count=1,
                       outputs=[{"output_type": "stream", "text": ["hi"]}]),
        ], kernelspec={"name": ".net-csharp"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is True

    def test_empty_notebook(self, tmp_path):
        nb = _make_nb([])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is True
        assert result["total_code"] == 0

    def test_markdown_only(self, tmp_path):
        nb = _make_nb([_md_cell("# Title"), _md_cell("Content")])
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is True
        assert result["total_code"] == 0


# ---------------------------------------------------------------------------
# validate_notebook — H.3: execution_count null
# ---------------------------------------------------------------------------

class TestValidateH3:
    def test_null_exec_count_python_fails(self, tmp_path):
        """Python kernel: null exec_count = H.3 violation."""
        nb = _make_nb([
            _code_cell("x = 42", execution_count=None),
        ], kernelspec={"name": "python3"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is False
        assert any("H.3" in e for e in result["errors"])

    def test_null_exec_count_dotnet_passes(self, tmp_path):
        """Dotnet kernel: null exec_count is not an error (skip_exec)."""
        nb = _make_nb([
            _code_cell("Console.WriteLine(\"hi\")", execution_count=None),
        ], kernelspec={"name": ".net-csharp"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is True

    def test_null_exec_count_lean_passes(self, tmp_path):
        """Lean kernel: null exec_count is not an error (skip_exec)."""
        nb = _make_nb([
            _code_cell("#check Nat", execution_count=None),
        ], kernelspec={"name": "lean4"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is True

    def test_empty_source_not_counted(self, tmp_path):
        """Empty source cell is skipped."""
        nb = _make_nb([
            _code_cell("", execution_count=None),
        ], kernelspec={"name": "python3"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["total_code"] == 0
        assert result["passed"] is True

    def test_comment_only_cell_skipped(self, tmp_path):
        """Comment-only code cell is skipped."""
        nb = _make_nb([
            _code_cell("# Just a comment\n# Another comment", execution_count=None),
        ], kernelspec={"name": "python3"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["total_code"] == 0
        assert result["passed"] is True


# ---------------------------------------------------------------------------
# validate_notebook — H.1: error outputs
# ---------------------------------------------------------------------------

class TestValidateH1:
    def test_error_output_python_fails(self, tmp_path):
        """Python kernel: error output = H.1 violation."""
        nb = _make_nb([
            _code_cell("1/0", execution_count=1, outputs=[
                {"output_type": "error", "ename": "ZeroDivisionError", "evalue": "division by zero"},
            ]),
        ], kernelspec={"name": "python3"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is False
        assert any("ZeroDivisionError" in e for e in result["errors"])

    def test_error_output_dotnet_advisory(self, tmp_path):
        """Dotnet kernel: error output is advisory (not a fail)."""
        nb = _make_nb([
            _code_cell("bad code", execution_count=1, outputs=[
                {"output_type": "error", "ename": "Error", "evalue": "bad"},
            ]),
        ], kernelspec={"name": ".net-csharp"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        # Dotnet skip_exec, so error is advisory (not passed=False)
        assert result["passed"] is True
        # But advisory error is still reported
        assert any("advisory" in e.lower() for e in result["errors"])

    def test_no_error_output_passes(self, tmp_path):
        nb = _make_nb([
            _code_cell("x = 1", execution_count=1, outputs=[
                {"output_type": "execute_result", "data": {"text/plain": ["1"]}},
            ]),
        ], kernelspec={"name": "python3"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is True

    def test_stream_output_not_error(self, tmp_path):
        nb = _make_nb([
            _code_cell("print('hi')", execution_count=1, outputs=[
                {"output_type": "stream", "name": "stdout", "text": ["hi\n"]},
            ]),
        ], kernelspec={"name": "python3"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is True


# ---------------------------------------------------------------------------
# validate_notebook — C.1: forbidden patterns
# ---------------------------------------------------------------------------

class TestValidateC1:
    def test_raise_not_implemented_error(self, tmp_path):
        """raise NotImplementedError is a C.1 violation."""
        nb = _make_nb([
            _code_cell("def foo():\n    raise NotImplementedError('TODO')", execution_count=1),
        ], kernelspec={"name": "python3"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is False
        assert any("C.1" in e for e in result["errors"])

    def test_assert_false(self, tmp_path):
        nb = _make_nb([
            _code_cell("assert False", execution_count=1),
        ], kernelspec={"name": "python3"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is False
        assert any("C.1" in e for e in result["errors"])

    def test_clean_code_passes(self, tmp_path):
        nb = _make_nb([
            _code_cell("x = 42\nprint(x)", execution_count=1,
                       outputs=[{"output_type": "stream", "text": ["42"]}]),
        ], kernelspec={"name": "python3"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is True

    def test_c1_violation_in_dotnet_also_fails(self, tmp_path):
        """C.1 violations are checked for ALL kernels (not skip_exec)."""
        nb = _make_nb([
            _code_cell("raise NotImplementedError()", execution_count=1),
        ], kernelspec={"name": ".net-csharp"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is False

    def test_date_not_false_positive(self, tmp_path):
        """Date '21/02/2022' should NOT trigger C.1 (digit-bounded regex)."""
        nb = _make_nb([
            _code_cell('date = "21/02/2022"', execution_count=1),
        ], kernelspec={"name": "python3"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is True


# ---------------------------------------------------------------------------
# validate_notebook — QC Cloud paths
# ---------------------------------------------------------------------------

class TestValidateQCCloud:
    def test_qc_cloud_null_exec_advisory(self, tmp_path):
        """QC Cloud notebook: null exec_count is advisory (path-based skip)."""
        nb = _make_nb([
            _code_cell("qb = QuantBook()", execution_count=None),
        ], kernelspec={"name": "python3"})
        path = tmp_path / "QuantConnect" / "Python" / "test.ipynb"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(nb), encoding="utf-8")
        result = validate_notebook(path)
        # QC Cloud path triggers skip_exec → no H.3 violation
        assert result["passed"] is True

    def test_qc_cloud_error_advisory(self, tmp_path):
        """QC Cloud notebook: error outputs are advisory (not hard fail)."""
        nb = _make_nb([
            _code_cell("qb = QuantBook()", execution_count=1, outputs=[
                {"output_type": "error", "ename": "NameError", "evalue": "QuantBook not defined"},
            ]),
        ], kernelspec={"name": "python3"})
        path = tmp_path / "QuantConnect" / "projects" / "test.ipynb"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(nb), encoding="utf-8")
        result = validate_notebook(path)
        # QC Cloud skip_exec → error is advisory
        assert result["passed"] is True


# ---------------------------------------------------------------------------
# validate_notebook — invalid input
# ---------------------------------------------------------------------------

class TestValidateInvalid:
    def test_invalid_json(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        p.write_text("not json {{{", encoding="utf-8")
        result = validate_notebook(p)
        assert result["passed"] is False
        assert any("Cannot parse" in e for e in result["errors"])

    def test_mixed_issues(self, tmp_path):
        """Notebook with C.1 + H.3 + H.1 violations."""
        nb = _make_nb([
            _code_cell("raise NotImplementedError()", execution_count=None),
            _code_cell("1/0", execution_count=1, outputs=[
                {"output_type": "error", "ename": "ZeroDivisionError", "evalue": "/ by zero"},
            ]),
        ], kernelspec={"name": "python3"})
        path = _write_nb(tmp_path, nb)
        result = validate_notebook(path)
        assert result["passed"] is False
        assert any("C.1" in e for e in result["errors"])
        assert any("H.3" in e for e in result["errors"])
        assert any("ZeroDivisionError" in e for e in result["errors"])


# ---------------------------------------------------------------------------
# SKIP_EXEC_KERNELS / QC_CLOUD_PATHS constants
# ---------------------------------------------------------------------------

class TestConstants:
    def test_skip_exec_kernels_contains_dotnet(self):
        assert ".net-csharp" in SKIP_EXEC_KERNELS
        assert ".net-fsharp" in SKIP_EXEC_KERNELS

    def test_skip_exec_kernels_contains_lean(self):
        assert "lean4" in SKIP_EXEC_KERNELS
        assert "lean" in SKIP_EXEC_KERNELS

    def test_qc_cloud_paths(self):
        assert "QuantConnect/Python" in QC_CLOUD_PATHS
        assert "QuantConnect/projects" in QC_CLOUD_PATHS
