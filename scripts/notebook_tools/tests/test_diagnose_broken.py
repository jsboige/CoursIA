"""Tests for scripts/notebook_tools/diagnose_broken.py — BROKEN notebook diagnostic.

Tests focus on pure functions: extract_errors, is_template, error classification
via ERROR_PATTERNS, and generate_report. No filesystem I/O on production files.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from diagnose_broken import (
    ERROR_PATTERNS,
    extract_errors,
    generate_report,
    is_template,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_notebook(cells):
    """Build a minimal notebook dict."""
    return {"cells": cells, "metadata": {}, "nbformat": 4}


def _code_cell_with_error(ename, evalue, traceback=None):
    """Build a code cell with an error output."""
    return {
        "cell_type": "code",
        "source": ["bad code"],
        "execution_count": 1,
        "outputs": [
            {
                "output_type": "error",
                "ename": ename,
                "evalue": evalue,
                "traceback": traceback or [f"{ename}: {evalue}"],
            }
        ],
        "metadata": {},
    }


def _code_cell_ok():
    """Build a code cell with successful output."""
    return {
        "cell_type": "code",
        "source": ["x = 1"],
        "execution_count": 1,
        "outputs": [{"output_type": "execute_result", "data": {"text/plain": ["1"]}}],
        "metadata": {},
    }


def _markdown_cell():
    return {"cell_type": "markdown", "source": ["# Title"], "metadata": {}}


# ---------------------------------------------------------------------------
# extract_errors
# ---------------------------------------------------------------------------

class TestExtractErrors:
    def test_no_errors(self):
        nb = _make_notebook([_code_cell_ok()])
        assert extract_errors(nb) == []

    def test_single_error(self):
        nb = _make_notebook([_code_cell_with_error("ImportError", "No module named 'foo'")])
        errors = extract_errors(nb)
        assert len(errors) == 1
        assert errors[0]["ename"] == "ImportError"
        assert "foo" in errors[0]["evalue"]

    def test_multiple_errors(self):
        nb = _make_notebook([
            _code_cell_with_error("TypeError", "bad type"),
            _code_cell_ok(),
            _code_cell_with_error("ValueError", "bad value"),
        ])
        errors = extract_errors(nb)
        assert len(errors) == 2

    def test_markdown_cells_ignored(self):
        nb = _make_notebook([_markdown_cell()])
        assert extract_errors(nb) == []

    def test_empty_notebook(self):
        assert extract_errors({"cells": []}) == []

    def test_error_with_traceback(self):
        tb = ["Traceback (most recent call last):", "  File ...", "ImportError: bad"]
        nb = _make_notebook([_code_cell_with_error("ImportError", "bad", traceback=tb)])
        errors = extract_errors(nb)
        assert len(errors) == 1
        assert "Traceback" in errors[0]["traceback"]

    def test_non_error_output_ignored(self):
        """Stream outputs should not be treated as errors."""
        cell = {
            "cell_type": "code",
            "source": ["print('hi')"],
            "execution_count": 1,
            "outputs": [{"output_type": "stream", "name": "stdout", "text": ["hi\n"]}],
            "metadata": {},
        }
        nb = _make_notebook([cell])
        assert extract_errors(nb) == []


# ---------------------------------------------------------------------------
# is_template
# ---------------------------------------------------------------------------

class TestIsTemplate:
    def test_template_in_path(self):
        assert is_template({"path": "SomeDir/template_notebook.ipynb"})

    def test_squelette_in_path(self):
        assert is_template({"path": "serie/squelette_base.ipynb"})

    def test_template_case_insensitive(self):
        assert is_template({"path": "dir/Template_thing.ipynb"})

    def test_normal_path(self):
        assert not is_template({"path": "Search/Search-1-Intro.ipynb"})

    def test_empty_path(self):
        assert not is_template({"path": ""})


# ---------------------------------------------------------------------------
# Error classification (via ERROR_PATTERNS)
# ---------------------------------------------------------------------------

class TestErrorPatterns:
    """Test that ERROR_PATTERNS correctly classify error messages."""

    def _classify(self, ename, evalue, traceback_text=""):
        """Classify an error by running through ERROR_PATTERNS."""
        import re
        text = f"{ename}\n{evalue}\n{traceback_text}"
        for pattern, category in ERROR_PATTERNS:
            if re.search(pattern, text, re.IGNORECASE):
                return category
        return "UNKNOWN"

    def test_import_error(self):
        assert self._classify("ImportError", "No module named 'torch'") == "MISSING_DEP"

    def test_module_not_found(self):
        assert self._classify("ModuleNotFoundError", "No module named 'langchain'") == "MISSING_DEP"

    def test_cannot_import_name(self):
        assert self._classify("ImportError", "cannot import name 'Chat'") == "MISSING_DEP"

    def test_dll_load_failed(self):
        """Pattern requires 'OSError' in ename AND 'cannot load library' in the combined text."""
        # The regex is r"OSError.*cannot load library|DLL load failed"
        # It needs "OSError" followed by "cannot load library" in the full text
        assert self._classify("OSError", "OSError: cannot load library libfoo.so") == "MISSING_DEP"

    def test_dll_load_failed_alt(self):
        """Alternative DLL load failed pattern."""
        assert self._classify("ImportError", "DLL load failed while importing foo") == "MISSING_DEP"

    def test_kernel_not_found(self):
        assert self._classify("RuntimeError", "Kernel not found: .NET") == "KERNEL_ERROR"

    def test_csharp_kernel(self):
        assert self._classify("Exception", "C# kernel not available") == "KERNEL_ERROR"

    def test_api_key_openai(self):
        assert self._classify("OpenAIError", "The api_key client option") == "API_KEY"

    def test_api_key_401(self):
        assert self._classify("HTTPError", "401 Unauthorized") == "API_KEY"

    def test_api_key_403(self):
        assert self._classify("HTTPError", "403 Forbidden") == "API_KEY"

    def test_file_not_found(self):
        assert self._classify("FileNotFoundError", "No such file or directory") == "RUNTIME_ERROR"

    def test_type_error(self):
        assert self._classify("TypeError", "unsupported operand") == "RUNTIME_ERROR"

    def test_value_error(self):
        assert self._classify("ValueError", "invalid literal") == "RUNTIME_ERROR"

    def test_syntax_error(self):
        assert self._classify("SyntaxError", "invalid syntax") == "RUNTIME_ERROR"

    def test_zero_division(self):
        assert self._classify("ZeroDivisionError", "division by zero") == "RUNTIME_ERROR"

    def test_cuda_oom(self):
        assert self._classify("RuntimeError", "CUDA out of memory") == "RUNTIME_ERROR"

    def test_timeout(self):
        assert self._classify("TimeoutError", "timed out") == "RUNTIME_ERROR"

    def test_connection_refused(self):
        assert self._classify("ConnectionError", "Connection refused") == "RUNTIME_ERROR"

    def test_compilation_error(self):
        assert self._classify("Exception", "compilation error in lean") == "KERNEL_ERROR"

    def test_system_exception(self):
        assert self._classify("System.NullReferenceException", "Object reference not set") == "KERNEL_ERROR"

    def test_unknown_error(self):
        assert self._classify("CustomError", "something weird") == "UNKNOWN"

    def test_api_key_preferred_over_missing_dep(self):
        """When both patterns match, API_KEY should be preferred (diagnose_notebook logic)."""
        # In diagnose_notebook, if API_KEY in all_causes -> prefer API_KEY
        # This tests that the PATTERN itself matches API_KEY
        assert self._classify("OpenAIError", "api_key not set") == "API_KEY"

    def test_patterns_order_first_match_wins(self):
        """ERROR_PATTERNS is ordered — first match wins."""
        import re
        # "cannot import name" matches MISSING_DEP pattern before RUNTIME_ERROR
        text = "ImportError\ncannot import name 'foo'"
        categories = []
        for pattern, category in ERROR_PATTERNS:
            if re.search(pattern, text, re.IGNORECASE):
                categories.append(category)
        # Should match MISSING_DEP first
        assert categories[0] == "MISSING_DEP"


# ---------------------------------------------------------------------------
# generate_report
# ---------------------------------------------------------------------------

class TestGenerateReport:
    def test_empty_results(self):
        report = generate_report([])
        assert "BROKEN Notebooks Diagnostic" in report
        assert "TOTAL** | **0**" in report

    def test_single_result(self):
        results = [{
            "path": "Search/Search-1.ipynb",
            "serie": "Search",
            "kernel": "python3",
            "root_cause": "MISSING_DEP",
            "num_errors": 1,
            "errors": [{"ename": "ImportError", "evalue": "No module named 'foo'"}],
        }]
        report = generate_report(results)
        assert "MISSING_DEP" in report
        assert "1" in report
        assert "Search" in report

    def test_multiple_root_causes(self):
        results = [
            {"path": "a.ipynb", "serie": "Search", "root_cause": "MISSING_DEP", "num_errors": 1, "errors": []},
            {"path": "b.ipynb", "serie": "GameTheory", "root_cause": "API_KEY", "num_errors": 1, "errors": []},
            {"path": "c.ipynb", "serie": "Search", "root_cause": "RUNTIME_ERROR", "num_errors": 2, "errors": []},
        ]
        report = generate_report(results)
        assert "MISSING_DEP" in report
        assert "API_KEY" in report
        assert "RUNTIME_ERROR" in report
        assert "**3**" in report  # total

    def test_summary_only_no_details(self):
        results = [
            {"path": "a.ipynb", "serie": "Search", "root_cause": "MISSING_DEP", "num_errors": 1, "errors": []},
        ]
        report = generate_report(results, summary_only=True)
        assert "MISSING_DEP" in report
        # Should NOT have per-notebook detail section
        assert "| Search | a.ipynb |" not in report

    def test_full_report_has_details(self):
        results = [
            {"path": "a.ipynb", "serie": "Search", "root_cause": "MISSING_DEP", "num_errors": 1,
             "errors": [{"ename": "ImportError", "evalue": "No module named 'foo'"}]},
        ]
        report = generate_report(results, summary_only=False)
        assert "MISSING_DEP (1 notebooks)" in report
        assert "ImportError" in report

    def test_serie_grouping(self):
        results = [
            {"path": "a.ipynb", "serie": "Search", "root_cause": "MISSING_DEP", "num_errors": 1, "errors": []},
            {"path": "b.ipynb", "serie": "Search", "root_cause": "RUNTIME_ERROR", "num_errors": 1, "errors": []},
            {"path": "c.ipynb", "serie": "Sudoku", "root_cause": "MISSING_DEP", "num_errors": 1, "errors": []},
        ]
        report = generate_report(results)
        assert "Search | 2" in report
        assert "Sudoku | 1" in report

    def test_unknown_cause_included(self):
        results = [
            {"path": "x.ipynb", "serie": "Test", "root_cause": "WEIRD_CAUSE", "num_errors": 0, "errors": []},
        ]
        report = generate_report(results)
        assert "WEIRD_CAUSE" in report

    def test_error_detail_truncated(self):
        """Error evalue in detail is truncated to 60 chars."""
        long_msg = "A" * 200
        results = [{
            "path": "x.ipynb", "serie": "Test", "root_cause": "RUNTIME_ERROR", "num_errors": 1,
            "errors": [{"ename": "ValueError", "evalue": long_msg}],
        }]
        report = generate_report(results, summary_only=False)
        # The detail in the table should be truncated
        assert "ValueError" in report
        # Should not contain the full 200-char string
        assert long_msg not in report
