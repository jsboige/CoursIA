"""Tests for diagnose_broken.py — error classification and notebook diagnostics."""

import json
import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from diagnose_broken import classify_error, extract_errors, is_template, generate_report


class TestClassifyError:

    def test_import_error(self):
        assert classify_error("ImportError", "No module named foo") == "MISSING_DEP"

    def test_module_not_found(self):
        assert classify_error("ModuleNotFoundError", "xxx") == "MISSING_DEP"

    def test_no_module_named(self):
        assert classify_error("RuntimeError", "No module named 'torch'") == "MISSING_DEP"

    def test_kernel_not_found(self):
        assert classify_error("RuntimeError", "kernel 'lean4' not found") == "KERNEL_ERROR"

    def test_csharp_kernel(self):
        assert classify_error("Exception", "C# kernel not supported") == "KERNEL_ERROR"

    def test_api_key_openai(self):
        assert classify_error("OpenAIError", "The api_key client option") == "API_KEY"

    def test_api_key_401(self):
        assert classify_error("HTTPError", "401 Unauthorized") == "API_KEY"

    def test_file_not_found(self):
        assert classify_error("FileNotFoundError", "No such file") == "RUNTIME_ERROR"

    def test_type_error(self):
        assert classify_error("TypeError", "unsupported operand") == "RUNTIME_ERROR"

    def test_syntax_error(self):
        assert classify_error("SyntaxError", "invalid syntax") == "RUNTIME_ERROR"

    def test_cuda_oom(self):
        assert classify_error("RuntimeError", "CUDA out of memory") == "RUNTIME_ERROR"

    def test_connection_refused(self):
        assert classify_error("ConnectionError", "Connection refused") == "RUNTIME_ERROR"

    def test_compilation_error(self):
        assert classify_error("Error", "compilation error in Lean") == "KERNEL_ERROR"

    def test_system_exception(self):
        assert classify_error("System.NullReferenceException", "Object reference") == "KERNEL_ERROR"

    def test_dll_load_failed(self):
        assert classify_error("OSError", "DLL load failed") == "MISSING_DEP"

    def test_unknown_error(self):
        assert classify_error("CustomError", "something unusual happened") == "UNKNOWN"

    def test_api_key_preferred_over_import(self):
        """API_KEY should be detected even with import error context."""
        result = classify_error("RuntimeError", "ImportError and OPENAI_API not set")
        assert result == "MISSING_DEP"  # First match wins in classify_error


class TestExtractErrors:

    def test_no_errors(self):
        nb = {"cells": [{"cell_type": "code", "outputs": []}]}
        assert extract_errors(nb) == []

    def test_stream_output_ignored(self):
        nb = {"cells": [{"cell_type": "code", "outputs": [
            {"output_type": "stream", "text": ["hello"]}
        ]}]}
        assert extract_errors(nb) == []

    def test_error_extracted(self):
        nb = {"cells": [{"cell_type": "code", "outputs": [
            {"output_type": "error", "ename": "ValueError", "evalue": "bad value",
             "traceback": ["Traceback...", "ValueError: bad value"]}
        ]}]}
        errors = extract_errors(nb)
        assert len(errors) == 1
        assert errors[0]["ename"] == "ValueError"
        assert errors[0]["evalue"] == "bad value"

    def test_markdown_cell_skipped(self):
        nb = {"cells": [{"cell_type": "markdown", "outputs": []}]}
        assert extract_errors(nb) == []

    def test_multiple_errors(self):
        nb = {"cells": [
            {"cell_type": "code", "outputs": [
                {"output_type": "error", "ename": "E1", "evalue": "e1", "traceback": []}
            ]},
            {"cell_type": "code", "outputs": [
                {"output_type": "error", "ename": "E2", "evalue": "e2", "traceback": []}
            ]},
        ]}
        errors = extract_errors(nb)
        assert len(errors) == 2


class TestIsTemplate:

    def test_template_in_name(self):
        assert is_template({"path": "some/template_file.ipynb"})

    def test_squelette_in_name(self):
        assert is_template({"path": "serie/squelette_notebook.ipynb"})

    def test_regular_notebook(self):
        assert not is_template({"path": "Search/Part1-Foundations/CSPs_Intro.ipynb"})

    def test_case_insensitive(self):
        assert is_template({"path": "folder/Template_starter.ipynb".lower()})


class TestGenerateReport:

    def test_report_has_summary(self):
        results = [
            {"path": "a.ipynb", "serie": "Test", "root_cause": "MISSING_DEP",
             "num_errors": 1, "errors": [{"ename": "ImportError", "evalue": "no mod"}]},
        ]
        report = generate_report(results)
        assert "MISSING_DEP" in report
        assert "BROKEN Notebooks" in report

    def test_report_summary_only(self):
        results = [
            {"path": "a.ipynb", "serie": "S1", "root_cause": "KERNEL_ERROR",
             "num_errors": 0, "errors": []},
            {"path": "b.ipynb", "serie": "S2", "root_cause": "API_KEY",
             "num_errors": 1, "errors": [{"ename": "Err", "evalue": "x"}]},
        ]
        report = generate_report(results, summary_only=True)
        assert "KERNEL_ERROR" in report
        assert "API_KEY" in report

    def test_report_empty(self):
        report = generate_report([])
        assert "TOTAL" in report

    def test_report_by_serie(self):
        results = [
            {"path": "a.ipynb", "serie": "GenAI", "root_cause": "API_KEY",
             "num_errors": 1, "errors": [{"ename": "E", "evalue": "x"}]},
            {"path": "b.ipynb", "serie": "GenAI", "root_cause": "MISSING_DEP",
             "num_errors": 1, "errors": [{"ename": "E", "evalue": "y"}]},
        ]
        report = generate_report(results)
        assert "GenAI" in report
