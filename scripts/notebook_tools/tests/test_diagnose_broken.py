"""Tests for diagnose_broken.py — error classification and notebook diagnostics."""

import json
import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from diagnose_broken import extract_errors, is_template, generate_report


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
