"""Tests for check_c2_compliance.py — C.2 compliance checker."""

import json
import sys
import tempfile
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_c2_compliance import check_notebook


def _write_nb(cells, tmp_path, name="test.ipynb"):
    """Write a notebook dict to a temp file and return its Path."""
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


def _code(source, execution_count=1, outputs=None):
    """Build a code cell."""
    if isinstance(source, str):
        source = [source + "\n"]
    return {
        "cell_type": "code",
        "source": source,
        "execution_count": execution_count,
        "outputs": outputs or [],
    }


def _md(source):
    """Build a markdown cell."""
    if isinstance(source, str):
        source = [source + "\n"]
    return {"cell_type": "markdown", "source": source}


def _stream_output(text="hello"):
    return {"output_type": "stream", "name": "stdout", "text": [text]}


# --- check_notebook ---

class TestCheckNotebook:
    def test_compliant_notebook(self, tmp_path):
        p = _write_nb([_code("print('hello')", 1, [_stream_output()])], tmp_path)
        result = check_notebook(p)
        assert result["violations"] == []
        assert result["total_code"] == 1

    def test_missing_execution_count(self, tmp_path):
        cell = _code("x = 1")
        cell["execution_count"] = None
        p = _write_nb([cell], tmp_path)
        result = check_notebook(p)
        assert len(result["violations"]) == 1
        assert result["violations"][0]["reason"] == "missing execution_count"

    def test_empty_code_cell_skipped(self, tmp_path):
        p = _write_nb([_code("", 1, [])], tmp_path)
        result = check_notebook(p)
        assert result["violations"] == []

    def test_comment_only_cell_skipped(self, tmp_path):
        p = _write_nb([_code("# just a comment", 1, [])], tmp_path)
        result = check_notebook(p)
        assert result["violations"] == []

    def test_import_no_output_ok(self, tmp_path):
        p = _write_nb([_code("import os", 1, [])], tmp_path)
        result = check_notebook(p)
        assert result["violations"] == []

    def test_print_no_output_flagged(self, tmp_path):
        p = _write_nb([_code("print('hello')", 1, [])], tmp_path)
        result = check_notebook(p)
        assert len(result["violations"]) == 1
        assert "no outputs" in result["violations"][0]["reason"]

    def test_markdown_cell_ignored(self, tmp_path):
        p = _write_nb([_md("# Title"), _code("x = 1", 1, [_stream_output()])], tmp_path)
        result = check_notebook(p)
        assert result["violations"] == []
        assert result["total_code"] == 1

    def test_invalid_json(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        p.write_text("not json{{{{", encoding="utf-8")
        result = check_notebook(p)
        assert len(result["violations"]) == 1
        assert "Cannot parse" in result["violations"][0]["error"]

    def test_empty_notebook(self, tmp_path):
        p = _write_nb([], tmp_path)
        result = check_notebook(p)
        assert result["violations"] == []
        assert result["total_code"] == 0

    def test_multiple_violations(self, tmp_path):
        cells = [
            _code("print('a')", 1, []),        # violation: print, no output
            _code("import os", 2, []),          # OK: import
            _code("x = None", None, []),        # violation: missing exec_count
        ]
        p = _write_nb(cells, tmp_path)
        result = check_notebook(p)
        assert len(result["violations"]) == 2

    def test_assignment_no_output_flagged(self, tmp_path):
        # `=` triggers has_output_statement check; no import, no output = flagged
        p = _write_nb([_code("x = 42", 1, [])], tmp_path)
        result = check_notebook(p)
        assert len(result["violations"]) == 1

    def test_multiline_comment_only_skipped(self, tmp_path):
        source = "# line 1\n# line 2\n# line 3"
        p = _write_nb([_code(source, 1, [])], tmp_path)
        result = check_notebook(p)
        assert result["violations"] == []

    def test_source_preview_in_violation(self, tmp_path):
        cell = _code("print('a very long output that should be previewed')", 1, [])
        p = _write_nb([cell], tmp_path)
        result = check_notebook(p)
        assert len(result["violations"]) == 1
        assert "source_preview" in result["violations"][0]

    def test_plt_no_output_flagged(self, tmp_path):
        p = _write_nb([_code("plt.plot(x)", 1, [])], tmp_path)
        result = check_notebook(p)
        assert len(result["violations"]) == 1

    def test_display_no_output_flagged(self, tmp_path):
        p = _write_nb([_code("display(df)", 1, [])], tmp_path)
        result = check_notebook(p)
        assert len(result["violations"]) == 1


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
