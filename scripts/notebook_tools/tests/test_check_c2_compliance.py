"""Tests for scripts/notebook_tools/check_c2_compliance.py — C.2 compliance checker.

Tests focus on the pure check_notebook function, covering:
- Missing execution_count violations
- Missing outputs violations
- Empty/comment-only cell skipping
- Import cell handling
- Invalid JSON handling
- Edge cases (empty notebook, markdown cells, etc.)
"""

import json
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from check_c2_compliance import (
    EXCLUDE_ALWAYS,
    EXCLUDE_PEDAGOGICAL,
    check_notebook,
    get_target_notebooks,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _code(source: str, exec_count: int | None = None, outputs: list | None = None) -> dict:
    return {
        "cell_type": "code",
        "source": [source],
        "execution_count": exec_count,
        "outputs": outputs or [],
    }


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


def _write_nb(path: Path, cells: list[dict], metadata: dict | None = None) -> Path:
    """Write a minimal .ipynb file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": metadata or {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# check_notebook — missing execution_count
# ---------------------------------------------------------------------------

class TestMissingExecCount:
    """Tests for missing execution_count detection."""

    def test_compliant_notebook(self, tmp_path):
        """Notebook with exec_count and outputs -> no violations."""
        nb_path = _write_nb(tmp_path / "good.ipynb", [
            _code("x = 1", exec_count=1, outputs=[{"output_type": "execute_result", "data": {"text/plain": "1"}}]),
        ])
        result = check_notebook(nb_path)
        assert result["violations"] == []
        assert result["total_code"] == 1

    def test_missing_exec_count(self, tmp_path):
        """Code cell without exec_count -> violation."""
        nb_path = _write_nb(tmp_path / "bad.ipynb", [
            _code("x = 1"),
        ])
        result = check_notebook(nb_path)
        assert len(result["violations"]) == 1
        assert result["violations"][0]["reason"] == "missing execution_count"
        assert result["violations"][0]["cell_index"] == 0

    def test_exec_count_null(self, tmp_path):
        """execution_count: null treated as missing."""
        nb_path = _write_nb(tmp_path / "null.ipynb", [
            _code("x = 1", exec_count=None),
        ])
        result = check_notebook(nb_path)
        assert len(result["violations"]) == 1

    def test_exec_count_zero_ok(self, tmp_path):
        """execution_count: 0 is valid (not None)."""
        nb_path = _write_nb(tmp_path / "zero.ipynb", [
            _code("x = 1", exec_count=0, outputs=[{"output_type": "execute_result"}]),
        ])
        result = check_notebook(nb_path)
        assert result["violations"] == []

    def test_multiple_cells_one_missing(self, tmp_path):
        """Only the cell missing exec_count is flagged."""
        nb_path = _write_nb(tmp_path / "mixed.ipynb", [
            _code("x = 1", exec_count=1, outputs=[{"output_type": "stream"}]),
            _code("y = 2"),  # missing
            _code("z = 3", exec_count=3, outputs=[{"output_type": "stream"}]),
        ])
        result = check_notebook(nb_path)
        assert len(result["violations"]) == 1
        assert result["violations"][0]["cell_index"] == 1
        assert result["total_code"] == 3


# ---------------------------------------------------------------------------
# check_notebook — missing outputs
# ---------------------------------------------------------------------------

class TestMissingOutputs:
    """Tests for missing outputs detection (exec_count set but no outputs)."""

    def test_print_without_output(self, tmp_path):
        """Cell with print() but no outputs -> violation."""
        nb_path = _write_nb(tmp_path / "no_out.ipynb", [
            _code("print('hello')", exec_count=1),
        ])
        result = check_notebook(nb_path)
        assert len(result["violations"]) == 1
        assert "no outputs" in result["violations"][0]["reason"]

    def test_display_without_output(self, tmp_path):
        """Cell with display() but no outputs -> violation."""
        nb_path = _write_nb(tmp_path / "disp.ipynb", [
            _code("display(x)", exec_count=1),
        ])
        result = check_notebook(nb_path)
        assert len(result["violations"]) == 1

    def test_plt_without_output(self, tmp_path):
        """Cell with plt. but no outputs -> violation."""
        nb_path = _write_nb(tmp_path / "plt.ipynb", [
            _code("plt.plot([1,2,3])", exec_count=1),
        ])
        result = check_notebook(nb_path)
        assert len(result["violations"]) == 1

    def test_import_no_output_ok(self, tmp_path):
        """Import cell without outputs -> OK (expected)."""
        nb_path = _write_nb(tmp_path / "import.ipynb", [
            _code("import os", exec_count=1),
        ])
        result = check_notebook(nb_path)
        assert result["violations"] == []

    def test_from_import_no_output_ok(self, tmp_path):
        """from X import Y without outputs -> OK."""
        nb_path = _write_nb(tmp_path / "from_import.ipynb", [
            _code("from pathlib import Path", exec_count=1),
        ])
        result = check_notebook(nb_path)
        assert result["violations"] == []

    def test_assignment_no_output_flagged(self, tmp_path):
        """Simple assignment with = but no print/display -> flagged (has '=' keyword)."""
        nb_path = _write_nb(tmp_path / "assign.ipynb", [
            _code("x = compute_value()", exec_count=1),
        ])
        result = check_notebook(nb_path)
        assert len(result["violations"]) == 1
        assert "no outputs" in result["violations"][0]["reason"]

    def test_pure_function_call_no_output(self, tmp_path):
        """Function call without = or print -> not flagged (no output keyword)."""
        nb_path = _write_nb(tmp_path / "func.ipynb", [
            _code("setup_environment()", exec_count=1),
        ])
        result = check_notebook(nb_path)
        assert result["violations"] == []

    def test_return_statement_no_output(self, tmp_path):
        """Cell with return statement but no outputs -> violation."""
        nb_path = _write_nb(tmp_path / "ret.ipynb", [
            _code("return value", exec_count=1),
        ])
        result = check_notebook(nb_path)
        assert len(result["violations"]) == 1

    def test_cell_with_outputs_ok(self, tmp_path):
        """Cell with exec_count AND outputs -> OK."""
        nb_path = _write_nb(tmp_path / "ok.ipynb", [
            _code("print('hello')", exec_count=1, outputs=[{"output_type": "stream"}]),
        ])
        result = check_notebook(nb_path)
        assert result["violations"] == []


# ---------------------------------------------------------------------------
# check_notebook — skipping rules
# ---------------------------------------------------------------------------

class TestSkippingRules:
    """Tests for cells that should be skipped."""

    def test_empty_cell_skipped(self, tmp_path):
        """Empty code cell -> skipped."""
        nb_path = _write_nb(tmp_path / "empty.ipynb", [
            _code("", exec_count=None),
        ])
        result = check_notebook(nb_path)
        assert result["violations"] == []
        assert result["total_code"] == 1

    def test_whitespace_only_cell_skipped(self, tmp_path):
        """Whitespace-only code cell -> skipped."""
        nb_path = _write_nb(tmp_path / "ws.ipynb", [
            _code("   \n  \n  ", exec_count=None),
        ])
        result = check_notebook(nb_path)
        assert result["violations"] == []

    def test_comment_only_cell_skipped(self, tmp_path):
        """Code cell with only comments -> skipped."""
        nb_path = _write_nb(tmp_path / "comment.ipynb", [
            _code("# This is just a comment", exec_count=None),
        ])
        result = check_notebook(nb_path)
        assert result["violations"] == []

    def test_multiline_comment_only_skipped(self, tmp_path):
        """Code cell with only comments across multiple lines -> skipped."""
        nb_path = _write_nb(tmp_path / "multi_comment.ipynb", [
            _code("# line 1\n# line 2\n# line 3", exec_count=None),
        ])
        result = check_notebook(nb_path)
        assert result["violations"] == []

    def test_markdown_cells_ignored(self, tmp_path):
        """Markdown cells are not counted as code cells."""
        nb_path = _write_nb(tmp_path / "md.ipynb", [
            _md("# Title"),
            _md("Some text"),
        ])
        result = check_notebook(nb_path)
        assert result["violations"] == []
        assert result["total_code"] == 0

    def test_mixed_markdown_and_code(self, tmp_path):
        """Markdown cells don't affect code cell indexing."""
        nb_path = _write_nb(tmp_path / "mixed.ipynb", [
            _md("# Title"),
            _code("x = 1", exec_count=None),
            _md("## Section"),
            _code("y = 2", exec_count=2, outputs=[{"output_type": "stream"}]),
        ])
        result = check_notebook(nb_path)
        assert len(result["violations"]) == 1
        assert result["violations"][0]["cell_index"] == 1  # 2nd cell overall, 1st code
        assert result["total_code"] == 2


# ---------------------------------------------------------------------------
# check_notebook — edge cases
# ---------------------------------------------------------------------------

class TestEdgeCases:
    """Edge cases for check_notebook."""

    def test_invalid_json(self, tmp_path):
        """Non-JSON file -> error violation."""
        p = tmp_path / "bad.ipynb"
        p.write_text("not valid json{{{", encoding="utf-8")
        result = check_notebook(p)
        assert len(result["violations"]) == 1
        assert "error" in result["violations"][0]
        assert "Cannot parse" in result["violations"][0]["error"]

    def test_empty_notebook(self, tmp_path):
        """Notebook with no cells -> no violations."""
        nb_path = _write_nb(tmp_path / "empty.ipynb", [])
        result = check_notebook(nb_path)
        assert result["violations"] == []
        assert result["total_code"] == 0

    def test_source_as_list(self, tmp_path):
        """Source as list of strings (standard nbformat)."""
        nb = {
            "cells": [{
                "cell_type": "code",
                "source": ["print('hello')\n"],
                "execution_count": 1,
                "outputs": [],
            }],
        }
        p = tmp_path / "list_src.ipynb"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps({"cells": nb["cells"], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}), encoding="utf-8")
        result = check_notebook(p)
        assert len(result["violations"]) == 1  # print but no outputs

    def test_source_preview_truncation(self, tmp_path):
        """Source preview is truncated to 80 chars."""
        long_code = "x = " + "a" * 200
        nb_path = _write_nb(tmp_path / "long.ipynb", [
            _code(long_code, exec_count=None),
        ])
        result = check_notebook(nb_path)
        assert len(result["violations"]) == 1
        assert len(result["violations"][0]["source_preview"]) <= 80

    def test_code_cell_numbering(self, tmp_path):
        """code_cell counts only code cells (not markdown)."""
        nb_path = _write_nb(tmp_path / "numbered.ipynb", [
            _md("# Title"),
            _code("a = 1"),
            _md("## Break"),
            _code("b = 2"),
        ])
        result = check_notebook(nb_path)
        assert result["violations"][0]["code_cell"] == 1  # 1st code cell
        assert result["violations"][1]["code_cell"] == 2  # 2nd code cell

    def test_unicode_decode_error(self, tmp_path):
        """Binary file that can't be decoded -> error violation."""
        p = tmp_path / "binary.ipynb"
        p.write_bytes(b"\x00\x01\x02\x03\xff\xfe")
        result = check_notebook(p)
        assert len(result["violations"]) == 1
        assert "error" in result["violations"][0]


# ---------------------------------------------------------------------------
# get_target_notebooks
# ---------------------------------------------------------------------------

class TestGetTargetNotebooks:
    """Tests for get_target_notebooks discovery."""

    def _make_args(self, **kwargs):
        """Build a namespace-like object for args."""
        import argparse
        defaults = {
            "path": None, "serie": None, "maturity": None,
            "exclude_broken": False, "no_catalog": True,
            "fix": False, "json": False,
        }
        defaults.update(kwargs)
        return argparse.Namespace(**defaults)

    def test_no_catalog_fallback(self, tmp_path):
        """Without catalog, scan filesystem."""
        with patch("check_c2_compliance.NOTEBOOKS_DIR", tmp_path), \
             patch("check_c2_compliance.CATALOG_PATH", tmp_path / "nonexistent.json"):
            (tmp_path / "good.ipynb").write_text("{}", encoding="utf-8")
            bad = tmp_path / ".ipynb_checkpoints"
            bad.mkdir()
            (bad / "bad.ipynb").write_text("{}", encoding="utf-8")
            args = self._make_args(no_catalog=True)
            result = get_target_notebooks(args)
            names = [p.name for p in result]
            assert "good.ipynb" in names
            assert "bad.ipynb" not in names

    def test_specific_path(self, tmp_path):
        """--path returns single notebook."""
        nb = tmp_path / "specific.ipynb"
        nb.write_text("{}", encoding="utf-8")
        with patch("check_c2_compliance.REPO_ROOT", tmp_path):
            args = self._make_args(path=str(nb))
            result = get_target_notebooks(args)
            assert len(result) == 1
            assert result[0].name == "specific.ipynb"

    def test_specific_path_not_found(self, tmp_path):
        """--path with nonexistent file -> empty list."""
        args = self._make_args(path=str(tmp_path / "missing.ipynb"))
        result = get_target_notebooks(args)
        assert result == []

    def test_excluded_pedagogical_dirs(self, tmp_path):
        """research/archive dirs are excluded in pedagogical mode."""
        with patch("check_c2_compliance.NOTEBOOKS_DIR", tmp_path), \
             patch("check_c2_compliance.CATALOG_PATH", tmp_path / "nonexistent.json"):
            (tmp_path / "good.ipynb").write_text("{}", encoding="utf-8")
            research = tmp_path / "research"
            research.mkdir()
            (research / "bad.ipynb").write_text("{}", encoding="utf-8")
            args = self._make_args(no_catalog=True)
            result = get_target_notebooks(args)
            names = [p.name for p in result]
            assert "good.ipynb" in names
            assert "bad.ipynb" not in names


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Tests for module constants."""

    def test_exclude_always_set(self):
        assert isinstance(EXCLUDE_ALWAYS, set)
        assert ".ipynb_checkpoints" in EXCLUDE_ALWAYS
        assert ".git" in EXCLUDE_ALWAYS

    def test_exclude_pedagogical_set(self):
        assert isinstance(EXCLUDE_PEDAGOGICAL, set)
        assert "research" in EXCLUDE_PEDAGOGICAL
        assert "archive" in EXCLUDE_PEDAGOGICAL
