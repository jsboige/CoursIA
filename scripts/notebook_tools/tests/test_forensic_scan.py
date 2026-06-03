"""Tests for forensic_scan.py — notebook execution state categorization."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from forensic_scan import (
    categorize_notebook,
    get_series,
    is_excluded,
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


def _code(
    source: str,
    execution_count: int | None = 1,
    outputs: list | None = None,
    has_error: bool = False,
) -> dict:
    """Build a code cell."""
    if outputs is None:
        outs = [{"output_type": "execute_result", "data": {"text/plain": ["ok"]}}]
    else:
        outs = outputs
    if has_error:
        outs = [{"output_type": "error", "ename": "RuntimeError", "evalue": "boom"}]
    return {
        "cell_type": "code",
        "source": [source],
        "execution_count": execution_count,
        "outputs": outs,
        "metadata": {},
    }


def _md(source: str) -> dict:
    """Build a markdown cell."""
    return {"cell_type": "markdown", "source": [source], "metadata": {}}


def _write_nb(tmp_path: Path, name: str, nb: dict) -> Path:
    """Write a notebook dict to disk and return the path."""
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


# --- categorize_notebook ---


class TestCategorizeAllExecOk:
    """Category A: all code cells executed, 0 errors."""

    def test_single_cell_executed(self, tmp_path):
        nb = _nb([_code("x = 1", execution_count=1)])
        p = _write_nb(tmp_path, "ok.ipynb", nb)
        result = categorize_notebook(p)
        assert result["category"] == "A_ALL_EXEC_OK"
        assert result["n_code"] == 1
        assert result["n_exec"] == 1
        assert result["n_err"] == 0

    def test_multiple_cells_all_executed(self, tmp_path):
        nb = _nb([
            _code("x = 1", execution_count=1),
            _code("y = 2", execution_count=2),
            _code("print(x + y)", execution_count=3),
        ])
        p = _write_nb(tmp_path, "ok.ipynb", nb)
        result = categorize_notebook(p)
        assert result["category"] == "A_ALL_EXEC_OK"
        assert result["n_code"] == 3

    def test_mixed_code_and_markdown(self, tmp_path):
        nb = _nb([
            _md("# Title"),
            _code("x = 1", execution_count=1),
            _md("## Section"),
            _code("y = 2", execution_count=2),
        ])
        p = _write_nb(tmp_path, "ok.ipynb", nb)
        result = categorize_notebook(p)
        assert result["category"] == "A_ALL_EXEC_OK"
        assert result["n_code"] == 2


class TestCategorizePartialExec:
    """Category B: some cells executed, some not."""

    def test_mixed_exec_counts(self, tmp_path):
        nb = _nb([
            _code("x = 1", execution_count=1),
            _code("y = 2", execution_count=None),
        ])
        p = _write_nb(tmp_path, "partial.ipynb", nb)
        result = categorize_notebook(p)
        assert result["category"] == "B_PARTIAL_EXEC"
        assert result["n_code"] == 2
        assert result["n_exec"] == 1

    def test_mostly_executed(self, tmp_path):
        nb = _nb([
            _code("a = 1", execution_count=1),
            _code("b = 2", execution_count=2),
            _code("c = 3", execution_count=3),
            _code("d = 4", execution_count=None),
        ])
        p = _write_nb(tmp_path, "partial.ipynb", nb)
        result = categorize_notebook(p)
        assert result["category"] == "B_PARTIAL_EXEC"
        assert result["n_exec"] == 3
        assert result["n_code"] == 4


class TestCategorizeNeverExecuted:
    """Category C: all code cells have null execution_count."""

    def test_all_null_exec(self, tmp_path):
        nb = _nb([
            _code("x = 1", execution_count=None, outputs=[]),
            _code("y = 2", execution_count=None, outputs=[]),
        ])
        p = _write_nb(tmp_path, "never.ipynb", nb)
        result = categorize_notebook(p)
        assert result["category"] == "C_NEVER_EXECUTED"
        assert result["n_exec"] == 0

    def test_single_unexecuted_cell(self, tmp_path):
        nb = _nb([_code("pass", execution_count=None, outputs=[])])
        p = _write_nb(tmp_path, "never.ipynb", nb)
        result = categorize_notebook(p)
        assert result["category"] == "C_NEVER_EXECUTED"


class TestCategorizeHasErrors:
    """Category D: at least one cell with error output."""

    def test_single_error(self, tmp_path):
        nb = _nb([
            _code("x = 1", execution_count=1),
            _code("1/0", execution_count=2, has_error=True),
        ])
        p = _write_nb(tmp_path, "error.ipynb", nb)
        result = categorize_notebook(p)
        assert result["category"] == "D_HAS_ERRORS"
        assert result["n_err"] == 1

    def test_all_errors(self, tmp_path):
        nb = _nb([
            _code("x = 1", execution_count=1, has_error=True),
            _code("y = 2", execution_count=2, has_error=True),
        ])
        p = _write_nb(tmp_path, "all_errors.ipynb", nb)
        result = categorize_notebook(p)
        assert result["category"] == "D_HAS_ERRORS"
        assert result["n_err"] == 2

    def test_error_takes_precedence_over_partial(self, tmp_path):
        """Error category should override partial execution."""
        nb = _nb([
            _code("x = 1", execution_count=1),
            _code("y = 2", execution_count=None, outputs=[], has_error=True),
        ])
        p = _write_nb(tmp_path, "mixed.ipynb", nb)
        result = categorize_notebook(p)
        assert result["category"] == "D_HAS_ERRORS"


class TestCategorizeSpecialCases:
    """Edge cases: no code cells, QC reference, parse errors."""

    def test_no_code_cells(self, tmp_path):
        nb = _nb([_md("# Title"), _md("Some text")])
        p = _write_nb(tmp_path, "no_code.ipynb", nb)
        result = categorize_notebook(p)
        assert result["category"] == "NO_CODE"
        assert result["n_code"] == 0

    def test_qc_reference_notebook(self, tmp_path):
        nb = _nb(
            [_code("x = 1", execution_count=None, outputs=[])],
            qc_reference=True,
        )
        p = _write_nb(tmp_path, "ref.ipynb", nb)
        result = categorize_notebook(p)
        assert result["category"] == "REFERENCE"
        assert result["n_code"] == 0

    def test_invalid_json(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        p.write_text("not valid json{{{", encoding="utf-8")
        result = categorize_notebook(p)
        assert result["category"] == "PARSE_ERROR"
        assert "error" in result

    def test_empty_notebook(self, tmp_path):
        nb = _nb([])
        p = _write_nb(tmp_path, "empty.ipynb", nb)
        result = categorize_notebook(p)
        assert result["category"] == "NO_CODE"

    def test_n_outputs_count(self, tmp_path):
        """n_outputs counts cells with truthy (non-empty) outputs."""
        nb = _nb([
            _code("x = 1", execution_count=1),
            _code("y = 2", execution_count=2, outputs=[]),
        ])
        p = _write_nb(tmp_path, "outputs.ipynb", nb)
        result = categorize_notebook(p)
        # Cell 1 has outputs=[execute_result] (truthy), cell 2 has outputs=[] (falsy)
        assert result["n_outputs"] == 1


# --- is_excluded ---


class TestIsExcluded:
    def test_normal_notebook_not_excluded(self):
        p = Path("MyIA.AI.Notebooks/Search/App-1.ipynb")
        assert is_excluded(p) is False

    def test_archive_excluded(self):
        p = Path("MyIA.AI.Notebooks/SomeSeries/_archives/old.ipynb")
        assert is_excluded(p) is True

    def test_output_artifact_excluded(self):
        p = Path("MyIA.AI.Notebooks/Search/App-1_output.ipynb")
        assert is_excluded(p) is True

    def test_checkpoint_excluded(self):
        p = Path("MyIA.AI.Notebooks/.ipynb_checkpoints/nb.ipynb")
        assert is_excluded(p) is True

    def test_pending_execution_excluded(self):
        p = Path("MyIA.AI.Notebooks/QC/_pending_execution/nb.ipynb")
        assert is_excluded(p) is True

    def test_node_modules_excluded(self):
        p = Path("MyIA.AI.Notebooks/node_modules/nb.ipynb")
        assert is_excluded(p) is True

    def test_trashbin_excluded(self):
        p = Path("MyIA.AI.Notebooks/TrashBin/old.ipynb")
        assert is_excluded(p) is True


# --- get_series ---


class TestGetSeries:
    def test_single_level_under_root(self):
        p = Path("MyIA.AI.Notebooks/README.md")
        # relative_to gives "README.md" -> parts = ("README.md",) -> len < 2 -> TOP
        rel = p.relative_to(Path("MyIA.AI.Notebooks"))
        assert get_series(p, Path("MyIA.AI.Notebooks")) == "TOP"

    def test_two_levels(self):
        p = Path("MyIA.AI.Notebooks/Search/App-1.ipynb")
        assert get_series(p, Path("MyIA.AI.Notebooks")) == "Search"

    def test_deep_path(self):
        p = Path("MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-1.ipynb")
        assert get_series(p, Path("MyIA.AI.Notebooks")) == "SymbolicAI"
