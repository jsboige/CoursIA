"""Tests for scripts/notebook_tools/forensic_scan.py — notebook forensic scanner.

Tests focus on pure functions: categorize_notebook, is_excluded, get_series.
Filesystem methods use tmp_path for isolation.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from forensic_scan import (
    EXCLUDE_DIRS,
    RULE_C2_DATE,
    categorize_notebook,
    get_series,
    is_excluded,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _write_nb(path: Path, cells: list[dict], metadata: dict | None = None) -> Path:
    """Write a minimal .ipynb file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": metadata or {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _code(source: str, exec_count: int | None = None, outputs: list | None = None) -> dict:
    return {
        "cell_type": "code",
        "source": [source],
        "execution_count": exec_count,
        "outputs": outputs or [],
        "metadata": {},
    }


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source], "metadata": {}}


# ---------------------------------------------------------------------------
# categorize_notebook
# ---------------------------------------------------------------------------

class TestCategorizeNotebook:
    def test_all_exec_ok(self, tmp_path):
        nb_path = _write_nb(tmp_path / "a.ipynb", [
            _code("x = 1", exec_count=1),
            _code("y = 2", exec_count=2),
        ])
        result = categorize_notebook(nb_path)
        assert result["category"] == "A_ALL_EXEC_OK"
        assert result["n_code"] == 2
        assert result["n_exec"] == 2
        assert result["n_err"] == 0

    def test_partial_exec(self, tmp_path):
        nb_path = _write_nb(tmp_path / "a.ipynb", [
            _code("x = 1", exec_count=1),
            _code("y = 2"),
        ])
        result = categorize_notebook(nb_path)
        assert result["category"] == "B_PARTIAL_EXEC"
        assert result["n_exec"] == 1

    def test_never_executed(self, tmp_path):
        nb_path = _write_nb(tmp_path / "a.ipynb", [
            _code("x = 1"),
            _code("y = 2"),
        ])
        result = categorize_notebook(nb_path)
        assert result["category"] == "C_NEVER_EXECUTED"
        assert result["n_exec"] == 0

    def test_has_errors(self, tmp_path):
        nb_path = _write_nb(tmp_path / "a.ipynb", [
            _code("x = 1", exec_count=1, outputs=[{"output_type": "error", "ename": "Err"}]),
        ])
        result = categorize_notebook(nb_path)
        assert result["category"] == "D_HAS_ERRORS"
        assert result["n_err"] == 1

    def test_error_takes_priority(self, tmp_path):
        """Error takes priority over partial execution."""
        nb_path = _write_nb(tmp_path / "a.ipynb", [
            _code("x = 1", exec_count=1),
            _code("y = 2", exec_count=2, outputs=[{"output_type": "error"}]),
        ])
        result = categorize_notebook(nb_path)
        assert result["category"] == "D_HAS_ERRORS"

    def test_no_code_cells(self, tmp_path):
        nb_path = _write_nb(tmp_path / "a.ipynb", [_md("# Title")])
        result = categorize_notebook(nb_path)
        assert result["category"] == "NO_CODE"
        assert result["n_code"] == 0

    def test_reference_notebook(self, tmp_path):
        nb_path = _write_nb(tmp_path / "a.ipynb", [_code("x = 1")],
                             metadata={"qc_reference": True})
        result = categorize_notebook(nb_path)
        assert result["category"] == "REFERENCE"

    def test_parse_error(self, tmp_path):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("{invalid json!!!", encoding="utf-8")
        result = categorize_notebook(bad)
        assert result["category"] == "PARSE_ERROR"
        assert "error" in result

    def test_missing_file(self, tmp_path):
        result = categorize_notebook(tmp_path / "missing.ipynb")
        assert result["category"] == "PARSE_ERROR"

    def test_outputs_count(self, tmp_path):
        nb_path = _write_nb(tmp_path / "a.ipynb", [
            _code("x = 1", exec_count=1, outputs=[{"output_type": "execute_result"}]),
            _code("y = 2"),
        ])
        result = categorize_notebook(nb_path)
        assert result["n_outputs"] == 1

    def test_empty_cells_list(self, tmp_path):
        nb_path = _write_nb(tmp_path / "a.ipynb", [])
        result = categorize_notebook(nb_path)
        assert result["category"] == "NO_CODE"


# ---------------------------------------------------------------------------
# is_excluded
# ---------------------------------------------------------------------------

class TestIsExcluded:
    def test_normal_notebook(self):
        assert is_excluded(Path("MyIA.AI.Notebooks/GenAI/nb.ipynb")) is False

    def test_archive_dir(self):
        assert is_excluded(Path("_archives/old.ipynb")) is True

    def test_archive_obsoletes(self):
        assert is_excluded(Path("_archive_obsoletes/x.ipynb")) is True

    def test_trashbin(self):
        assert is_excluded(Path("TrashBin/x.ipynb")) is True

    def test_checkpoints(self):
        assert is_excluded(Path(".ipynb_checkpoints/nb.ipynb")) is True

    def test_node_modules(self):
        assert is_excluded(Path("node_modules/ext/nb.ipynb")) is True

    def test_output_artifact(self):
        assert is_excluded(Path("series/nb_output.ipynb")) is True

    def test_pending_execution(self):
        assert is_excluded(Path("series/_pending_execution/nb.ipynb")) is True

    def test_normal_name_not_excluded(self):
        assert is_excluded(Path("series/nb.ipynb")) is False

    def test_old_dir(self):
        assert is_excluded(Path("_old/legacy.ipynb")) is True


# ---------------------------------------------------------------------------
# get_series
# ---------------------------------------------------------------------------

class TestGetSeries:
    def test_nested_path(self):
        root = Path("MyIA.AI.Notebooks")
        path = Path("MyIA.AI.Notebooks/GenAI/Image/nb.ipynb")
        assert get_series(path, root) == "GenAI"

    def test_direct_child(self):
        root = Path("MyIA.AI.Notebooks")
        path = Path("MyIA.AI.Notebooks/Search/nb.ipynb")
        assert get_series(path, root) == "Search"

    def test_top_level_notebook(self):
        root = Path("MyIA.AI.Notebooks")
        path = Path("MyIA.AI.Notebooks/lonely.ipynb")
        assert get_series(path, root) == "TOP"

    def test_root_path(self):
        """Edge case: path == root (should not happen in practice)."""
        root = Path("MyIA.AI.Notebooks")
        # Simulate by making path relative to itself
        assert get_series(root, root) == "ROOT"


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

class TestConstants:
    def test_rule_c2_date(self):
        assert RULE_C2_DATE.year == 2026
        assert RULE_C2_DATE.month == 4
        assert RULE_C2_DATE.day == 26

    def test_exclude_dirs_has_expected(self):
        assert "_archives" in EXCLUDE_DIRS
        assert ".ipynb_checkpoints" in EXCLUDE_DIRS
        assert "node_modules" in EXCLUDE_DIRS
