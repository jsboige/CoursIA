"""Tests for scripts/notebook_tools/notebook_helpers.py — notebook utilities.

Tests focus on pure functions: NotebookHelper (load, save, get/set source,
find cells, insert/delete, replace, enrichment validation), CellIterator,
CellInfo, IterationResult, ExecutionResult, NotebookExecutionResult.
Uses synthetic notebook dicts and tmp_path for filesystem isolation.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
from notebook_helpers import (
    CellInfo,
    CellIterator,
    ExecutionResult,
    IterationResult,
    NotebookExecutionResult,
    NotebookHelper,
    find_cells_needing_markdown,
    read_notebook,
    write_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _write_nb(path: Path, cells: list[dict], metadata: dict | None = None) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": cells,
        "metadata": metadata or {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _code(source: str, exec_count: int | None = None, outputs: list | None = None,
          cell_id: str | None = None) -> dict:
    cell = {
        "cell_type": "code",
        "source": [source],
        "execution_count": exec_count,
        "outputs": outputs or [],
        "id": cell_id or "abc123",
        "metadata": {},
    }
    return cell


def _md(source: str, cell_id: str | None = None) -> dict:
    return {
        "cell_type": "markdown",
        "source": [source],
        "id": cell_id or "def456",
        "metadata": {},
    }


# ---------------------------------------------------------------------------
# NotebookHelper — load / save
# ---------------------------------------------------------------------------

class TestNotebookHelperLoadSave:
    def test_load_notebook(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        helper = NotebookHelper(str(path))
        assert helper.cell_count == 1

    def test_save_notebook(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        helper = NotebookHelper(str(path))
        helper.set_cell_source(0, "y = 2")
        helper.save()
        # Reload and verify
        helper2 = NotebookHelper(str(path))
        assert helper2.get_cell_source(0) == "y = 2"

    def test_save_to_different_path(self, tmp_path):
        path = _write_nb(tmp_path / "orig.ipynb", [_code("x = 1")])
        helper = NotebookHelper(str(path))
        helper.set_cell_source(0, "z = 3")
        save_path = str(tmp_path / "copy.ipynb")
        helper.save(path=save_path)
        # Original unchanged
        helper_orig = NotebookHelper(str(path))
        assert helper_orig.get_cell_source(0) == "x = 1"
        # Copy has changes
        helper_copy = NotebookHelper(save_path)
        assert helper_copy.get_cell_source(0) == "z = 3"

    def test_file_not_found(self, tmp_path):
        with pytest.raises(FileNotFoundError):
            NotebookHelper(str(tmp_path / "missing.ipynb"))


# ---------------------------------------------------------------------------
# NotebookHelper — cell access
# ---------------------------------------------------------------------------

class TestNotebookHelperCellAccess:
    def test_get_cell_valid(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("a"), _md("b")])
        helper = NotebookHelper(str(path))
        assert helper.get_cell(0)["cell_type"] == "code"
        assert helper.get_cell(1)["cell_type"] == "markdown"

    def test_get_cell_out_of_range(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("a")])
        helper = NotebookHelper(str(path))
        assert helper.get_cell(-1) is None
        assert helper.get_cell(5) is None

    def test_get_cell_by_id(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("a", cell_id="cell-0"),
            _code("b", cell_id="cell-1"),
        ])
        helper = NotebookHelper(str(path))
        result = helper.get_cell_by_id("cell-1")
        assert result is not None
        idx, cell = result
        assert idx == 1

    def test_get_cell_by_id_not_found(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("a")])
        helper = NotebookHelper(str(path))
        assert helper.get_cell_by_id("nonexistent") is None

    def test_cells_property(self, tmp_path):
        cells = [_code("a"), _md("b"), _code("c")]
        path = _write_nb(tmp_path / "test.ipynb", cells)
        helper = NotebookHelper(str(path))
        assert len(helper.cells) == 3

    def test_cell_count(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("a"), _md("b")])
        helper = NotebookHelper(str(path))
        assert helper.cell_count == 2

    def test_cell_count_empty(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [])
        helper = NotebookHelper(str(path))
        assert helper.cell_count == 0


# ---------------------------------------------------------------------------
# NotebookHelper — get/set source
# ---------------------------------------------------------------------------

class TestNotebookHelperSource:
    def test_get_source_string(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        helper = NotebookHelper(str(path))
        assert helper.get_cell_source(0) == "x = 1"

    def test_get_source_list_joined(self, tmp_path):
        nb_path = tmp_path / "test.ipynb"
        nb = {
            "cells": [{"cell_type": "code", "source": ["line1\n", "line2\n", "line3"],
                       "execution_count": None, "outputs": [], "id": "x", "metadata": {}}],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        helper = NotebookHelper(str(nb_path))
        assert helper.get_cell_source(0) == "line1\nline2\nline3"

    def test_get_source_invalid_index(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        helper = NotebookHelper(str(path))
        assert helper.get_cell_source(5) == ""

    def test_set_source_basic(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("old")])
        helper = NotebookHelper(str(path))
        assert helper.set_cell_source(0, "new code") is True
        assert helper.get_cell_source(0) == "new code"

    def test_set_source_multiline(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("old")])
        helper = NotebookHelper(str(path))
        assert helper.set_cell_source(0, "line1\nline2\nline3") is True
        source = helper.get_cell_source(0)
        assert source == "line1\nline2\nline3"

    def test_set_source_invalid_index(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("old")])
        helper = NotebookHelper(str(path))
        assert helper.set_cell_source(5, "new") is False


# ---------------------------------------------------------------------------
# NotebookHelper — outputs
# ---------------------------------------------------------------------------

class TestNotebookHelperOutputs:
    def test_get_outputs_stream(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("print('hello')", outputs=[
                {"output_type": "stream", "text": ["hello\n"]}
            ])
        ])
        helper = NotebookHelper(str(path))
        assert len(helper.get_cell_outputs(0)) == 1

    def test_get_output_text_stream(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("x", outputs=[
                {"output_type": "stream", "text": ["hello\n", "world\n"]}
            ])
        ])
        helper = NotebookHelper(str(path))
        assert "hello" in helper.get_cell_output_text(0)
        assert "world" in helper.get_cell_output_text(0)

    def test_get_output_text_execute_result(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("x", outputs=[
                {"output_type": "execute_result", "data": {"text/plain": "42"}}
            ])
        ])
        helper = NotebookHelper(str(path))
        assert helper.get_cell_output_text(0) == "42"

    def test_get_output_text_error(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("x", outputs=[
                {"output_type": "error", "ename": "ValueError", "evalue": "bad"}
            ])
        ])
        helper = NotebookHelper(str(path))
        text = helper.get_cell_output_text(0)
        assert "ValueError" in text
        assert "bad" in text

    def test_get_output_text_string_text(self, tmp_path):
        """Stream text as string (not list)."""
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("x", outputs=[
                {"output_type": "stream", "text": "single string"}
            ])
        ])
        helper = NotebookHelper(str(path))
        assert "single string" in helper.get_cell_output_text(0)

    def test_get_outputs_markdown_returns_empty(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_md("# Title")])
        helper = NotebookHelper(str(path))
        assert helper.get_cell_outputs(0) == []

    def test_get_outputs_empty(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        helper = NotebookHelper(str(path))
        assert helper.get_cell_outputs(0) == []

    def test_has_cell_error_true(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("x", outputs=[
                {"output_type": "error", "ename": "TypeError", "evalue": "oops"}
            ])
        ])
        helper = NotebookHelper(str(path))
        has_err, msg = helper.has_cell_error(0)
        assert has_err is True
        assert "TypeError" in msg

    def test_has_cell_error_false(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        helper = NotebookHelper(str(path))
        assert helper.has_cell_error(0) == (False, None)


# ---------------------------------------------------------------------------
# NotebookHelper — find cells
# ---------------------------------------------------------------------------

class TestNotebookHelperFind:
    def test_find_code_cells(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("a"), _md("b"), _code("c"), _md("d"), _code("e")
        ])
        helper = NotebookHelper(str(path))
        assert helper.find_code_cells() == [0, 2, 4]

    def test_find_markdown_cells(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("a"), _md("b"), _code("c"), _md("d")
        ])
        helper = NotebookHelper(str(path))
        assert helper.find_markdown_cells() == [1, 3]

    def test_find_consecutive_code_cells(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("a"), _code("b"), _md("c"), _code("d"), _code("e")
        ])
        helper = NotebookHelper(str(path))
        pairs = helper.find_consecutive_code_cells()
        assert (0, 1) in pairs
        assert (3, 4) in pairs
        assert len(pairs) == 2

    def test_find_consecutive_code_cells_none(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("a"), _md("b"), _code("c")
        ])
        helper = NotebookHelper(str(path))
        assert helper.find_consecutive_code_cells() == []

    def test_find_cells_with_pattern(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("import numpy as np"),
            _md("Some text"),
            _code("import pandas as pd"),
        ])
        helper = NotebookHelper(str(path))
        assert helper.find_cells_with_pattern("import") == [0, 2]

    def test_find_cells_with_pattern_code_only(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("import numpy"),
            _md("import pandas"),
        ])
        helper = NotebookHelper(str(path))
        assert helper.find_cells_with_pattern("import", cell_type="code") == [0]

    def test_find_cells_with_pattern_case_insensitive(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("Print('hello')"),
        ])
        helper = NotebookHelper(str(path))
        assert 0 in helper.find_cells_with_pattern("print")

    def test_find_cells_with_errors(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("ok"),
            _code("bad", outputs=[{"output_type": "error", "ename": "E"}]),
            _code("fine"),
        ])
        helper = NotebookHelper(str(path))
        assert helper.find_cells_with_errors() == [1]

    def test_find_cells_with_errors_none(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        helper = NotebookHelper(str(path))
        assert helper.find_cells_with_errors() == []


# ---------------------------------------------------------------------------
# NotebookHelper — insert / delete / replace
# ---------------------------------------------------------------------------

class TestNotebookHelperModify:
    def test_insert_cell_code(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("a"), _md("b")])
        helper = NotebookHelper(str(path))
        cell_id = helper.insert_cell(1, "code", "x = 42")
        assert helper.cell_count == 3
        assert helper.get_cell_source(1) == "x = 42"
        assert len(cell_id) == 8

    def test_insert_cell_markdown(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("a")])
        helper = NotebookHelper(str(path))
        cell_id = helper.insert_cell(1, "markdown", "# Title")
        assert helper.cell_count == 2
        assert helper.get_cell_source(1) == "# Title"

    def test_insert_cell_code_has_outputs_and_exec_count(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("a")])
        helper = NotebookHelper(str(path))
        helper.insert_cell(1, "code", "x = 1")
        cell = helper.get_cell(1)
        assert "outputs" in cell
        assert cell["execution_count"] is None

    def test_delete_cell(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("a"), _md("b"), _code("c")])
        helper = NotebookHelper(str(path))
        assert helper.delete_cell(1) is True
        assert helper.cell_count == 2
        assert helper.get_cell(0)["cell_type"] == "code"
        assert helper.get_cell(1)["cell_type"] == "code"

    def test_delete_cell_invalid(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("a")])
        helper = NotebookHelper(str(path))
        assert helper.delete_cell(5) is False
        assert helper.delete_cell(-1) is False

    def test_replace_in_source_single(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("old value")])
        helper = NotebookHelper(str(path))
        count = helper.replace_in_source(0, "old", "new")
        assert count == 1
        assert helper.get_cell_source(0) == "new value"

    def test_replace_in_source_all(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("a a a")])
        helper = NotebookHelper(str(path))
        count = helper.replace_in_source(0, "a", "b", replace_all=True)
        assert count == 3
        assert helper.get_cell_source(0) == "b b b"

    def test_replace_in_source_no_match(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("hello")])
        helper = NotebookHelper(str(path))
        count = helper.replace_in_source(0, "xyz", "abc")
        assert count == 0


# ---------------------------------------------------------------------------
# NotebookHelper — CellInfo
# ---------------------------------------------------------------------------

class TestNotebookHelperCellInfo:
    def test_get_cell_info(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("print('hi')", exec_count=1, cell_id="myid",
                  outputs=[{"output_type": "stream", "text": ["hi\n"]}])
        ])
        helper = NotebookHelper(str(path))
        info = helper.get_cell_info(0)
        assert info is not None
        assert info.index == 0
        assert info.cell_type == "code"
        assert info.cell_id == "myid"
        assert info.first_line == "print('hi')"
        assert info.execution_count == 1
        assert info.has_error is False
        assert len(info.outputs) == 1

    def test_get_cell_info_with_error(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("bad", outputs=[{"output_type": "error", "ename": "Err", "evalue": "x"}])
        ])
        helper = NotebookHelper(str(path))
        info = helper.get_cell_info(0)
        assert info.has_error is True
        assert "Err" in info.error_message

    def test_get_cell_info_invalid_index(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("a")])
        helper = NotebookHelper(str(path))
        assert helper.get_cell_info(5) is None

    def test_get_cell_info_empty_source(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("")])
        helper = NotebookHelper(str(path))
        info = helper.get_cell_info(0)
        assert info.first_line == ""

    def test_list_cells(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("a"), _md("b")])
        helper = NotebookHelper(str(path))
        infos = helper.list_cells()
        assert len(infos) == 2
        assert infos[0].cell_type == "code"
        assert infos[1].cell_type == "markdown"


# ---------------------------------------------------------------------------
# NotebookHelper — enrichment validation
# ---------------------------------------------------------------------------

class TestNotebookHelperEnrichment:
    def test_validate_enrichment_context_valid(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _md("# Introduction"),
            _code("x = 1", exec_count=1, outputs=[{"output_type": "stream", "text": ["1"]}]),
            _md("Interpretation"),
        ])
        helper = NotebookHelper(str(path))
        result = helper.validate_enrichment_context(1)
        assert result["valid"] is True
        assert result["has_intro_before"] is True
        assert result["has_interpretation_after"] is True

    def test_validate_enrichment_consecutive_code(self, tmp_path):
        """Consecutive code cells without markdown between them = invalid."""
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("a"),
            _code("b"),
        ])
        helper = NotebookHelper(str(path))
        result = helper.validate_enrichment_context(1)
        assert result["valid"] is False
        assert "explanation BEFORE" in result["suggestion"]

    def test_validate_enrichment_output_no_interpretation(self, tmp_path):
        """Code with output but no markdown after = invalid."""
        path = _write_nb(tmp_path / "test.ipynb", [
            _md("intro"),
            _code("x = 1", outputs=[{"output_type": "stream", "text": ["1"]}]),
            _code("y = 2"),
        ])
        helper = NotebookHelper(str(path))
        result = helper.validate_enrichment_context(1)
        assert result["valid"] is False
        assert "interpretation AFTER" in result["suggestion"]

    def test_validate_enrichment_not_code_cell(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_md("text")])
        helper = NotebookHelper(str(path))
        result = helper.validate_enrichment_context(0)
        assert result["valid"] is False
        assert "not a code cell" in result["suggestion"]

    def test_validate_enrichment_first_cell(self, tmp_path):
        """First cell with no previous cell is OK for has_intro_before."""
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        helper = NotebookHelper(str(path))
        result = helper.validate_enrichment_context(0)
        # No output → no interpretation needed. No prev cell → not a consecutive code issue.
        assert result["has_intro_before"] is False
        assert result["has_interpretation_after"] is False

    def test_find_cells_needing_enrichment(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("a"),
            _code("b", outputs=[{"output_type": "stream", "text": ["x"]}]),
        ])
        helper = NotebookHelper(str(path))
        needs = helper.find_cells_needing_enrichment()
        # Cell 0: prev is None, next is code → consecutive code → needs intro
        # Cell 1: prev is code (consecutive), has output, next is None → needs both
        assert len(needs) >= 1

    def test_find_cells_needing_enrichment_all_good(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _md("# Intro"),
            _code("x = 1", exec_count=1),
            _md("Result"),
        ])
        helper = NotebookHelper(str(path))
        assert helper.find_cells_needing_enrichment() == []

    def test_get_insertion_plan(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _md("# Title"),
            _code("a", outputs=[{"output_type": "stream", "text": ["x"]}]),
            _code("b"),
        ])
        helper = NotebookHelper(str(path))
        plan = helper.get_insertion_plan()
        # Cell 1 has output, cell 2 is code → need interpretation after cell 1
        assert len(plan) == 1
        assert plan[0]["insert_after_index"] == 1
        assert plan[0]["content_type"] == "interpretation"

    def test_get_insertion_plan_reversed(self, tmp_path):
        """Plan should be in REVERSE order so insertions don't shift indices."""
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("a", outputs=[{"output_type": "stream", "text": ["x"]}]),
            _code("b"),
            _code("c", outputs=[{"output_type": "stream", "text": ["y"]}]),
            _code("d"),
        ])
        helper = NotebookHelper(str(path))
        plan = helper.get_insertion_plan()
        # Interpretation after cell 2 and after cell 0
        if len(plan) >= 2:
            assert plan[0]["insert_after_index"] > plan[1]["insert_after_index"]

    def test_get_insertion_plan_empty(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _md("# Title"),
            _code("x = 1"),
            _md("Conclusion"),
        ])
        helper = NotebookHelper(str(path))
        assert helper.get_insertion_plan() == []


# ---------------------------------------------------------------------------
# NotebookHelper — cell sequence
# ---------------------------------------------------------------------------

class TestNotebookHelperCellSequence:
    def test_get_cell_sequence_single(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1", cell_id="c0"),
        ])
        helper = NotebookHelper(str(path))
        seq = helper.get_cell_sequence(0)
        assert len(seq) == 1
        assert seq[0]["index"] == 0
        assert seq[0]["type"] == "code"

    def test_get_cell_sequence_range(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("a", cell_id="c0"),
            _md("b", cell_id="c1"),
            _code("c", cell_id="c2"),
        ])
        helper = NotebookHelper(str(path))
        seq = helper.get_cell_sequence(0, 2)
        assert len(seq) == 3

    def test_get_cell_sequence_clamp(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("a")])
        helper = NotebookHelper(str(path))
        seq = helper.get_cell_sequence(-5, 100)
        assert len(seq) == 1

    def test_get_cell_sequence_code_has_output_flag(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("x", outputs=[{"output_type": "stream", "text": ["x"]}]),
        ])
        helper = NotebookHelper(str(path))
        seq = helper.get_cell_sequence(0)
        assert seq[0]["has_output"] is True

    def test_get_cell_sequence_code_no_output(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        helper = NotebookHelper(str(path))
        seq = helper.get_cell_sequence(0)
        assert seq[0]["has_output"] is False

    def test_print_cell_sequence(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("x = 1", cell_id="c0"),
            _md("# Title", cell_id="c1"),
        ])
        helper = NotebookHelper(str(path))
        output = helper.print_cell_sequence(0, 1)
        assert "[CODE]" in output
        assert "[MD]" in output
        assert "c0" in output
        assert "c1" in output


# ---------------------------------------------------------------------------
# CellIterator
# ---------------------------------------------------------------------------

class TestCellIterator:
    def test_init(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        it = CellIterator(str(path), cell_index=0, objective="output contains 1")
        assert it.iteration == 0
        assert it.is_complete is False
        assert it.success is False

    def test_current_source(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        it = CellIterator(str(path), cell_index=0, objective="1")
        assert it.current_source == "x = 1"

    def test_evaluate_success(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        it = CellIterator(str(path), cell_index=0, objective="success",
                          max_iterations=3)
        result = it.evaluate("Operation success!")
        assert result.success is True
        assert result.objective_met is True
        assert it.is_complete is True
        assert it.success is True

    def test_evaluate_with_error(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("bad")])
        it = CellIterator(str(path), cell_index=0, objective="success")
        result = it.evaluate("", error="TypeError: bad call")
        assert result.success is False
        assert result.objective_met is False
        assert it.is_complete is False

    def test_evaluate_max_iterations(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x")])
        it = CellIterator(str(path), cell_index=0, objective="NEVER_MATCH",
                          max_iterations=2)
        it.evaluate("output1")
        it.evaluate("output2")
        assert it.is_complete is True
        assert it.success is False

    def test_apply_correction(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("old")])
        it = CellIterator(str(path), cell_index=0, objective="new")
        it.apply_correction("new code")
        assert it.current_source == "new code"

    def test_get_summary(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x")])
        it = CellIterator(str(path), cell_index=0, objective="test", max_iterations=5)
        it.evaluate("test output")
        summary = it.get_summary()
        assert summary["iterations"] == 1
        assert summary["notebook"] == str(path)
        assert summary["cell_index"] == 0
        assert len(summary["history"]) == 1

    def test_custom_objective_checker(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x")])
        checker = lambda output, obj: "MAGIC" in output
        it = CellIterator(str(path), cell_index=0, objective="irrelevant",
                          objective_checker=checker)
        result = it.evaluate("some MAGIC output")
        assert result.objective_met is True

    def test_default_checker_error_keywords(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x")])
        it = CellIterator(str(path), cell_index=0, objective="success")
        # Error keyword in output → not met
        result = it.evaluate("Error: something failed")
        assert result.objective_met is False

    def test_history_accumulates(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x")])
        it = CellIterator(str(path), cell_index=0, objective="NEVER",
                          max_iterations=3)
        it.evaluate("a")
        it.evaluate("b")
        assert len(it.history) == 2
        assert it.history[0].iteration == 1
        assert it.history[1].iteration == 2

    def test_save(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("old")])
        it = CellIterator(str(path), cell_index=0, objective="new")
        it.apply_correction("new code")
        it.save()
        helper2 = NotebookHelper(str(path))
        assert helper2.get_cell_source(0) == "new code"


# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------

class TestDataclasses:
    def test_cell_info_defaults(self):
        info = CellInfo(index=0, cell_id="x", cell_type="code",
                        source="code", first_line="code")
        assert info.outputs == []
        assert info.execution_count is None
        assert info.has_error is False
        assert info.error_message is None

    def test_iteration_result_defaults(self):
        result = IterationResult(iteration=1, success=True,
                                 cell_source="code")
        assert result.output is None
        assert result.error is None
        assert result.objective_met is False
        assert result.notes == ""

    def test_execution_result_defaults(self):
        result = ExecutionResult(success=True)
        assert result.cell_index is None
        assert result.output == ""
        assert result.error is None
        assert result.duration == 0.0
        assert result.kernel == "unknown"

    def test_notebook_execution_result_success_rate(self):
        result = NotebookExecutionResult(
            success=True, notebook_path="test.ipynb",
            executed_cells=10, failed_cells=2
        )
        assert result.success_rate == 80.0

    def test_notebook_execution_result_zero_cells(self):
        result = NotebookExecutionResult(
            success=True, notebook_path="test.ipynb",
            executed_cells=0
        )
        assert result.success_rate == 0.0

    def test_notebook_execution_result_defaults(self):
        result = NotebookExecutionResult(success=True, notebook_path="t.ipynb")
        assert result.output_path is None
        assert result.kernel == "unknown"
        assert result.total_cells == 0
        assert result.executed_cells == 0
        assert result.failed_cells == 0
        assert result.duration == 0.0
        assert result.cell_results == []
        assert result.errors == []


# ---------------------------------------------------------------------------
# Utility functions
# ---------------------------------------------------------------------------

class TestUtilityFunctions:
    def test_read_notebook(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")])
        nb = read_notebook(str(path))
        assert "cells" in nb
        assert len(nb["cells"]) == 1

    def test_write_notebook(self, tmp_path):
        path = tmp_path / "out.ipynb"
        nb = {"cells": [], "metadata": {}}
        write_notebook(str(path), nb)
        assert path.exists()
        loaded = json.loads(path.read_text(encoding="utf-8"))
        assert loaded == nb

    def test_find_cells_needing_markdown(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [
            _code("a"),
            _code("b"),
            _md("c"),
        ])
        result = find_cells_needing_markdown(str(path))
        assert "consecutive_code_cells" in result
        assert "cells_with_errors" in result
        assert "code_cells_without_output" in result
        assert len(result["consecutive_code_cells"]) == 1


# ---------------------------------------------------------------------------
# NotebookExecutor — detect_kernel (no actual kernel execution)
# ---------------------------------------------------------------------------

class TestDetectKernel:
    def test_detect_python3_kernel(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")],
                         metadata={"kernelspec": {"name": "python3", "language": "python"}})
        from notebook_helpers import NotebookExecutor
        executor = NotebookExecutor()
        assert executor.detect_kernel(str(path)) == "python3"

    def test_detect_csharp_kernel(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")],
                         metadata={"kernelspec": {"name": ".net-csharp", "language": "C#"}})
        from notebook_helpers import NotebookExecutor
        executor = NotebookExecutor()
        assert executor.detect_kernel(str(path)) == ".net-csharp"

    def test_detect_lean_kernel(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")],
                         metadata={"kernelspec": {"name": "lean4", "language": "lean"}})
        from notebook_helpers import NotebookExecutor
        executor = NotebookExecutor()
        assert executor.detect_kernel(str(path)) == "lean4"

    def test_detect_kernel_default_python(self, tmp_path):
        path = _write_nb(tmp_path / "test.ipynb", [_code("x = 1")],
                         metadata={"kernelspec": {"name": "unknown-kernel"}})
        from notebook_helpers import NotebookExecutor
        executor = NotebookExecutor()
        assert executor.detect_kernel(str(path)) == "python3"

    def test_detect_kernel_dotnet_magic(self, tmp_path):
        nb_path = tmp_path / "test.ipynb"
        nb = {
            "cells": [{"cell_type": "code", "source": ["#!csharp\nlet x = 1"],
                       "execution_count": None, "outputs": [], "id": "x", "metadata": {}}],
            "metadata": {"kernelspec": {"name": "unknown"}},
            "nbformat": 4, "nbformat_minor": 5,
        }
        nb_path.write_text(json.dumps(nb), encoding="utf-8")
        from notebook_helpers import NotebookExecutor
        executor = NotebookExecutor()
        assert executor.detect_kernel(str(nb_path)) == ".net-csharp"

    def test_kernel_patterns_constant(self):
        from notebook_helpers import NotebookExecutor
        assert "python" in NotebookExecutor.KERNEL_PATTERNS
        assert ".net-csharp" in NotebookExecutor.KERNEL_PATTERNS
        assert "lean4" in NotebookExecutor.KERNEL_PATTERNS
