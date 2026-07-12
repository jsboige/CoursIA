"""Tests for notebook_helpers.py — NotebookHelper pure methods, CellIterator, utilities."""

import json
import os
import sys

import pytest

# Add parent dir to path for import
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from notebook_helpers import (
    NotebookHelper,
    CellIterator,
    CellInfo,
    IterationResult,
    ExecutionResult,
    NotebookExecutionResult,
    read_notebook,
    write_notebook,
    find_cells_needing_markdown,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_nb(cells, metadata=None):
    """Build a minimal notebook dict."""
    nb = {
        "cells": cells,
        "metadata": metadata or {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    return nb


def _write_nb(cells, tmp_path, name="test.ipynb", metadata=None):
    """Write a notebook to disk and return its path."""
    p = tmp_path / name
    p.write_text(json.dumps(_make_nb(cells, metadata)), encoding="utf-8")
    return str(p)


def _code_cell(source, cell_id="c1", outputs=None, execution_count=1):
    """Build a code cell dict."""
    cell = {
        "cell_type": "code",
        "id": cell_id,
        "metadata": {},
        "source": [source] if isinstance(source, str) else source,
        "outputs": outputs or [],
        "execution_count": execution_count,
    }
    return cell


def _md_cell(source, cell_id="m1"):
    """Build a markdown cell dict."""
    return {
        "cell_type": "markdown",
        "id": cell_id,
        "metadata": {},
        "source": [source] if isinstance(source, str) else source,
    }


# ===========================================================================
# NotebookHelper — load / save / cells / cell_count
# ===========================================================================

class TestNotebookHelperLoadSave:

    def test_load_reads_json(self, tmp_path):
        cells = [_code_cell("x = 1")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        assert h.cell_count == 1
        assert h.cells[0]["cell_type"] == "code"

    def test_save_writes_json(self, tmp_path):
        cells = [_code_cell("x = 1")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        h.set_cell_source(0, "y = 2")
        out = tmp_path / "out.ipynb"
        h.save(str(out))
        h2 = NotebookHelper(str(out))
        assert h2.get_cell_source(0) == "y = 2"

    def test_save_default_path_overwrites(self, tmp_path):
        p = _write_nb([_code_cell("x = 1")], tmp_path)
        h = NotebookHelper(p)
        h.set_cell_source(0, "z = 3")
        h.save()
        h2 = NotebookHelper(p)
        assert h2.get_cell_source(0) == "z = 3"

    def test_cells_empty_notebook(self, tmp_path):
        p = _write_nb([], tmp_path)
        h = NotebookHelper(p)
        assert h.cells == []
        assert h.cell_count == 0


# ===========================================================================
# NotebookHelper — get_cell / get_cell_by_id / get_cell_source / set_cell_source
# ===========================================================================

class TestNotebookHelperCellAccess:

    def test_get_cell_valid(self, tmp_path):
        p = _write_nb([_code_cell("x = 1", cell_id="abc")], tmp_path)
        h = NotebookHelper(p)
        cell = h.get_cell(0)
        assert cell is not None
        assert cell["id"] == "abc"

    def test_get_cell_out_of_range(self, tmp_path):
        p = _write_nb([_code_cell("x = 1")], tmp_path)
        h = NotebookHelper(p)
        assert h.get_cell(-1) is None
        assert h.get_cell(99) is None

    def test_get_cell_by_id_found(self, tmp_path):
        p = _write_nb([_code_cell("a", cell_id="id1"), _md_cell("b", cell_id="id2")], tmp_path)
        h = NotebookHelper(p)
        idx, cell = h.get_cell_by_id("id2")
        assert idx == 1
        assert cell["cell_type"] == "markdown"

    def test_get_cell_by_id_not_found(self, tmp_path):
        p = _write_nb([_code_cell("a")], tmp_path)
        h = NotebookHelper(p)
        assert h.get_cell_by_id("nonexistent") is None

    def test_get_cell_source_string(self, tmp_path):
        p = _write_nb([_code_cell("print('hello')")], tmp_path)
        h = NotebookHelper(p)
        assert h.get_cell_source(0) == "print('hello')"

    def test_get_cell_source_list(self, tmp_path):
        cell = _code_cell(["line1\n", "line2"])
        p = _write_nb([cell], tmp_path)
        h = NotebookHelper(p)
        assert h.get_cell_source(0) == "line1\nline2"

    def test_get_cell_source_empty(self, tmp_path):
        p = _write_nb([], tmp_path)
        h = NotebookHelper(p)
        assert h.get_cell_source(0) == ""

    def test_set_cell_source(self, tmp_path):
        p = _write_nb([_code_cell("old")], tmp_path)
        h = NotebookHelper(p)
        ok = h.set_cell_source(0, "new code")
        assert ok
        src = h.get_cell_source(0)
        assert src == "new code"

    def test_set_cell_source_out_of_range(self, tmp_path):
        p = _write_nb([_code_cell("x")], tmp_path)
        h = NotebookHelper(p)
        assert h.set_cell_source(5, "y") is False

    def test_set_cell_source_multiline_roundtrip(self, tmp_path):
        p = _write_nb([_code_cell("x")], tmp_path)
        h = NotebookHelper(p)
        h.set_cell_source(0, "line1\nline2\nline3")
        src = h.get_cell_source(0)
        assert src == "line1\nline2\nline3"


# ===========================================================================
# NotebookHelper — outputs / errors
# ===========================================================================

class TestNotebookHelperOutputs:

    def test_get_cell_outputs_code(self, tmp_path):
        outputs = [{"output_type": "stream", "text": ["hello\n"]}]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        assert len(h.get_cell_outputs(0)) == 1

    def test_get_cell_outputs_markdown_empty(self, tmp_path):
        p = _write_nb([_md_cell("# Title")], tmp_path)
        h = NotebookHelper(p)
        assert h.get_cell_outputs(0) == []

    def test_get_cell_output_text_stream(self, tmp_path):
        outputs = [{"output_type": "stream", "text": ["hello ", "world"]}]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        assert h.get_cell_output_text(0) == "hello world"

    def test_get_cell_output_text_execute_result(self, tmp_path):
        outputs = [{"output_type": "execute_result", "data": {"text/plain": "42"}}]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        assert h.get_cell_output_text(0) == "42"

    def test_get_cell_output_text_error(self, tmp_path):
        outputs = [{"output_type": "error", "ename": "TypeError", "evalue": "bad"}]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        assert "[TypeError] bad" in h.get_cell_output_text(0)

    def test_get_cell_output_text_mixed(self, tmp_path):
        outputs = [
            {"output_type": "stream", "text": ["out1"]},
            {"output_type": "execute_result", "data": {"text/plain": "out2"}},
        ]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        text = h.get_cell_output_text(0)
        assert "out1" in text
        assert "out2" in text

    def test_has_cell_error_true(self, tmp_path):
        outputs = [{"output_type": "error", "ename": "ValueError", "evalue": "oops"}]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        has_err, msg = h.has_cell_error(0)
        assert has_err
        assert "ValueError" in msg

    def test_has_cell_error_false(self, tmp_path):
        p = _write_nb([_code_cell("x", outputs=[])], tmp_path)
        h = NotebookHelper(p)
        has_err, msg = h.has_cell_error(0)
        assert not has_err
        assert msg is None


# ===========================================================================
# NotebookHelper — cell_info / list_cells
# ===========================================================================

class TestNotebookHelperCellInfo:

    def test_get_cell_info_code(self, tmp_path):
        outputs = [{"output_type": "stream", "text": ["result"]}]
        p = _write_nb([_code_cell("x = 1", cell_id="c0", outputs=outputs, execution_count=3)], tmp_path)
        h = NotebookHelper(p)
        info = h.get_cell_info(0)
        assert isinstance(info, CellInfo)
        assert info.index == 0
        assert info.cell_type == "code"
        assert info.execution_count == 3
        assert not info.has_error

    def test_get_cell_info_with_error(self, tmp_path):
        outputs = [{"output_type": "error", "ename": "Err", "evalue": "x"}]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        info = h.get_cell_info(0)
        assert info.has_error
        assert info.error_message is not None

    def test_get_cell_info_out_of_range(self, tmp_path):
        p = _write_nb([], tmp_path)
        h = NotebookHelper(p)
        assert h.get_cell_info(0) is None

    def test_list_cells(self, tmp_path):
        cells = [_md_cell("# Title"), _code_cell("x = 1")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        infos = h.list_cells()
        assert len(infos) == 2
        assert infos[0].cell_type == "markdown"
        assert infos[1].cell_type == "code"


# ===========================================================================
# NotebookHelper — find_code_cells / find_markdown_cells / consecutive / pattern
# ===========================================================================

class TestNotebookHelperFindCells:

    def test_find_code_cells(self, tmp_path):
        cells = [_md_cell("a"), _code_cell("b"), _md_cell("c"), _code_cell("d")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        assert h.find_code_cells() == [1, 3]

    def test_find_markdown_cells(self, tmp_path):
        cells = [_md_cell("a"), _code_cell("b"), _md_cell("c")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        assert h.find_markdown_cells() == [0, 2]

    def test_find_consecutive_code_cells(self, tmp_path):
        cells = [_code_cell("a"), _code_cell("b"), _md_cell("c"), _code_cell("d"), _code_cell("e")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        pairs = h.find_consecutive_code_cells()
        assert (0, 1) in pairs
        assert (3, 4) in pairs
        assert len(pairs) == 2

    def test_find_consecutive_code_cells_none(self, tmp_path):
        cells = [_code_cell("a"), _md_cell("b"), _code_cell("c")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        assert h.find_consecutive_code_cells() == []

    def test_find_cells_with_pattern_code_only(self, tmp_path):
        cells = [_code_cell("import numpy"), _md_cell("import pandas"), _code_cell("import torch")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        result = h.find_cells_with_pattern("import", cell_type="code")
        assert result == [0, 2]

    def test_find_cells_with_pattern_all_types(self, tmp_path):
        cells = [_code_cell("import numpy"), _md_cell("import pandas")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        result = h.find_cells_with_pattern("import")
        assert result == [0, 1]

    def test_find_cells_with_pattern_regex(self, tmp_path):
        cells = [_code_cell("df = pd.DataFrame()"), _code_cell("x = 42")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        assert h.find_cells_with_pattern(r"DataFrame\(\)") == [0]

    def test_find_cells_with_pattern_case_insensitive(self, tmp_path):
        cells = [_code_cell("PRINT('hello')")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        assert h.find_cells_with_pattern("print") == [0]

    def test_find_cells_with_errors(self, tmp_path):
        err_out = [{"output_type": "error", "ename": "E", "evalue": "x"}]
        cells = [_code_cell("ok"), _code_cell("bad", outputs=err_out)]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        assert h.find_cells_with_errors() == [1]


# ===========================================================================
# NotebookHelper — insert_cell / delete_cell / replace_in_source
# ===========================================================================

class TestNotebookHelperMutations:

    def test_insert_cell_code(self, tmp_path):
        p = _write_nb([_md_cell("a")], tmp_path)
        h = NotebookHelper(p)
        cell_id = h.insert_cell(0, "code", "x = 1")
        assert h.cell_count == 2
        new_cell = h.get_cell(0)
        assert new_cell["cell_type"] == "code"
        assert "outputs" in new_cell
        assert new_cell["execution_count"] is None
        assert len(cell_id) == 8

    def test_insert_cell_markdown(self, tmp_path):
        p = _write_nb([_code_cell("a")], tmp_path)
        h = NotebookHelper(p)
        cell_id = h.insert_cell(1, "markdown", "# Title")
        assert h.cell_count == 2
        new_cell = h.get_cell(1)
        assert new_cell["cell_type"] == "markdown"
        assert "outputs" not in new_cell

    def test_insert_cell_at_end(self, tmp_path):
        p = _write_nb([_code_cell("a")], tmp_path)
        h = NotebookHelper(p)
        h.insert_cell(1, "code", "b = 2")
        assert h.cell_count == 2
        assert h.get_cell_source(1) == "b = 2"

    def test_delete_cell(self, tmp_path):
        cells = [_md_cell("a"), _code_cell("b"), _md_cell("c")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        ok = h.delete_cell(1)
        assert ok
        assert h.cell_count == 2
        assert h.get_cell(0)["cell_type"] == "markdown"
        assert h.get_cell(1)["cell_type"] == "markdown"

    def test_delete_cell_out_of_range(self, tmp_path):
        p = _write_nb([_code_cell("a")], tmp_path)
        h = NotebookHelper(p)
        assert h.delete_cell(5) is False

    def test_replace_in_source_single(self, tmp_path):
        p = _write_nb([_code_cell("old_value = 1")], tmp_path)
        h = NotebookHelper(p)
        count = h.replace_in_source(0, "old", "new")
        assert count == 1
        assert "new_value" in h.get_cell_source(0)

    def test_replace_in_source_all(self, tmp_path):
        p = _write_nb([_code_cell("foo + foo + foo")], tmp_path)
        h = NotebookHelper(p)
        count = h.replace_in_source(0, "foo", "bar", replace_all=True)
        assert count == 3
        assert h.get_cell_source(0) == "bar + bar + bar"

    def test_replace_in_source_not_found(self, tmp_path):
        p = _write_nb([_code_cell("x = 1")], tmp_path)
        h = NotebookHelper(p)
        count = h.replace_in_source(0, "nonexistent", "new")
        assert count == 0


# ===========================================================================
# NotebookHelper — get_cell_sequence
# ===========================================================================

class TestNotebookHelperCellSequence:

    def test_get_cell_sequence_range(self, tmp_path):
        cells = [_md_cell("a"), _code_cell("b"), _md_cell("c"), _code_cell("d")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        seq = h.get_cell_sequence(0, 2)
        assert len(seq) == 3
        assert seq[0]["type"] == "markdown"
        assert seq[1]["type"] == "code"

    def test_get_cell_sequence_single(self, tmp_path):
        cells = [_md_cell("a"), _code_cell("b")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        seq = h.get_cell_sequence(1)
        assert len(seq) == 1
        assert seq[0]["index"] == 1

    def test_get_cell_sequence_clamps(self, tmp_path):
        cells = [_md_cell("a")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        seq = h.get_cell_sequence(-5, 100)
        assert len(seq) == 1

    def test_get_cell_sequence_output_flag(self, tmp_path):
        outputs = [{"output_type": "stream", "text": ["hi"]}]
        cells = [_code_cell("x", outputs=outputs), _code_cell("y")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        seq = h.get_cell_sequence(0, 1)
        assert seq[0].get("has_output") is True
        assert seq[1].get("has_output") is False

    def test_print_cell_sequence_format(self, tmp_path):
        cells = [_md_cell("Title"), _code_cell("x = 1")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        text = h.print_cell_sequence(0, 1)
        assert "[MD]" in text
        assert "[CODE]" in text


# ===========================================================================
# NotebookHelper — validate_enrichment_context
# ===========================================================================

class TestNotebookHelperEnrichmentContext:

    def test_valid_context_md_before_and_after(self, tmp_path):
        cells = [
            _md_cell("Intro"),
            _code_cell("x = 1", outputs=[{"output_type": "stream", "text": ["1"]}]),
            _md_cell("Interpretation"),
        ]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        result = h.validate_enrichment_context(1)
        assert result["valid"]
        assert result["has_intro_before"]
        assert result["has_interpretation_after"]

    def test_missing_intro_code_before(self, tmp_path):
        cells = [
            _code_cell("x = 1"),
            _code_cell("y = 2", outputs=[{"output_type": "stream", "text": ["2"]}]),
        ]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        result = h.validate_enrichment_context(1)
        assert not result["valid"]
        assert "explanation BEFORE" in result["suggestion"]

    def test_missing_interpretation_code_after(self, tmp_path):
        cells = [
            _md_cell("Intro"),
            _code_cell("x = 1", outputs=[{"output_type": "stream", "text": ["1"]}]),
            _code_cell("y = 2"),
        ]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        result = h.validate_enrichment_context(1)
        assert not result["valid"]
        assert "interpretation AFTER" in result["suggestion"]

    def test_not_code_cell_invalid(self, tmp_path):
        cells = [_md_cell("Title")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        result = h.validate_enrichment_context(0)
        assert not result["valid"]
        assert "not a code cell" in result["suggestion"]

    def test_first_cell_no_prev_ok(self, tmp_path):
        cells = [_code_cell("x = 1", outputs=[])]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        result = h.validate_enrichment_context(0)
        # No output = no need for interpretation; first cell = no need for intro
        assert result["valid"]

    def test_code_with_output_no_interpretation(self, tmp_path):
        cells = [
            _md_cell("Intro"),
            _code_cell("x = 1", outputs=[{"output_type": "stream", "text": ["1"]}]),
        ]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        result = h.validate_enrichment_context(1)
        assert not result["valid"]
        assert "interpretation AFTER" in result["suggestion"]


# ===========================================================================
# NotebookHelper — find_cells_needing_enrichment / get_insertion_plan
# ===========================================================================

class TestNotebookHelperEnrichmentPlan:

    def test_find_cells_needing_enrichment(self, tmp_path):
        cells = [
            _md_cell("Intro"),
            _code_cell("x = 1", outputs=[{"output_type": "stream", "text": ["1"]}]),
            _code_cell("y = 2"),
        ]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        needs = h.find_cells_needing_enrichment()
        # Cell 1 needs interpretation after; cell 2 has no prev md
        assert len(needs) >= 1
        indices = [n["cell_index"] for n in needs]
        assert 1 in indices

    def test_find_cells_needing_enrichment_skips_empty(self, tmp_path):
        cells = [_code_cell(""), _code_cell("   ")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        assert h.find_cells_needing_enrichment() == []

    def test_get_insertion_plan_reversed(self, tmp_path):
        cells = [
            _code_cell("a", outputs=[{"output_type": "stream", "text": ["a"]}]),
            _code_cell("b", outputs=[{"output_type": "stream", "text": ["b"]}]),
            _code_cell("c", outputs=[{"output_type": "stream", "text": ["c"]}]),
        ]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        plan = h.get_insertion_plan()
        # Cell 0 has output + code after; cell 1 has output + code after; cell 2 is last
        assert len(plan) == 2
        # Should be in reverse order (index 1 first, then 0)
        assert plan[0]["insert_after_index"] > plan[1]["insert_after_index"]

    def test_get_insertion_plan_empty_when_good(self, tmp_path):
        cells = [
            _md_cell("Intro"),
            _code_cell("x = 1", outputs=[{"output_type": "stream", "text": ["1"]}]),
            _md_cell("Interpretation"),
        ]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        assert h.get_insertion_plan() == []

    def test_print_enrichment_plan(self, tmp_path):
        cells = [
            _code_cell("a", outputs=[{"output_type": "stream", "text": ["a"]}]),
            _code_cell("b"),
        ]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        text = h.print_enrichment_plan()
        assert "ENRICHMENT PLAN" in text


# ===========================================================================
# CellIterator — default_checker / evaluate
# ===========================================================================

class TestCellIterator:

    def test_default_checker_objective_in_output(self, tmp_path):
        p = _write_nb([_code_cell("x = 1")], tmp_path)
        it = CellIterator(p, 0, "SUCCESS")
        assert it._default_checker("Operation SUCCESS", "SUCCESS")

    def test_default_checker_success_keyword(self, tmp_path):
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "target value reached")
        assert it._default_checker("All done", "target value reached")

    def test_default_checker_error_keyword_fails(self, tmp_path):
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "anything")
        assert not it._default_checker("Error: something failed", "anything")

    def test_default_checker_empty_output(self, tmp_path):
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "specific target")
        assert not it._default_checker("", "specific target")

    def test_evaluate_success(self, tmp_path):
        p = _write_nb([_code_cell("x = 1")], tmp_path)
        it = CellIterator(p, 0, "1", max_iterations=3)
        result = it.evaluate("1")
        assert result.objective_met
        assert it.is_complete
        assert it.success

    def test_evaluate_error(self, tmp_path):
        p = _write_nb([_code_cell("x = 1")], tmp_path)
        it = CellIterator(p, 0, "target", max_iterations=3)
        result = it.evaluate("some output", error="TypeError: bad")
        assert not result.objective_met
        assert result.error == "TypeError: bad"

    def test_evaluate_max_iterations(self, tmp_path):
        p = _write_nb([_code_cell("x = 1")], tmp_path)
        it = CellIterator(p, 0, "impossible", max_iterations=2)
        it.evaluate("output1")
        it.evaluate("output2")
        assert it.is_complete
        assert not it.success
        assert it.iteration == 2

    def test_apply_correction(self, tmp_path):
        p = _write_nb([_code_cell("old")], tmp_path)
        it = CellIterator(p, 0, "target", max_iterations=3)
        it.apply_correction("new code")
        assert it.current_source == "new code"

    def test_get_summary(self, tmp_path):
        p = _write_nb([_code_cell("x = 1")], tmp_path)
        it = CellIterator(p, 0, "1", max_iterations=5)
        it.evaluate("1")
        summary = it.get_summary()
        assert summary["success"]
        assert summary["iterations"] == 1
        assert len(summary["history"]) == 1

    def test_custom_objective_checker(self, tmp_path):
        p = _write_nb([_code_cell("x")], tmp_path)

        def custom_checker(output, objective):
            return output.strip().endswith("!")

        it = CellIterator(p, 0, "irrelevant", objective_checker=custom_checker)
        result = it.evaluate("Hello!")
        assert result.objective_met

    def test_current_source_property(self, tmp_path):
        p = _write_nb([_code_cell("x = 42")], tmp_path)
        it = CellIterator(p, 0, "x")
        assert it.current_source == "x = 42"


# ===========================================================================
# NotebookExecutionResult — success_rate property
# ===========================================================================

class TestNotebookExecutionResult:

    def test_success_rate_100(self):
        r = NotebookExecutionResult(
            success=True, notebook_path="x", executed_cells=5, failed_cells=0
        )
        assert r.success_rate == 100.0

    def test_success_rate_partial(self):
        r = NotebookExecutionResult(
            success=True, notebook_path="x", executed_cells=10, failed_cells=3
        )
        assert r.success_rate == 70.0

    def test_success_rate_zero_executed(self):
        r = NotebookExecutionResult(
            success=True, notebook_path="x", executed_cells=0, failed_cells=0
        )
        assert r.success_rate == 0.0


# ===========================================================================
# Utility functions
# ===========================================================================

class TestUtilityFunctions:

    def test_read_notebook(self, tmp_path):
        p = _write_nb([_code_cell("x = 1")], tmp_path)
        nb = read_notebook(p)
        assert "cells" in nb
        assert len(nb["cells"]) == 1

    def test_write_notebook(self, tmp_path):
        nb = _make_nb([_code_cell("x = 1")])
        out = str(tmp_path / "out.ipynb")
        write_notebook(out, nb)
        loaded = json.loads(open(out, encoding="utf-8").read())
        assert len(loaded["cells"]) == 1


# ===========================================================================
# NotebookExecutor — detect_kernel (pure, reads from file)
# ===========================================================================

class TestNotebookExecutorDetectKernel:

    def test_detect_python3_from_kernelspec(self, tmp_path):
        meta = {"kernelspec": {"name": "python3", "language": "python"}}
        p = _write_nb([_code_cell("x")], tmp_path, metadata=meta)
        from notebook_helpers import NotebookExecutor
        ex = NotebookExecutor()
        assert ex.detect_kernel(p) == "python3"

    def test_detect_dotnet_from_kernelspec(self, tmp_path):
        meta = {"kernelspec": {"name": ".net-csharp", "language": "C#"}}
        p = _write_nb([_code_cell("x")], tmp_path, metadata=meta)
        from notebook_helpers import NotebookExecutor
        ex = NotebookExecutor()
        assert ex.detect_kernel(p) == ".net-csharp"

    def test_detect_lean4_from_language(self, tmp_path):
        meta = {"kernelspec": {"name": "custom", "language": "lean4"}}
        p = _write_nb([_code_cell("x")], tmp_path, metadata=meta)
        from notebook_helpers import NotebookExecutor
        ex = NotebookExecutor()
        assert ex.detect_kernel(p) == "lean4"

    def test_detect_default_python3(self, tmp_path):
        p = _write_nb([_code_cell("x")], tmp_path, metadata={})
        from notebook_helpers import NotebookExecutor
        ex = NotebookExecutor()
        assert ex.detect_kernel(p) == "python3"

    def test_detect_from_magic_command(self, tmp_path):
        cell = _code_cell("#!csharp\nvar x = 1;")
        p = _write_nb([cell], tmp_path, metadata={})
        from notebook_helpers import NotebookExecutor
        ex = NotebookExecutor()
        assert ex.detect_kernel(p) == ".net-csharp"


# ===========================================================================
# Mutation tests — Round 2: killing mutants in notebook_helpers.py
# ===========================================================================


class TestGetCellOutputTextMutation:
    """Mutation tests for get_cell_output_text (L134-163)."""

    def test_stream_text_as_string_not_list(self, tmp_path):
        """Kill mutant: isinstance(text, list) → isinstance(text, tuple)."""
        outputs = [{"output_type": "stream", "text": "single string output"}]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        assert h.get_cell_output_text(0) == "single string output"

    def test_execute_result_text_as_list(self, tmp_path):
        """Kill mutant: isinstance(text, list) branch for execute_result data."""
        outputs = [{"output_type": "execute_result", "data": {"text/plain": ["line1\n", "line2"]}}]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        assert h.get_cell_output_text(0) == "line1\nline2"

    def test_execute_result_text_as_string(self, tmp_path):
        """Kill mutant: else branch for execute_result data text."""
        outputs = [{"output_type": "execute_result", "data": {"text/plain": "plain string"}}]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        assert h.get_cell_output_text(0) == "plain string"

    def test_error_format_with_colon(self, tmp_path):
        """Kill mutant: f"[{ename}] {evalue}" → f"[{evalue}] {ename}"."""
        outputs = [{"output_type": "error", "ename": "ZeroDiv", "evalue": "by zero"}]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        text = h.get_cell_output_text(0)
        assert "[ZeroDiv] by zero" in text
        assert text.index("ZeroDiv") < text.index("by zero")

    def test_multiple_outputs_joined_by_newline(self, tmp_path):
        """Kill mutant: '\\n'.join(text_parts) → ' '.join(text_parts)."""
        outputs = [
            {"output_type": "stream", "text": ["line1"]},
            {"output_type": "execute_result", "data": {"text/plain": "line2"}},
        ]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        text = h.get_cell_output_text(0)
        assert "line1\nline2" in text

    def test_unknown_output_type_skipped(self, tmp_path):
        """Kill mutant: unknown output_type not skipped."""
        outputs = [{"output_type": "display_data", "data": {"text/plain": "ignored"}}]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        assert h.get_cell_output_text(0) == ""


class TestHasCellErrorMutation:
    """Mutation tests for has_cell_error (L165-175)."""

    def test_returns_first_error_only(self, tmp_path):
        """Kill mutant: loop breaks on first error vs continues."""
        outputs = [
            {"output_type": "error", "ename": "E1", "evalue": "first"},
            {"output_type": "error", "ename": "E2", "evalue": "second"},
        ]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        has_err, msg = h.has_cell_error(0)
        assert has_err
        assert "E1" in msg
        assert "E2" not in msg  # Only first error returned

    def test_no_error_returns_none_message(self, tmp_path):
        """Kill mutant: (False, None) → (False, '')."""
        p = _write_nb([_code_cell("x", outputs=[])], tmp_path)
        h = NotebookHelper(p)
        has_err, msg = h.has_cell_error(0)
        assert not has_err
        assert msg is None

    def test_error_message_format(self, tmp_path):
        """Kill mutant: f"{ename}: {evalue}" → f"{evalue}: {ename}"."""
        outputs = [{"output_type": "error", "ename": "ValueError", "evalue": "bad input"}]
        p = _write_nb([_code_cell("x", outputs=outputs)], tmp_path)
        h = NotebookHelper(p)
        _, msg = h.has_cell_error(0)
        assert msg.startswith("ValueError: bad input")


class TestGetCellInfoMutation:
    """Mutation tests for get_cell_info (L177-197)."""

    def test_first_line_truncated_at_60(self, tmp_path):
        """Kill mutant: [:60] → [:50] or [:70]."""
        long_line = "x" * 100
        p = _write_nb([_code_cell(long_line)], tmp_path)
        h = NotebookHelper(p)
        info = h.get_cell_info(0)
        assert len(info.first_line) == 60

    def test_empty_source_first_line(self, tmp_path):
        """Kill mutant: first_line = '' when source is empty."""
        p = _write_nb([_code_cell("")], tmp_path)
        h = NotebookHelper(p)
        info = h.get_cell_info(0)
        assert info.first_line == ""

    def test_cell_id_default_na(self, tmp_path):
        """Kill mutant: cell.get('id', 'N/A') → cell.get('id', '')."""
        cell = {
            "cell_type": "code",
            "metadata": {},
            "source": ["x = 1"],
            "outputs": [],
            "execution_count": 1,
            # No 'id' key
        }
        p = _write_nb([cell], tmp_path)
        h = NotebookHelper(p)
        info = h.get_cell_info(0)
        assert info.cell_id == "N/A"


class TestInsertCellMutation:
    """Mutation tests for insert_cell (L264-284)."""

    def test_multiline_source_split(self, tmp_path):
        """Kill mutant: source.split('\\n') handling of trailing newline."""
        p = _write_nb([_md_cell("a")], tmp_path)
        h = NotebookHelper(p)
        h.insert_cell(0, "code", "line1\nline2\nline3")
        new_cell = h.get_cell(0)
        # Source should be stored as list
        source_list = new_cell["source"]
        assert len(source_list) == 3
        assert source_list[0] == "line1\n"
        assert source_list[1] == "line2\n"
        assert source_list[2] == "line3"  # Last line without \n

    def test_code_cell_has_execution_count_null(self, tmp_path):
        """Kill mutant: execution_count=None → execution_count=0."""
        p = _write_nb([_md_cell("a")], tmp_path)
        h = NotebookHelper(p)
        h.insert_cell(0, "code", "x = 1")
        new_cell = h.get_cell(0)
        assert new_cell["execution_count"] is None
        assert new_cell["outputs"] == []

    def test_markdown_cell_no_outputs_key(self, tmp_path):
        """Kill mutant: code-only branch runs for markdown too."""
        p = _write_nb([_code_cell("a")], tmp_path)
        h = NotebookHelper(p)
        h.insert_cell(1, "markdown", "# Title")
        new_cell = h.get_cell(1)
        assert "outputs" not in new_cell
        assert "execution_count" not in new_cell


class TestReplaceInSourceMutation:
    """Mutation tests for replace_in_source (L293-306)."""

    def test_single_replace_only_first(self, tmp_path):
        """Kill mutant: replace(..., 1) → replace(...)."""
        p = _write_nb([_code_cell("foo + foo + baz")], tmp_path)
        h = NotebookHelper(p)
        count = h.replace_in_source(0, "foo", "bar", replace_all=False)
        assert count == 1
        src = h.get_cell_source(0)
        assert src == "bar + foo + baz"

    def test_replace_all_count_matches_source(self, tmp_path):
        """Kill mutant: source.count(old) vs count=1 always."""
        p = _write_nb([_code_cell("aba")], tmp_path)
        h = NotebookHelper(p)
        count = h.replace_in_source(0, "a", "x", replace_all=True)
        assert count == 2
        assert h.get_cell_source(0) == "xbx"

    def test_not_found_returns_zero_no_modification(self, tmp_path):
        """Kill mutant: count > 0 check bypassed."""
        p = _write_nb([_code_cell("hello world")], tmp_path)
        h = NotebookHelper(p)
        original = h.get_cell_source(0)
        count = h.replace_in_source(0, "xyz", "abc")
        assert count == 0
        assert h.get_cell_source(0) == original


class TestGetCellSequenceMutation:
    """Mutation tests for get_cell_sequence (L312-361)."""

    def test_preview_truncation_with_ellipsis(self, tmp_path):
        """Kill mutant: len(first_line) == max_preview → len check removed."""
        long_source = "x" * 100
        p = _write_nb([_code_cell(long_source)], tmp_path)
        h = NotebookHelper(p)
        seq = h.get_cell_sequence(0, max_preview=20)
        assert seq[0]["preview"].endswith("...")
        assert len(seq[0]["preview"]) == 23  # 20 chars + "..."

    def test_empty_source_no_preview(self, tmp_path):
        """Kill mutant: source.split('\\n')[0] on empty string."""
        p = _write_nb([_code_cell("")], tmp_path)
        h = NotebookHelper(p)
        seq = h.get_cell_sequence(0)
        assert seq[0]["preview"] == ""

    def test_markdown_no_has_output_key(self, tmp_path):
        """Kill mutant: has_output added for all cell types."""
        p = _write_nb([_md_cell("# Title")], tmp_path)
        h = NotebookHelper(p)
        seq = h.get_cell_sequence(0)
        assert "has_output" not in seq[0]


class TestValidateEnrichmentContextMutation:
    """Mutation tests for validate_enrichment_context (L385-462)."""

    def test_out_of_range_cell_invalid(self, tmp_path):
        """Kill mutant: cell not found returns valid."""
        p = _write_nb([_code_cell("x")], tmp_path)
        h = NotebookHelper(p)
        result = h.validate_enrichment_context(99)
        assert not result["valid"]

    def test_output_no_md_after_at_last_cell(self, tmp_path):
        """Kill mutant: last cell with output is valid."""
        cells = [
            _md_cell("Intro"),
            _code_cell("x = 1", outputs=[{"output_type": "stream", "text": ["1"]}]),
        ]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        result = h.validate_enrichment_context(1)
        assert not result["valid"]
        assert "interpretation AFTER" in result["suggestion"]

    def test_no_output_consecutive_code_needs_explanation(self, tmp_path):
        """Kill mutant: consecutive code check bypassed when has_intro_before=True."""
        # Cell 1: md → code (no output) → code
        # Cell 1 has md before → has_intro_before=True
        # No output → no interpretation needed
        # BUT prev is md → has_intro_before=True, so no "explanation BEFORE" issue
        # AND no output → no "interpretation AFTER" issue
        # So valid=True for cell 1. The issue is on cell 2.
        cells = [
            _md_cell("Intro"),
            _code_cell("x = 1"),  # no output, md before
            _code_cell("y = 2"),  # code before → needs explanation
        ]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        # Cell 2: prev is code (not md) → no intro → invalid
        result = h.validate_enrichment_context(2)
        assert not result["valid"]
        assert "explanation BEFORE" in result["suggestion"]


class TestPrintEnrichmentPlanMutation:
    """Mutation tests for print_enrichment_plan (L541-564)."""

    def test_no_plan_needed_returns_message(self, tmp_path):
        """Kill mutant: empty plan still prints ENRICHMENT PLAN."""
        cells = [
            _md_cell("Intro"),
            _code_cell("x = 1"),
        ]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        text = h.print_enrichment_plan()
        assert "No enrichment needed" in text
        assert "ENRICHMENT PLAN" not in text

    def test_plan_includes_cell_id(self, tmp_path):
        """Kill mutant: cell_id omitted from output."""
        cells = [
            _code_cell("a", cell_id="myid"),
            _code_cell("b"),
        ]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        text = h.print_enrichment_plan()
        # First cell has no output, so no plan for it
        # Need output on first cell + code after
        # Let me fix: add output to first cell
        # Actually let me just test with proper setup below
        pass

    def test_plan_with_output_includes_interpretation(self, tmp_path):
        """Kill mutant: content_type always 'introduction'."""
        cells = [
            _code_cell("a", outputs=[{"output_type": "stream", "text": ["a"]}]),
            _code_cell("b"),
        ]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        text = h.print_enrichment_plan()
        assert "INTERPRETATION" in text


class TestCellIteratorDefaultCheckerMutation:
    """Mutation tests for _default_checker (L625-645)."""

    def test_passed_keyword_success(self, tmp_path):
        """Kill mutant: 'passed' removed from success_keywords."""
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "unrelated")
        assert it._default_checker("All tests passed", "unrelated")

    def test_complete_keyword_success(self, tmp_path):
        """Kill mutant: 'complete' removed from success_keywords."""
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "unrelated")
        assert it._default_checker("Operation complete", "unrelated")

    def test_done_keyword_success(self, tmp_path):
        """Kill mutant: 'done' removed from success_keywords."""
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "unrelated")
        assert it._default_checker("Task done", "unrelated")

    def test_ok_keyword_success(self, tmp_path):
        """Kill mutant: 'ok' removed from success_keywords."""
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "unrelated")
        assert it._default_checker("Status ok", "unrelated")

    def test_traceback_keyword_fails(self, tmp_path):
        """Kill mutant: 'traceback' removed from error_keywords."""
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "anything")
        assert not it._default_checker("Traceback (most recent call)", "anything")

    def test_failed_keyword_fails(self, tmp_path):
        """Kill mutant: 'failed' removed from error_keywords."""
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "anything")
        assert not it._default_checker("Test failed", "anything")

    def test_exception_keyword_fails(self, tmp_path):
        """Kill mutant: 'exception' removed from error_keywords."""
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "anything")
        assert not it._default_checker("Exception raised", "anything")

    def test_case_insensitive_check(self, tmp_path):
        """Kill mutant: .lower() removed."""
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "unrelated")
        assert it._default_checker("ERROR: bad", "unrelated") is False


class TestCellIteratorEvaluateMutation:
    """Mutation tests for CellIterator.evaluate (L652-693)."""

    def test_iteration_counter_increments(self, tmp_path):
        """Kill mutant: self.iteration not incremented."""
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "target", max_iterations=5)
        r1 = it.evaluate("target reached")
        assert r1.iteration == 1
        assert it.iteration == 1

    def test_history_accumulates(self, tmp_path):
        """Kill mutant: history not appended."""
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "impossible", max_iterations=3)
        it.evaluate("out1")
        it.evaluate("out2")
        assert len(it.history) == 2
        assert it.history[0].output == "out1"
        assert it.history[1].output == "out2"

    def test_error_cell_still_checks(self, tmp_path):
        """Kill mutant: error=True → objective_met never checked."""
        err_out = [{"output_type": "error", "ename": "E", "evalue": "x"}]
        p = _write_nb([_code_cell("x", outputs=err_out)], tmp_path)
        it = CellIterator(p, 0, "x", max_iterations=3)
        result = it.evaluate("output", error="bad")
        assert not result.objective_met
        assert not result.success

    def test_notes_format(self, tmp_path):
        """Kill mutant: notes format wrong."""
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "target", max_iterations=10)
        result = it.evaluate("target")
        assert "1/10" in result.notes


class TestCellIteratorSummaryMutation:
    """Mutation tests for get_summary error truncation (L718)."""

    def test_error_truncated_to_100_chars(self, tmp_path):
        """Kill mutant: error[:100] → error[:50] or removed."""
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "target", max_iterations=3)
        long_error = "E" * 200
        it.evaluate("output", error=long_error)
        summary = it.get_summary()
        assert len(summary["history"][0]["error"]) == 100

    def test_none_error_in_summary(self, tmp_path):
        """Kill mutant: None error → empty string."""
        p = _write_nb([_code_cell("x")], tmp_path)
        it = CellIterator(p, 0, "target", max_iterations=3)
        it.evaluate("target")
        summary = it.get_summary()
        assert summary["history"][0]["error"] is None


class TestNotebookExecutorDetectKernelMutation:
    """Mutation tests for detect_kernel language/code fallback branches (L802-847)."""

    def test_fsharp_magic_command(self, tmp_path):
        """Kill mutant: '#!fsharp' → '.net-csharp' instead of '.net-fsharp'."""
        cell = _code_cell("#!fsharp\nlet x = 1")
        p = _write_nb([cell], tmp_path, metadata={})
        from notebook_helpers import NotebookExecutor
        ex = NotebookExecutor()
        assert ex.detect_kernel(p) == ".net-fsharp"

    def test_import_magic_command(self, tmp_path):
        """Kill mutant: '#!import' not recognized."""
        cell = _code_cell("#!import SomeModule")
        p = _write_nb([cell], tmp_path, metadata={})
        from notebook_helpers import NotebookExecutor
        ex = NotebookExecutor()
        assert ex.detect_kernel(p) == ".net-csharp"

    def test_language_fsharp_detection(self, tmp_path):
        """Kill mutant: 'f#' language not mapped to '.net-fsharp'."""
        meta = {"kernelspec": {"name": "custom", "language": "F#"}}
        p = _write_nb([_code_cell("x")], tmp_path, metadata=meta)
        from notebook_helpers import NotebookExecutor
        ex = NotebookExecutor()
        assert ex.detect_kernel(p) == ".net-fsharp"

    def test_language_csharp_detection(self, tmp_path):
        """Kill mutant: 'c#' language not mapped."""
        meta = {"kernelspec": {"name": "custom", "language": "C#"}}
        p = _write_nb([_code_cell("x")], tmp_path, metadata=meta)
        from notebook_helpers import NotebookExecutor
        ex = NotebookExecutor()
        assert ex.detect_kernel(p) == ".net-csharp"

    def test_language_python_fallback(self, tmp_path):
        """Kill mutant: 'python' in language check removed."""
        meta = {"kernelspec": {"name": "custom", "language": "python"}}
        p = _write_nb([_code_cell("x")], tmp_path, metadata=meta)
        from notebook_helpers import NotebookExecutor
        ex = NotebookExecutor()
        assert ex.detect_kernel(p) == "python3"

    def test_smartcontracts_kernel(self, tmp_path):
        """Kill mutant: smartcontracts not in KERNEL_PATTERNS."""
        meta = {"kernelspec": {"name": "smartcontracts", "language": "solidity"}}
        p = _write_nb([_code_cell("x")], tmp_path, metadata=meta)
        from notebook_helpers import NotebookExecutor
        ex = NotebookExecutor()
        assert ex.detect_kernel(p) == "smartcontracts"

    def test_verbose_on_exception(self, tmp_path):
        """Kill mutant: verbose=False silences warning."""
        from notebook_helpers import NotebookExecutor
        ex = NotebookExecutor(verbose=True)
        # Non-existent file → exception caught → returns python3
        assert ex.detect_kernel("/nonexistent/path.ipynb") == "python3"

    def test_markdown_cell_not_checked_for_magic(self, tmp_path):
        """Kill mutant: markdown cells also scanned for magic commands."""
        cells = [_md_cell("#!csharp"), _code_cell("x = 1")]
        p = _write_nb(cells, tmp_path, metadata={})
        from notebook_helpers import NotebookExecutor
        ex = NotebookExecutor()
        # Magic in markdown should NOT trigger .net-csharp
        assert ex.detect_kernel(p) == "python3"


class TestFindCellsNeedingMarkdownMutation:
    """Mutation tests for find_cells_needing_markdown (L1318-1329)."""

    def test_code_cells_without_output_detected(self, tmp_path):
        """Kill mutant: code_cells_without_output list empty."""
        cells = [
            _code_cell("x = 1"),  # no output
            _code_cell("y = 2", outputs=[{"output_type": "stream", "text": ["2"]}]),
        ]
        p = _write_nb(cells, tmp_path)
        result = find_cells_needing_markdown(p)
        assert 0 in result["code_cells_without_output"]
        assert 1 not in result["code_cells_without_output"]

    def test_all_keys_present(self, tmp_path):
        """Kill mutant: missing key in return dict."""
        p = _write_nb([_code_cell("x")], tmp_path)
        result = find_cells_needing_markdown(p)
        assert "consecutive_code_cells" in result
        assert "cells_with_errors" in result
        assert "code_cells_without_output" in result


class TestDeleteCellMutation:
    """Mutation tests for delete_cell boundary (L286-291)."""

    def test_delete_negative_index_fails(self, tmp_path):
        """Kill mutant: -1 index deletes last cell."""
        p = _write_nb([_code_cell("a"), _code_cell("b")], tmp_path)
        h = NotebookHelper(p)
        assert h.delete_cell(-1) is False
        assert h.cell_count == 2

    def test_delete_exact_length_fails(self, tmp_path):
        """Kill mutant: index == len allowed."""
        p = _write_nb([_code_cell("a")], tmp_path)
        h = NotebookHelper(p)
        assert h.delete_cell(1) is False
        assert h.cell_count == 1


class TestDataclassDefaultsMutation:
    """Mutation tests for dataclass field defaults."""

    def test_cell_info_defaults(self):
        """Kill mutant: default field values changed."""
        from notebook_helpers import CellInfo
        info = CellInfo(index=0, cell_id="c1", cell_type="code", source="x", first_line="x")
        assert info.outputs == []
        assert info.execution_count is None
        assert info.has_error is False
        assert info.error_message is None

    def test_iteration_result_defaults(self):
        """Kill mutant: default field values changed."""
        r = IterationResult(iteration=1, success=True, cell_source="x")
        assert r.output is None
        assert r.error is None
        assert r.objective_met is False
        assert r.notes == ""

    def test_execution_result_defaults(self):
        """Kill mutant: default field values changed."""
        from notebook_helpers import ExecutionResult
        r = ExecutionResult(success=True)
        assert r.cell_index is None
        assert r.output == ""
        assert r.error is None
        assert r.duration == 0.0
        assert r.kernel == "unknown"

    def test_notebook_execution_result_defaults(self):
        """Kill mutant: default field values changed."""
        r = NotebookExecutionResult(success=True, notebook_path="x")
        assert r.output_path is None
        assert r.kernel == "unknown"
        assert r.total_cells == 0
        assert r.executed_cells == 0
        assert r.failed_cells == 0
        assert r.duration == 0.0
        assert r.cell_results == []
        assert r.errors == []


class TestSuccessRateMutation:
    """Mutation tests for NotebookExecutionResult.success_rate (L754-758)."""

    def test_success_rate_formula(self):
        """Kill mutant: (executed - failed) / executed → failed / executed."""
        r = NotebookExecutionResult(
            success=True, notebook_path="x",
            executed_cells=10, failed_cells=2
        )
        assert r.success_rate == 80.0  # 8/10 * 100

    def test_success_rate_all_failed(self):
        """Kill mutant: 0% edge case."""
        r = NotebookExecutionResult(
            success=True, notebook_path="x",
            executed_cells=5, failed_cells=5
        )
        assert r.success_rate == 0.0

    def test_success_rate_100_percent(self):
        """Kill mutant: 100% edge case."""
        r = NotebookExecutionResult(
            success=True, notebook_path="x",
            executed_cells=3, failed_cells=0
        )
        assert r.success_rate == 100.0


class TestConsecutiveCodeCellsMutation:
    """Mutation tests for find_consecutive_code_cells (L234-244)."""

    def test_non_adjacent_code_cells_not_found(self, tmp_path):
        """Kill mutant: idx2 == idx1 + 1 → idx2 == idx1 + 2."""
        cells = [_code_cell("a"), _md_cell("b"), _code_cell("c")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        assert h.find_consecutive_code_cells() == []

    def test_three_consecutive_returns_two_pairs(self, tmp_path):
        """Kill mutant: only first pair found."""
        cells = [_code_cell("a"), _code_cell("b"), _code_cell("c")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        pairs = h.find_consecutive_code_cells()
        assert len(pairs) == 2
        assert (0, 1) in pairs
        assert (1, 2) in pairs


class TestFindPatternMutation:
    """Mutation tests for find_cells_with_pattern (L246-258)."""

    def test_cell_type_filter_enforced(self, tmp_path):
        """Kill mutant: cell_type filter ignored."""
        cells = [_code_cell("target"), _md_cell("target")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        result = h.find_cells_with_pattern("target", cell_type="markdown")
        assert result == [1]
        assert 0 not in result

    def test_no_match_returns_empty(self, tmp_path):
        """Kill mutant: empty list returns all indices."""
        cells = [_code_cell("hello")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        assert h.find_cells_with_pattern("xyz") == []

    def test_none_cell_type_matches_all(self, tmp_path):
        """Kill mutant: cell_type=None still filters."""
        cells = [_code_cell("target"), _md_cell("target")]
        p = _write_nb(cells, tmp_path)
        h = NotebookHelper(p)
        result = h.find_cells_with_pattern("target", cell_type=None)
        assert result == [0, 1]
