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
