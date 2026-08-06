"""Tests for the per-cell C.3 scope audit (`audit_c1_c3.check_c3_scope`).

The audited property: a PR that edits one cell, re-runs the whole notebook and
commits fresh outputs for cells it never touched is staging outputs that C.3
says should not be staged. The whole-notebook `check_c3` cannot see this — one
modified cell suppresses every flag for the rest of the file.

Git is stubbed via `_cells_at_ref` so the tests stay hermetic (no repo fixture,
no network, no temporary clones).
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import audit_c1_c3  # noqa: E402


def code(source, outputs=None, execution_count=1):
    return {
        "cell_type": "code",
        "source": source if isinstance(source, list) else [source],
        "outputs": outputs or [],
        "execution_count": execution_count,
    }


def stream(text):
    return {"output_type": "stream", "name": "stdout", "text": [text]}


def error(ename="RuntimeError", evalue="boom"):
    return {"output_type": "error", "ename": ename, "evalue": evalue, "traceback": []}


@pytest.fixture
def stub_refs(monkeypatch):
    """Install a fake `_cells_at_ref` returning per-ref `(nb_index, cell)` lists.

    Cells are numbered as if a markdown cell sat before each code cell, which is
    the usual notebook shape and keeps the tests honest about the reported index
    being the notebook position rather than the code-cell ordinal.
    """

    def numbered(cells):
        return [(2 * i + 1, c) for i, c in enumerate(cells)]

    def install(base_cells, head_cells):
        def fake(rel, ref):
            if ref == "BASE":
                return numbered(base_cells)
            if ref == "HEAD":
                return numbered(head_cells)
            return None
        monkeypatch.setattr(audit_c1_c3, "_cells_at_ref", fake)

    return install


def scope(rel="nb.ipynb"):
    return audit_c1_c3.check_c3_scope(rel, "BASE", "HEAD")


def test_untouched_cell_with_identical_outputs_is_clean(stub_refs):
    cell = code("print(1)", [stream("1\n")])
    stub_refs([cell], [cell])
    assert scope() == []


def test_untouched_cell_re_executed_with_fewer_outputs_is_flagged(stub_refs):
    stub_refs(
        [code("print(1)", [stream("a"), stream("b"), stream("c")])],
        [code("print(1)", [stream("a")])],
    )
    (v,) = scope()
    assert v["severity"] == "OUTPUTS-LOST"
    assert (v["outputs_before"], v["outputs_after"]) == (3, 1)


def test_untouched_cell_gaining_error_output_is_flagged_as_lost(stub_refs):
    stub_refs(
        [code("call()", [stream("ok")])],
        [code("call()", [stream("ok"), error()])],
    )
    (v,) = scope()
    assert v["severity"] == "OUTPUTS-LOST"
    assert (v["errors_before"], v["errors_after"]) == (0, 1)


def test_untouched_cell_whose_outputs_grow_is_still_flagged(stub_refs):
    """The #8615 shape: a failing re-run grows the output count with logged errors."""
    stub_refs(
        [code("bench()", [stream("25/25 OK")])],
        [code("bench()", [stream("[ERROR] exception"), stream("[ERROR] exception")])],
    )
    (v,) = scope()
    assert v["severity"] == "OUTPUTS-REPLACED"
    assert v["outputs_after"] > v["outputs_before"]


def test_modified_source_is_not_a_c3_violation(stub_refs):
    """C.3 governs untouched cells only — an edited cell must be re-executed."""
    stub_refs(
        [code("print(1)", [stream("1")])],
        [code("print(2)", [stream("2")])],
    )
    assert scope() == []


def test_edited_cell_does_not_mask_its_untouched_neighbours(stub_refs):
    """The gap that motivated this audit: `check_c3` goes silent here.

    One edited cell is enough to make the whole-notebook check pass, so the
    untouched neighbour's destroyed outputs sail through unflagged.
    """
    stub_refs(
        [code("print(1)", [stream("1")]),
         code("heavy()", [stream("row 1"), stream("row 2"), stream("row 3")])],
        [code("print(99)", [stream("99")]),
         code("heavy()", [stream("")])],
    )
    (v,) = scope()
    assert v["cell_index"] == 3  # notebook position of the 2nd code cell
    assert v["severity"] == "OUTPUTS-LOST"


def test_duplicate_sources_are_matched_by_occurrence(stub_refs):
    """Two cells sharing a source must not collapse onto the same base cell."""
    stub_refs(
        [code("ping()", [stream("first")]), code("ping()", [stream("second")])],
        [code("ping()", [stream("first")]), code("ping()", [stream("CHANGED")])],
    )
    (v,) = scope()
    assert v["cell_index"] == 3


def test_execution_count_renumbering_alone_is_not_flagged(stub_refs):
    """Re-running a notebook renumbers cells; that alone destroys nothing."""
    stub_refs(
        [code("print(1)", [stream("1")], execution_count=3)],
        [code("print(1)", [stream("1")], execution_count=11)],
    )
    assert scope() == []


def test_appended_new_cell_is_ignored(stub_refs):
    stub_refs(
        [code("print(1)", [stream("1")])],
        [code("print(1)", [stream("1")]), code("brand_new()", [stream("out")])],
    )
    assert scope() == []


def test_notebook_absent_from_base_is_not_a_violation(monkeypatch):
    """A notebook added by the diff has no base to compare against."""
    monkeypatch.setattr(audit_c1_c3, "_cells_at_ref",
                        lambda rel, ref: None if ref == "BASE" else [(0, code("x"))])
    assert scope() == []


def test_markdown_cells_are_out_of_scope(stub_refs):
    """`_cells_at_ref` yields code cells only; markdown never reaches the matcher."""
    stub_refs([code("run()", [stream("a")])], [code("run()", [stream("a")])])
    assert scope() == []


def test_reported_index_is_the_notebook_position_not_the_code_ordinal(stub_refs):
    """A reader opens the notebook and counts cells — the index must match that.

    With markdown cells interleaved, the 3rd code cell sits at notebook index 5.
    Reporting `2` would send the reader to the wrong cell.
    """
    unchanged = code("keep()", [stream("ok")])
    stub_refs(
        [unchanged, unchanged, code("victim()", [stream("a"), stream("b")])],
        [unchanged, unchanged, code("victim()", [stream("a")])],
    )
    (v,) = scope()
    assert v["cell_index"] == 5


def test_cells_at_ref_numbers_by_notebook_position(tmp_path, monkeypatch):
    """Guards the contract at the git boundary, not just through the stub."""
    nb = {"cells": [
        {"cell_type": "markdown", "source": ["# Titre"]},
        {"cell_type": "code", "source": ["a()"], "outputs": [], "execution_count": 1},
        {"cell_type": "markdown", "source": ["texte"]},
        {"cell_type": "code", "source": ["b()"], "outputs": [], "execution_count": 2},
    ]}

    class Blob:
        returncode = 0
        stdout = json.dumps(nb).encode("utf-8")

    monkeypatch.setattr(audit_c1_c3.subprocess, "run", lambda *a, **k: Blob())
    cells = audit_c1_c3._cells_at_ref("nb.ipynb", "SOMEREF")
    assert [i for i, _ in cells] == [1, 3]


def test_outputs_signature_counts_errors_and_concatenates_text():
    cell = code("x", [stream("hello "), error("ValueError", "bad"), stream("world")])
    n_out, n_err, text = audit_c1_c3._outputs_signature(cell)
    assert (n_out, n_err) == (3, 1)
    assert "hello " in text and "world" in text and "ValueError" in text


def test_execute_result_data_is_part_of_the_signature(stub_refs):
    """A changed `text/plain` result must be detected even at equal output count."""
    def result(value):
        return {"output_type": "execute_result", "data": {"text/plain": value},
                "metadata": {}, "execution_count": 1}

    stub_refs([code("df.shape", [result("(100, 5)")])],
              [code("df.shape", [result("(0, 5)")])])
    (v,) = scope()
    assert v["severity"] == "OUTPUTS-REPLACED"
    assert v["outputs_before"] == v["outputs_after"] == 1
