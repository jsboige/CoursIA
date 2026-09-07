"""Tests for check_output_flood.py — output-object explosion axis (2026-09-06).

Pins the two-axis ratchet: a code cell whose output-object count GREW beyond
CELL_CAP, or one ADDED by the branch already above CELL_CAP, is the finding;
plus a notebook whose TOTAL output-object count GREW beyond TOTAL_CAP. Each
half alone, a benign sub-cap growth, a flood REDUCTION (improvement), a benign
new cell, and a notebook ADDED by the branch (advisory, not gated) are all
silent. The logic under test is the pure ``analyze`` — no git, no kernel.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_output_flood import (CELL_CAP, TOTAL_CAP, analyze, _cell_counts,
                                _cell_key)


def code_cell(cid, outputs):
    return {"cell_type": "code", "id": cid, "outputs": [{}] * outputs}


def nb(code_cells):
    return {"cells": [code_cell(k, n) for k, n in code_cells],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def base(code_cells, added=False):
    """None when the notebook is ADDED by the branch (no baseline)."""
    return None if added else nb(code_cells)


def test_existing_cell_flood_fires():
    got = analyze(base([("a", 3)]), nb([("a", 3018)]))
    assert got["regressed"]
    assert got["cells"] == [{"cell": "a", "kind": "grew",
                             "base": 3, "head": 3018}]


def test_added_cell_above_cap_fires():
    got = analyze(base([("a", 3)]), nb([("a", 3), ("b", 80)]))
    assert got["regressed"]
    assert got["cells"] == [{"cell": "b", "kind": "added", "head": 80}]


def test_benign_subcap_growth_silent():
    got = analyze(base([("a", 5)]), nb([("a", 12)]))
    assert got["cells"] == []
    assert not got["regressed"]


def test_flood_reduction_silent():
    # Restoration direction (3018 -> 500) is never a finding.
    got = analyze(base([("a", 3018)]), nb([("a", 500)]))
    assert got["cells"] == []
    assert not got["regressed"]


def test_benign_new_cell_silent():
    got = analyze(base([("a", 3)]), nb([("a", 3), ("b", 40)]))
    assert got["cells"] == []
    assert not got["regressed"]


def test_index_shift_not_misattributed():
    # Insert a new cell (id zz) BEFORE a legacy flooded-but-unchanged cell
    # (id a at 3000): id-alignment must NOT flag the unchanged cell a.
    got = analyze(base([("a", 3000)]), nb([("zz", 10), ("a", 3000)]))
    assert got["cells"] == []
    # TOTAL keeps the pure-ratchet semantics: the notebook went 3000 -> 3010,
    # both abovs TOTAL_CAP, so the total axis fires (same as the sibling's
    # 0 -> N = regression). This is NOT an index-shift artifact.
    assert got["regressed"] is True
    assert got["total"] == {"base": 3000, "head": 3010, "delta": 10}


def test_diffuse_flood_catches_total():
    # 40 cells each growing 5 -> 30 stays under CELL_CAP but blows TOTAL.
    got = analyze(base([(f"c{i}", 5) for i in range(40)]),
                  nb([(f"c{i}", 30) for i in range(40)]))
    assert got["cells"] == []
    assert got["total"] == {"base": 200, "head": 1200, "delta": 1000}
    assert got["regressed"]


def test_added_notebook_advisory_not_gated():
    # A fresh notebook with an 800-object cell is ADVISORY: reported, not gated.
    got = analyze(None, nb([("a", 800)]))
    assert got["added"]
    assert got["cells"], "le signal doit rester visible en advisory"
    assert not got["regressed"], "mais ne doit jamais faire échouer la gate"


def test_unchanged_flooded_total_silent():
    # A legacy notebook already above TOTAL_CAP (5583) that does NOT grow is a
    # pre-existing debt, never a regression.
    got = analyze(base([("a", 3018), ("b", 2243), ("c", 322)]),
                  nb([("a", 3018), ("b", 2243), ("c", 322)]))
    assert got["total"] is None
    assert not got["regressed"]


def test_cell_counts_uses_id_then_positional():
    # id-aligned key when present, else positional (@index) — both shapes must
    # be counted and never collide with a real nbformat id.
    cells = [{"cell_type": "code", "id": "x", "outputs": [{}] * 2},
             {"cell_type": "code", "outputs": [{}]},
             {"cell_type": "markdown", "outputs": [{}] * 9}]
    counts = _cell_counts({"cells": cells})
    assert counts == {"x": 2, "@1": 1}
    assert _cell_key(cells[0], 0) == "x"
    assert _cell_key(cells[1], 1) == "@1"
