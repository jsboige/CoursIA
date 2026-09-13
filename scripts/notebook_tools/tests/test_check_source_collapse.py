"""Tests for check_source_collapse.py — SOURCE-volume collapse axis (#15901).

Pins the design that the founding case forces: a cell that loses 37 % of its
source (8425 -> 5309 on GameTheory-06e, cell ``c989_independent_v2``) must
fire, so the discriminant is an ABSOLUTE loss over a floor plus a modest
ratio — an "order of magnitude" rule would stay silent on the incident that
motivated the organ. The two mechanically detectable legitimate causes
(content moved to another cell of the SAME notebook, diagnostic-text purge)
exempt the signal. Benign churn, sub-floor losses, sub-floor bases, growth,
deleted cells and added notebooks are silent.

The last test is the point of the whole file: a cell whose SOURCE collapses
while its outputs are untouched FIRES here and is invisible to the
output-side sibling — which is exactly why #15862 turned 30 ratchets green.

The logic under test is the pure ``analyze`` — no git, no kernel.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_source_collapse import (
    BASE_FLOOR,
    DIAGNOSTIC_LINE_FRACTION,
    LOSS_FLOOR,
    LOSS_FRACTION,
    MIN_MOVED_LINE_CHARS,
    MOVED_FRACTION,
    _diagnostic_fraction,
    _moved_fraction,
    _normalize,
    _removed_lines,
    analyze,
)


def code_cell(cid, source, outputs=None):
    return {"cell_type": "code", "id": cid, "source": source,
            "outputs": outputs if outputs is not None else []}


def nb(code_cells):
    return {"cells": [code_cell(*c) for c in code_cells],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def base(code_cells, added=False):
    """None when the notebook is ADDED by the branch (no baseline)."""
    return None if added else nb(code_cells)


BIG = "\n".join("ligne_de_code_%d = %d" % (i, i) for i in range(400))
WARNINGS = "\n".join(
    "# warning CS8632: reference nullable requise %d" % i for i in range(60))
MOVED_BLOCK = "\n".join("bloc_deplace_%d = %d" % (i, i) for i in range(120))


def kinds(row):
    return [f["kind"] for f in row["cells"]]


def test_founding_case_shape_fires():
    """8425 -> 5309 is the measured incident: 3116 chars, 37 % — must fire."""
    base_src = "x" * 8425
    head_src = base_src[:5309]
    row = analyze(base([("c989_independent_v2", base_src)]),
                  nb([("c989_independent_v2", head_src)]))
    assert kinds(row) == ["magnitude"]
    assert row["regressed"] is True
    f = row["cells"][0]
    assert f["base"] == 8425 and f["head"] == 5309


def test_ratio_floor_silences_benign_churn():
    """A loss that clears the absolute floor but not the ratio is churn."""
    row = analyze(base([("a", BIG)]), nb([("a", BIG[:7600])]))
    assert row["cells"] == []
    assert row["regressed"] is False


def test_absolute_floor_silences_small_loss():
    """A big ratio on a small absolute loss is not a collapse."""
    small = "\n".join("x_%d = %d" % (i, i) for i in range(60))
    assert len(small) >= BASE_FLOOR
    row = analyze(base([("a", small)]), nb([("a", small[:300])]))
    assert row["cells"] == []


def test_subfloor_base_silent():
    """Below the base floor the cell is never judged, even at 100 % loss."""
    row = analyze(base([("a", "x" * 400)]), nb([("a", "")]))
    assert row["cells"] == []


def test_growth_silent():
    assert analyze(base([("a", BIG)]), nb([("a", BIG + BIG)]))["cells"] == []


def test_deleted_cell_silent():
    """Deleting a code cell is legitimate; the survivor reports nothing."""
    row = analyze(base([("a", BIG), ("b", BIG)]), nb([("a", BIG)]))
    assert row["cells"] == []


def test_added_notebook_never_regressed():
    row = analyze(base([], added=True), nb([("a", BIG[:3000])]))
    assert row["added"] is True and row["regressed"] is False


def test_index_shift_not_misattributed():
    """A benign insert must not attribute the shift to an existing cell."""
    row = analyze(base([("a", BIG)]), nb([("zz", "court = 1"), ("a", BIG)]))
    assert not any(f["cell"] == "a" for f in row["cells"])


def test_moved_content_exempts_within_notebook():
    """Content moved to ANOTHER CELL of the same notebook is not a loss."""
    head_a = BIG[:2000]
    row = analyze(
        base([("a", MOVED_BLOCK + "\n" + head_a), ("b", "court = 1")]),
        nb([("a", head_a), ("b", MOVED_BLOCK + "\ncourt = 1")]))
    assert kinds(row) == ["exempt-moved"]
    assert row["regressed"] is False


def test_insufficient_move_does_not_exempt():
    """Only a small tail of the removed block reappears elsewhere."""
    head_a = BIG[:2000]
    tail = "\n".join(MOVED_BLOCK.splitlines()[-10:])
    row = analyze(
        base([("a", MOVED_BLOCK + "\n" + head_a), ("b", "court = 1")]),
        nb([("a", head_a), ("b", tail + "\ncourt = 1")]))
    assert kinds(row) == ["magnitude"]
    assert row["regressed"] is True


def test_diagnostic_purge_exempt():
    row = analyze(base([("a", WARNINGS + "\n" + BIG[:1500])]),
                  nb([("a", BIG[:1500])]))
    assert kinds(row) == ["exempt-diagnostic"]
    assert row["regressed"] is False


def test_purge_swallowing_real_code_still_fires():
    """Warnings plus a large real block: the purge does not cover it."""
    row = analyze(base([("a", WARNINGS + "\n" + BIG[:2500])]),
                  nb([("a", BIG[:300])]))
    assert kinds(row) == ["magnitude"]
    assert row["regressed"] is True


def test_source_collapse_is_invisible_to_the_output_side():
    """The reason the organ exists: outputs untouched, source gone.

    Same cell count, same outputs, an ``assert`` and a table removed. The
    output-side ratchets keep the exact same output volume and stay green.
    """
    kept = [{"output_type": "stream", "text": "Trois organes en accord\n"}]
    base_src = "EXPECTED_TABLE_V2 = [(1, 2), (3, 4)]\n" + "x" * 8400
    head_src = "EXPECTED_TABLE_V2 = derive_table()\n" + "x" * 5200
    row = analyze(
        base([("c", base_src, kept), ("d", BIG, kept)]),
        nb([("c", head_src, kept), ("d", BIG, kept)]))
    assert kinds(row) == ["magnitude"]
    assert row["regressed"] is True


def test_normalize_strips_accents_and_lowercases():
    assert _normalize("Référence") == "reference"


def test_diagnostic_fraction_is_char_weighted():
    removed = _removed_lines(
        WARNINGS + "\n" + "z" * 900 + "\n", "z" * 50 + "\n")
    frac = _diagnostic_fraction(removed)
    assert 0.5 < frac < DIAGNOSTIC_LINE_FRACTION


def test_moved_fraction_ignores_short_lines():
    """Punctuation and blank lines reappear everywhere: not evidence."""
    removed = _removed_lines("    \n}\n)\n" + "vraie_ligne_longue = 1\n",
                             "court\n")
    assert _moved_fraction(removed, "    \n}\n)\n") < MOVED_FRACTION


def test_constants_pinned():
    """A silent threshold drift must fail here, not in production."""
    assert (BASE_FLOOR, LOSS_FLOOR, LOSS_FRACTION) == (500, 1000, 0.25)
    assert (MOVED_FRACTION, MIN_MOVED_LINE_CHARS) == (0.8, 4)
    assert DIAGNOSTIC_LINE_FRACTION == 0.8
