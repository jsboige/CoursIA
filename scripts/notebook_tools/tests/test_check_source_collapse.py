"""Tests for check_source_collapse.py — SOURCE collapse, both mechanisms.

VOLUME (#15901). Pins the design that the founding case forces: a cell that
loses 37 % of its source (8425 -> 5309 on GameTheory-06e, cell
``c989_independent_v2``) must fire, so the discriminant is an ABSOLUTE loss
over a floor plus a modest ratio — an "order of magnitude" rule would stay
silent on the incident that motivated the organ. The two mechanically
detectable legitimate causes (content moved to another cell of the SAME
notebook, diagnostic-text purge) exempt the signal. Benign churn, sub-floor
losses, sub-floor bases, growth, deleted cells and added notebooks are silent.

STRUCTURE (#16110). The other end of the same family: the source survives in
volume and loses its shape. The founding case (PR #16097, cell ``40cb37d5`` of
Lean-18) folds the whole cell into one comment and GROWS it (1132 -> 1728
chars), so the volume gate stops before any floor, and a fully commented cell
parses clean, so the syntax guard stays green. The discriminants are EMPTIED
(statements > 0 -> 0) and ORPHAN-OUTPUT (a result asserted with no statement
to produce it, base-free). Criterion 1 of the issue — the unterminated-item
count — is REFUTED by measurement and has its own test.

One test in the volume half is the point of the whole file: a cell whose
SOURCE collapses while its outputs are untouched FIRES here and is invisible
to the output-side sibling — which is exactly why #15862 turned 30 ratchets
green.

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
    _format_delta,
    _has_ipython_magic,
    _moved_fraction,
    _normalize,
    _python_statements,
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


# ---------------------------------------------------------------------------
# SOURCE-STRUCTURE collapse axis (#16110) -- the other end of the same family.
#
# The volume criteria above are blind to it BY CONSTRUCTION: the founding case
# (PR #16097, head 1209b5357, cell 40cb37d5 of Lean-18) folds every newline of
# the cell into one comment AND appends a note, so the head is LONGER than the
# base (1132 -> 1728 chars) and the magnitude gate stops before any floor.
# Syntax is blind too: a fully commented cell parses clean, so the BLOCKING
# notebook-cell-source-parses guard stays green. The discriminant is the
# STATEMENT COUNT.
#
# A fixture here must name a Python kernel: the statement is a Python notion,
# and `metadata: {}` (the volume fixtures above) leaves the structural pass
# deliberately off.
# ---------------------------------------------------------------------------

STREAM = [{"output_type": "stream", "name": "stdout",
           "text": "@Sendov.sendov : axioms [propext, ...]"}]
# The incident's head is LONGER than its base (1132 -> 1728 chars): the same
# write that stripped the newlines also appended a 639-character recovery
# note. The fixture reproduces that shape, because the growth is exactly what
# makes the volume gate structurally blind to the fold.
NOTE = ("# Note de recuperation : la sortie authentique de base a ete "
        "transposee dans un output stream, exec_count retire, verdict "
        "RECOVERABLE-MACHINE pour la re-execution live. ") * 5
FOLDED = "# " + BIG.replace("\n", "") + NOTE    # the incident's exact shape


def pnb(code_cells):
    """Python-kernel notebook: the structural criteria are switched on."""
    return {"cells": [code_cell(*c) for c in code_cells],
            "metadata": {"kernelspec": {"name": "python3",
                                        "language": "python"}},
            "nbformat": 4, "nbformat_minor": 5}


def pbase(code_cells, added=False):
    return None if added else pnb(code_cells)


def signals(row):
    return [s for f in row["cells"] for s in f["signals"]]


def test_structure_founding_case_fires_where_volume_cannot():
    """#16110: the fold GROWS the cell, so MAGNITUDE never fires."""
    row = analyze(pbase([("40cb37d5", BIG)]),
                  pnb([("40cb37d5", FOLDED, STREAM)]))
    assert kinds(row) == ["structure"]
    assert row["regressed"] is True
    f = row["cells"][0]
    assert "magnitude" not in f["signals"]
    assert sorted(f["signals"]) == ["emptied", "orphan-output"]
    assert f["base_body"] > 0 and f["head_body"] == 0
    assert f["loss"] < 0, "the fixture must GROW, as the incident does"


def test_emptied_fires_without_any_output():
    """An emptied cell is a finding on its own: no output required."""
    row = analyze(pbase([("a", BIG)]), pnb([("a", FOLDED)]))
    assert kinds(row) == ["structure"]
    assert row["cells"][0]["signals"] == ["emptied"]


def test_orphan_output_is_base_free():
    """A cell asserting a result it cannot produce fires unchanged."""
    row = analyze(pbase([("a", "# rien qu'un commentaire\n", STREAM)]),
                  pnb([("a", "# rien qu'un commentaire\n", STREAM)]))
    assert kinds(row) == ["structure"]
    assert row["cells"][0]["signals"] == ["orphan-output"]


def test_no_output_no_orphan():
    """Zero statements with no output is not an orphan claim."""
    row = analyze(pbase([("a", "# commentaire seul\n")]),
                  pnb([("a", "# commentaire seul\n")]))
    assert row["cells"] == []


def test_magic_cell_is_not_orphan():
    """`# comment` + `!python ...` DOES have a producer: the magic.

    Measured necessity: without this guard a sweep of `main` flags 6 healthy
    cells, every one of them of exactly this shape.
    """
    magic = "# Telecharger\n!python x.py --symbols SPY"
    row = analyze(pbase([("a", magic)]), pnb([("a", magic, STREAM)]))
    assert "orphan-output" not in signals(row)
    assert "emptied" not in signals(row)


def test_unchanged_magic_cell_is_silent():
    magic = "# Installer\n%pip install -q rdflib"
    assert analyze(pbase([("a", magic)]),
                   pnb([("a", magic, STREAM)]))["cells"] == []


def test_per_character_serialization_is_not_a_collapse():
    """Criterion 1 of #16110 refuted: the unterminated count is a
    serialization GRANULARITY, not a defect.

    `GenAI/Texte/21_LoRA_FineTuning.ipynb` cell `69b296cb` on `main` is
    serialized character by character -- 802 unterminated items, 10
    statements, a real output. Nothing about it is broken.
    """
    perchar = list(BIG)
    unterminated = sum(1 for x in perchar[:-1] if not x.endswith("\n"))
    assert unterminated >= 800, "the witness must be as pathological as main's"
    row = analyze(pbase([("a", perchar)]), pnb([("a", perchar)]))
    assert row["cells"] == []


def test_moved_exemption_does_not_silence_orphan_output():
    """The exemptions speak about the base->head RELATION, so they arbitrate
    EMPTIED -- but an asserted result no statement can produce stays true."""
    row = analyze(
        pbase([("a", MOVED_BLOCK), ("b", "court = 1")]),
        pnb([("a", "# " + MOVED_BLOCK.replace("\n", ""), STREAM),
             ("b", MOVED_BLOCK)]))
    assert kinds(row) == ["structure"]
    f = row["cells"][0]
    assert f["signals"] == ["orphan-output"], "emptied must be exempted here"
    assert f["moved_fraction"] >= MOVED_FRACTION
    assert row["regressed"] is True


def test_added_notebook_is_judged_by_neither_pass():
    """The boundary is the notebook: a wholly new one is read as new content."""
    row = analyze(pbase([], added=True),
                  pnb([("a", "# commentaire\n", STREAM)]))
    assert row["cells"] == [] and row["regressed"] is False


def test_non_python_kernel_skips_the_structural_pass():
    """A .NET cell has no Python statement count to compare."""
    row = analyze(base([("a", BIG)]), nb([("a", "# commentaire\n", STREAM)]))
    assert "orphan-output" not in signals(row)
    assert "emptied" not in signals(row)


def test_python_statements_none_means_not_measurable():
    """None is 'no verdict', never 'zero' -- the distinction is the predicate."""
    assert _python_statements("") is None
    assert _python_statements("   \n\n") is None
    assert _python_statements("%matplotlib inline") is None
    assert _python_statements("!pip install x") is None
    assert _python_statements("def f(:\n") is None          # unparseable
    assert _python_statements("# rien\n") == 0              # the incident
    assert _python_statements("x = 1\n") == 1
    assert _python_statements("%time\nx = 1\n") == 1        # magic stripped


def test_has_ipython_magic_follows_the_logical_line_rule():
    """Same rule as the stripper (PR #13328): `%` in continuation position is
    the formatting operator, not a magic."""
    assert _has_ipython_magic("!pip install x") is True
    assert _has_ipython_magic("x = 1\n%time y = 2\n") is True
    assert _has_ipython_magic('print("a"\n      % (b, c))\n') is False
    assert _has_ipython_magic("# %pas une magic (commentaire)\n") is False
    assert _has_ipython_magic("x = 1\n") is False


def test_format_delta_is_signed():
    """A growth must print as growth: the founding case gains 596 chars."""
    assert _format_delta({"loss": -596, "ratio": -0.526}) == "-596 chars, -52%"
    assert _format_delta({"loss": 3116, "ratio": 0.37}) == "+3116 chars, 37%"
    assert _format_delta({"loss": None, "ratio": None}) == "no baseline"
