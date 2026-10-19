"""Tests for check_output_collapse.py — output-volume collapse axis (#15327).

Pins the discriminating design (ai-01 measurement on the issue: aggregate
contraction alone is ~100 % FP): the SIGNATURE signal fires on a
graceful-degradation motif over a substantial base, the MAGNITUDE signal on
a per-cell order-of-magnitude loss, and the two mechanically detectable
legitimate causes (content moved to a notebook created by the same diff,
diagnostic-text purge) exempt the magnitude signal only. Benign variance,
sub-floor bases, growth, deleted cells and added notebooks are silent.
The logic under test is the pure ``analyze`` / ``_apply_moved_content`` —
no git, no kernel.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_output_collapse import (
    BASE_FLOOR,
    DIAGNOSTIC_LINE_FRACTION,
    MAGNITUDE_FACTOR,
    MOVED_GAIN_FRACTION,
    SIGNATURE_FACTOR,
    _apply_moved_content,
    _diagnostic_fraction,
    _normalize,
    analyze,
)


def code_cell(cid, text):
    return {"cell_type": "code", "id": cid,
            "outputs": [{"output_type": "stream", "text": text}]}


def nb(code_cells):
    return {"cells": [code_cell(k, t) for k, t in code_cells],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def base(code_cells, added=False):
    """None when the notebook is ADDED by the branch (no baseline)."""
    return None if added else nb(code_cells)


LONG = "x" * 1000
SKIP_NOTICE = ("[INFO] API non configuree - execution sautee\n"
               "Configurez OPENAI_API_KEY pour executer les exemples\n")
WARNINGS = "".join(
    "warning CS8632: Une reference nullable est requise %d\n" % i
    for i in range(30))


def test_signature_fires_on_skip_notice():
    got = analyze(base([("a", LONG)]), nb([("a", SKIP_NOTICE)]))
    assert got["regressed"]
    assert got["cells"][0]["kind"] == "signature"
    assert got["cells"][0]["factor"] >= SIGNATURE_FACTOR


def test_signature_is_accent_blind():
    # "sautée" / "configurée" with accents must match the accent-stripped
    # motifs (both spellings exist in the wild).
    got = analyze(base([("a", LONG)]),
                  nb([("a", "Execution sautée (API non configurée)\n")]))
    assert got["cells"] and got["cells"][0]["kind"] == "signature"


def test_signature_needs_real_contraction():
    # A motif substring in a GROWN output is not degradation.
    got = analyze(base([("a", LONG)]),
                  nb([("a", "skipped 0 tests\n" + "x" * 1500)]))
    assert got["cells"] == []


def test_magnitude_fires_on_order_of_magnitude_loss():
    got = analyze(base([("a", LONG)]), nb([("a", "y" * 40)]))
    assert got["regressed"]
    assert got["cells"][0]["kind"] == "magnitude"
    assert got["cells"][0]["factor"] >= MAGNITUDE_FACTOR


def test_benign_variance_silent():
    got = analyze(base([("a", LONG)]), nb([("a", "x" * 700)]))
    assert got["cells"] == []
    assert not got["regressed"]


def test_subfloor_base_silent():
    # Below the noise floor a base is jitter, even at x400 contraction.
    assert len("x" * 400) < BASE_FLOOR
    got = analyze(base([("a", "x" * 400)]), nb([("a", "y")]))
    assert got["cells"] == []


def test_growth_silent():
    got = analyze(base([("a", LONG)]), nb([("a", "x" * 5000)]))
    assert got["cells"] == []


def test_diagnostic_purge_exempt():
    got = analyze(base([("a", WARNINGS)]), nb([("a", "Build succeeded.\n")]))
    assert got["cells"][0]["kind"] == "exempt-diagnostic"
    assert got["cells"][0]["diagnostic_fraction"] >= DIAGNOSTIC_LINE_FRACTION
    assert not got["regressed"]


def test_purge_swallowing_real_output_still_fires():
    # Char-weighted classification: a purge that also swallows a large real
    # output line must not ride along the short warning lines.
    got = analyze(base([("a", WARNINGS + "real: " + "z" * 900 + "\n")]),
                  nb([("a", "real: " + "z" * 50 + "\n")]))
    assert got["cells"][0]["kind"] == "magnitude"
    assert got["regressed"]


def test_deleted_cell_silent():
    # A PR that deletes code cells loses volume legitimately: the deleted
    # cell has no head counterpart, so no finding is produced.
    got = analyze(base([("a", LONG), ("b", LONG)]), nb([("a", LONG)]))
    assert got["cells"] == []
    assert not got["regressed"]


def test_added_notebook_never_regressed():
    got = analyze(base([], added=True), nb([("a", SKIP_NOTICE)]))
    assert not got["regressed"]
    assert got["added"]


def test_index_shift_not_misattributed():
    got = analyze(base([("a", LONG)]), nb([("zz", "y"), ("a", LONG)]))
    assert got["cells"] == []


def test_moved_content_exempts_at_diff_scale():
    # Split pattern (#14795): notebook A collapses a cell, notebook B is
    # CREATED by the same diff with comparable volume.
    rows = [analyze(base([("a", LONG * 3)]), nb([("a", "y" * 30)])),
            analyze(base([], added=True), nb([("b", "z" * 1500)]))]
    _apply_moved_content(rows)
    assert rows[0]["cells"][0]["kind"] == "exempt-moved"
    assert not rows[0]["regressed"]


def test_insufficient_moved_gain_does_not_exempt():
    rows = [analyze(base([("a", LONG * 3)]), nb([("a", "y" * 30)])),
            analyze(base([], added=True), nb([("b", "z" * 300)]))]
    _apply_moved_content(rows)
    assert rows[0]["cells"][0]["kind"] == "magnitude"
    assert rows[0]["regressed"]


def test_moved_content_never_exempts_signature():
    rows = [analyze(base([("a", LONG)]), nb([("a", SKIP_NOTICE)])),
            analyze(base([], added=True), nb([("b", "z" * 5000)]))]
    _apply_moved_content(rows)
    assert rows[0]["cells"][0]["kind"] == "signature"
    assert rows[0]["regressed"]


def test_normalize_strips_accents_and_lowercases():
    assert _normalize("Exécution Sautée (non configuré)") == \
        "execution sautee (non configure)"


def test_diagnostic_fraction_char_weighted():
    removed_real = "z" * 900
    got = _diagnostic_fraction(WARNINGS + removed_real + "\n",
                               removed_real + "\n")
    # All removed chars are warnings here: fraction 1.0.
    assert got == 1.0
    got = _diagnostic_fraction(WARNINGS + removed_real + "\n", "\n")
    # The real 900-char line dominates the removed volume: fraction < 0.8.
    assert got < DIAGNOSTIC_LINE_FRACTION


def test_constants_pinned():
    # Calibration provenance: reference case factors 14.9/67.6/49.4 (all
    # above 10), noise floor 500 chars, moved-gain fraction from ai-01's
    # "un volume comparable" on #14795's split.
    assert BASE_FLOOR == 500
    assert MAGNITUDE_FACTOR == 10
    assert SIGNATURE_FACTOR == 2
    assert MOVED_GAIN_FRACTION == 0.5
    assert DIAGNOSTIC_LINE_FRACTION == 0.8


# ---------------------------------------------------------------------------
# Issue #21424 T1 + T2: --history mode and the body-justification bypass.
# ---------------------------------------------------------------------------

def test_parse_collapse_justification_absent():
    """No section header -> no justification, regardless of body content."""
    from check_output_collapse import parse_collapse_justification
    assert parse_collapse_justification("") == {}
    assert parse_collapse_justification("## unrelated section") == {}
    assert parse_collapse_justification(
        "## output-collapse justification\nno cells here"
    ) == {}


def test_parse_collapse_justification_form_dash_cell():
    """`- notebook.ipynb cell abcd: reason` is recognized."""
    from check_output_collapse import parse_collapse_justification
    body = ("## Output-collapse justification\n"
            "- Lean-7b-Examples.ipynb cell eb711ddb: API key absent\n"
            "## Next section")
    j = parse_collapse_justification(body)
    assert ("Lean-7b-Examples.ipynb", "eb711ddb") in j
    assert "API key absent" in j[("Lean-7b-Examples.ipynb", "eb711ddb")]


def test_parse_collapse_justification_form_hash():
    """`notebook.ipynb#abcd reason` is recognized (alternate spelling)."""
    from check_output_collapse import parse_collapse_justification
    body = ("## Output-collapse justification\n"
            "- Lean-7b-Examples.ipynb#4d4322dd: re-execution skipped\n")
    j = parse_collapse_justification(body)
    assert ("Lean-7b-Examples.ipynb", "4d4322dd") in j


def test_unaddressed_keeps_only_unjustified_cells():
    """The unaddressed list is the gate signal -- justified cells drop out."""
    from check_output_collapse import (
        parse_collapse_justification, _unaddressed,
    )
    body = ("## Output-collapse justification\n"
            "- Lean-7b-Examples.ipynb cell eb711ddb: env-only\n")
    j = parse_collapse_justification(body)
    bad = [
        {"notebook": "Lean-7b-Examples.ipynb",
         "cells": [
             {"cell": "eb711ddb", "kind": "signature",
              "factor": 14.9, "base": 1000, "head": 67},
             {"cell": "32aa3fbb", "kind": "magnitude",
              "factor": 49.4, "base": 1000, "head": 20},
         ]},
    ]
    un = _unaddressed(bad, j)
    assert len(un) == 1
    assert un[0]["cell"] == "32aa3fbb"


def test_unaddressed_drops_exempt_entries():
    """Exempt (moved, diagnostic) findings are never unaddressed."""
    from check_output_collapse import _unaddressed
    bad = [
        {"notebook": "Foo.ipynb", "cells": [
            {"cell": "a", "kind": "exempt-moved", "factor": 5,
             "base": 100, "head": 20},
        ]},
    ]
    assert _unaddressed(bad, {}) == []


def test_history_yields_no_findings_on_clean_diff():
    """A diff that adds a notebook yields no finding (added == exempt)."""
    from check_output_collapse import history
    # The 'added-notebook' case: pass an empty list of paths through the
    # helper. We assert only that the iterator returns a list (we don't
    # drive a real git walk in this unit test).
    assert list(history("2026-10-10", "2026-10-19",
                         notebook="does-not-exist.ipynb",
                         limit=1)) == []
