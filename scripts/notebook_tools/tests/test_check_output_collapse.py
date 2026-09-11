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
