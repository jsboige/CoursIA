#!/usr/bin/env python3
"""Unit tests for ``translation_override_required.py`` (#10332).

The script is a pure decision over (labels, comments) -> verdict. Fetchers are
default ``gh``-based and injectable; these tests pass dict-based fixtures so
the test runner never touches the network.

Coverage map (mirrors the acceptance criteria of #10332):
  - test_override_pass_label_and_marker       : pass / override_applied True
  - test_override_fail_label_only             : label present, no marker -> fail
  - test_override_fail_marker_only            : marker present, no label -> fail
  - test_override_fail_neither                : nothing -> fail (cliquet)
  - test_override_fail_empty_motif            : marker present but empty motif
  - test_override_pass_picks_first_marker     : multiple markers -> first wins
  - test_override_motif_extraction            : regex anchoring (not in prose)
  - test_override_label_case_sensitive        : case-sensitive label match
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ci.translation_override_required import (  # noqa: E402
    OVERRIDE_LABEL,
    _extract_marker,
    check,
)


def test_override_pass_label_and_marker():
    """Dual-key satisfied: pass with the motif journalised in the verdict."""
    verdict = check(
        pr_number=999,
        comment_bodies=["[TRANSLATION-OVERRIDE] hand-edit finetuning.csv ligne 42-44\n"],
        label_names=[OVERRIDE_LABEL, "other-label"],
    )
    assert verdict["guard_pass"] is True, verdict
    assert verdict["override_applied"] is True
    assert verdict["label_present"] is True
    assert verdict["marker_present"] is True
    assert verdict["motif"] == "hand-edit finetuning.csv ligne 42-44"


def test_override_fail_label_only():
    """Label without marker: the dual-key is unsatisfied -> fail."""
    verdict = check(
        pr_number=999,
        comment_bodies=["This is just a comment without the marker."],
        label_names=[OVERRIDE_LABEL],
    )
    assert verdict["guard_pass"] is False
    assert verdict["override_applied"] is False
    assert verdict["label_present"] is True
    assert verdict["marker_present"] is False
    assert verdict["motif"] is None
    assert "label" in verdict["reason"].lower()
    assert "marker" in verdict["reason"].lower()


def test_override_fail_marker_only():
    """Marker without label: dual-key unsatisfied -> fail."""
    verdict = check(
        pr_number=999,
        comment_bodies=["[TRANSLATION-OVERRIDE] legitimate override #10299"],
        label_names=["unrelated-label"],
    )
    assert verdict["guard_pass"] is False
    assert verdict["override_applied"] is False
    assert verdict["label_present"] is False
    assert verdict["marker_present"] is True
    assert verdict["motif"] == "legitimate override #10299"
    assert "label" in verdict["reason"].lower()


def test_override_fail_neither():
    """No label, no marker: cliquet non disarmé -> fail (criterion 4 of #10332)."""
    verdict = check(
        pr_number=999,
        comment_bodies=["Some unrelated comment", "Another one"],
        label_names=["random-label"],
    )
    assert verdict["guard_pass"] is False
    assert verdict["override_applied"] is False
    assert verdict["label_present"] is False
    assert verdict["marker_present"] is False
    assert verdict["motif"] is None


def test_override_fail_empty_motif():
    """A marker line whose motif is whitespace-only: fail (no journalable decision)."""
    verdict = check(
        pr_number=999,
        comment_bodies=["[TRANSLATION-OVERRIDE]    \n"],
        label_names=[OVERRIDE_LABEL],
    )
    # The regex requires \S after the marker -- a whitespace-only motif does
    # not match. marker_present should be False; dual-key unsatisfied -> fail.
    assert verdict["guard_pass"] is False
    assert verdict["override_applied"] is False
    assert verdict["marker_present"] is False


def test_override_pass_picks_first_marker():
    """Two marker comments: the FIRST one is the override decision."""
    verdict = check(
        pr_number=999,
        comment_bodies=[
            "[TRANSLATION-OVERRIDE] first decision (motif A)",
            "[TRANSLATION-OVERRIDE] second decision (motif B)",
        ],
        label_names=[OVERRIDE_LABEL],
    )
    assert verdict["guard_pass"] is True
    assert verdict["motif"] == "first decision (motif A)"


def test_override_motif_extraction():
    """The marker must appear on its own LINE -- mid-prose markers do not count."""
    # The regex anchors with ^ + MULTILINE. A marker buried in prose does not
    # match because the line starts with prose text.
    body = (
        "Long paragraph that mentions [TRANSLATION-OVERRIDE] in passing "
        "but the marker is not on its own line.\n"
    )
    assert _extract_marker(body) is None

    # But a marker on its own line, with leading whitespace tolerated, matches.
    body2 = "   [TRANSLATION-OVERRIDE]   motif with leading and trailing\n"
    assert _extract_marker(body2) == "motif with leading and trailing"


def test_override_label_case_sensitive():
    """Label match is case-sensitive -- 'Translation-Override' != 'translation-override'."""
    verdict = check(
        pr_number=999,
        comment_bodies=["[TRANSLATION-OVERRIDE] motif"],
        label_names=["Translation-Override"],  # capitalised, NOT the canonical form
    )
    assert verdict["guard_pass"] is False
    assert verdict["label_present"] is False
    assert verdict["marker_present"] is True
