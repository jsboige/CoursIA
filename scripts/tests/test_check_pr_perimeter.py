#!/usr/bin/env python3
"""Unit tests for the pure core of check_pr_perimeter.py (#11268).

Acceptance 4 (non-regression): a draft review asserting "2 fichiers twins
uniquement" over a 3-file PR whose third file is a CI workflow moving a
sorry-baseline CANNOT pass the confrontation. The #11227 incident, encoded.
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from check_pr_perimeter import (  # noqa: E402
    BaselineMove,
    check_assertion,
    extract_baseline_moves,
    format_report,
    _fence_mask,
)

# The exact shape of the founding incident (#11227).
FILES_11227 = [
    {"path": ".github/workflows/lean-knot.yml", "additions": 18, "deletions": 10},
    {"path": "MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/Knots/Invariant.lean", "additions": 43, "deletions": 67},
    {"path": "MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/Knots/Invariant_en.lean", "additions": 42, "deletions": 66},
]

DIFF_11227 = """\
diff --git a/MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/Knots/Invariant.lean b/MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/Knots/Invariant.lean
--- a/...Invariant.lean
+++ b/...Invariant.lean
@@ -1,3 +1,3 @@
-old line
+new line
diff --git a/.github/workflows/lean-knot.yml b/.github/workflows/lean-knot.yml
--- a/.github/workflows/lean-knot.yml
+++ b/.github/workflows/lean-knot.yml
@@ -10,7 +10,7 @@
 jobs:
   ci:
-    sorry-baseline: "16"
+    sorry-baseline: "14"
     runs-on: ubuntu-latest
"""


def test_founding_incident_assertion_fails():
    """Acceptance 4: '2 fichiers twins uniquement' over the 3-file PR #11227."""
    problems = check_assertion(FILES_11227, "Périmètre : 2 fichiers twins uniquement, aucune autre modification.")
    assert problems, "the #11227 review sentence MUST be rejected"
    assert any("3" in p for p in problems)
    assert any("lean-knot.yml" in p for p in problems)


def test_count_only_mismatch_is_caught_without_exclusivity():
    problems = check_assertion(FILES_11227, "Périmètre : 2 fichiers.")
    assert any("2" in p and "3" in p for p in problems)


def test_correct_assertion_with_workflow_named_passes():
    assertion = "Périmètre : 3 fichiers uniquement : Invariant.lean, Invariant_en.lean, lean-knot.yml"
    assert check_assertion(FILES_11227, assertion) == []


def test_workflow_named_but_count_wrong_still_fails():
    assertion = "2 fichiers uniquement : Invariant.lean, lean-knot.yml"
    assert check_assertion(FILES_11227, assertion) != []


def test_unverifiable_wording_is_flagged():
    problems = check_assertion(FILES_11227, "Le scope semble correct.")
    assert any("non verifiable" in p for p in problems)


def test_sorry_baseline_down_is_tighten_up_is_loosen():
    moves = extract_baseline_moves(DIFF_11227)
    m = [x for x in moves if x.key == "sorry-baseline"]
    assert len(m) == 1
    assert (m[0].old, m[0].new) == (16, 14)
    assert m[0].direction == "TIGHTEN"


def test_sorry_baseline_loosening_detected():
    diff = DIFF_11227.replace('-    sorry-baseline: "16"', '-    sorry-baseline: "14"').replace(
        '+    sorry-baseline: "14"', '+    sorry-baseline: "18"'
    )
    moves = extract_baseline_moves(diff)
    m = [x for x in moves if x.key == "sorry-baseline"][0]
    assert m.direction == "LOOSEN"


def test_baseline_removal_is_loosen():
    diff = DIFF_11227.replace('+    sorry-baseline: "14"', "+    runs-on: ubuntu-latest")
    moves = extract_baseline_moves(diff)
    m = [x for x in moves if x.key == "sorry-baseline"][0]
    assert m.direction == "LOOSEN" and m.new is None


def test_baseline_addition_is_tighten():
    diff = DIFF_11227.replace('-    sorry-baseline: "16"', "-    runs-on: ubuntu-latest")
    moves = extract_baseline_moves(diff)
    m = [x for x in moves if x.key == "sorry-baseline"][0]
    assert m.direction == "TIGHTEN" and m.old is None


def test_density_threshold_up_is_tighten():
    diff = (
        "diff --git a/scripts/notebook_tools/pedagogy_density.py b/scripts/notebook_tools/pedagogy_density.py\n"
        "--- a/scripts/notebook_tools/pedagogy_density.py\n"
        "+++ b/scripts/notebook_tools/pedagogy_density.py\n"
        "@@ -77 +77 @@\n"
        "-DENSITY_THRESHOLD = 1200\n"
        "+DENSITY_THRESHOLD = 1350\n"
    )
    moves = extract_baseline_moves(diff)
    m = [x for x in moves if x.key == "DENSITY_THRESHOLD"][0]
    assert m.direction == "TIGHTEN"


def test_unknown_knob_reported_for_qualification():
    diff = (
        "diff --git a/.github/workflows/foo.yml b/.github/workflows/foo.yml\n"
        "--- a/.github/workflows/foo.yml\n"
        "+++ b/.github/workflows/foo.yml\n"
        "@@ -5 +5 @@\n"
        "-      parallel_cap: 4\n"
        "+      parallel_cap: 9\n"
    )
    moves = extract_baseline_moves(diff)
    assert any(x.direction == "DIRECTION-A-QUALIFIER" for x in moves)


def test_report_renders_workflow_section_always():
    report_lines = format_report(
        __import__("check_pr_perimeter").Report(
            files=FILES_11227, moves=[BaselineMove(".github/workflows/lean-knot.yml", "sorry-baseline", 16, 14, "TIGHTEN")]
        ),
        None,
    ).splitlines()
    assert any("WORKFLOWS CI TOUCH" in l for l in report_lines)
    assert any("lean-knot.yml" in l for l in report_lines)
    assert any("[TIGHTEN]" in l for l in report_lines)


def test_report_renders_no_workflow_explicitly():
    lines = format_report(
        __import__("check_pr_perimeter").Report(files=[{"path": "README.md", "additions": 1, "deletions": 1}]),
        None,
    ).splitlines()
    assert any("aucun" in l.lower() for l in lines if "Workflows" in l)


# --- Issue #11670 : fence blocks (transcribed L898 ★★★ proof) must be exempted ---

# Founder case from PR #11664 body verbatim: the worker's L898 ★★★
# documentation in a ``` fence contains "0 fichiers en commun", which
# COUNT_CLAIM would otherwise mis-trigger on. The reviewer passes the
# body verbatim via --assert and the guard mis-reads the fence as
# "this PR touches 0 files". The fix: mask fences before scanning.
# The body carries a perimeter claim in PROSE ("Perimetre : 1 fichier")
# alongside the L898 fence — a realistic reviewer pass.
L898_BODY_11664 = (
    "## L898 verifie\n"
    "\n"
    "Perimetre : 1 fichier modifie.\n"
    "\n"
    "```\n"
    "$ git worktree list\n"
    "D:/Dev/CoursIA-2-11663\n"
    "$ gh pr list --search head:feature/11663-xtts-melody-test\n"
    "0 collisions\n"
    "$ gh pr list --state open --json files\n"
    "0 fichiers en commun avec les autres PR\n"
    "```\n"
)
FILES_11664 = [{"path": "MyIA.AI.Notebooks/Audio/XTTS/foo.ipynb", "additions": 5, "deletions": 2}]


def test_fence_with_count_claim_does_not_trigger():
    """Acceptance 1 + 2 : fence with L898 '0 fichiers en commun' over a 1-file
    PR must NOT trip COUNT_CLAIM (the count is in a transcription fence,
    not the author's perimeter claim). The body carries a prose perimeter
    claim (1 fichier modifie) that matches the file list exactly."""
    assert check_assertion(FILES_11664, L898_BODY_11664) == []


def test_fence_mask_replaces_internal_chars():
    """The mask blanks out characters inside a fence but preserves length and
    newlines so downstream regexes don't crash on boundary artifacts."""
    src = "before\n```\ninside fence\n```\nafter"
    masked = _fence_mask(src)
    assert len(masked) == len(src)
    assert "\n" in masked
    assert "before" in masked
    assert "after" in masked
    assert "inside fence" not in masked


def test_prose_claim_still_triggers_with_fence_present():
    """Acceptance 3 (non-regression) : a real perimeter assertion in PROSE
    outside any fence still trips the guard, even when a fence with a
    count claim exists elsewhere in the body. The #11227 incident,
    replicated with a fence added to ensure the fix doesn't open a hole."""
    body = (
        "## Sortie console\n"
        "\n"
        "```\n"
        "$ gh pr list --search foo\n"
        "0 fichiers en commun\n"
        "```\n"
        "\n"
        "Perimetre : 2 fichiers twins uniquement, aucune autre modification.\n"
    )
    files = [
        {"path": "a.lean", "additions": 1, "deletions": 0},
        {"path": "b.lean", "additions": 1, "deletions": 0},
        {"path": ".github/workflows/lean-knot.yml", "additions": 1, "deletions": 1},
    ]
    probs = check_assertion(files, body)
    # exclusivity + workflow not named -> at least one problem remains
    assert any("exclusivite" in p for p in probs), (
        f"expected exclusivity problem to survive fence exemption, got: {probs!r}"
    )


def test_tilde_fence_is_also_exempted():
    """Acceptance 2 variant : ~~~ fences (alternative markdown delimiter) are
    exempt too — same exemption, same pattern as ``` fences."""
    body = (
        "Perimetre : 1 fichier modifie.\n"
        "\n"
        "L898 output :\n"
        "\n"
        "~~~\n"
        "$ gh pr list\n"
        "0 fichiers en commun\n"
        "~~~\n"
    )
    assert check_assertion(FILES_11664, body) == []
