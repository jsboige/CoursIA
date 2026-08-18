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
    extract_perimeter_assertions,
    format_report,
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


# ---------------------------------------------------------------------------
# --scan-thread extraction (the wiring into the review path, acceptance 4)
# ---------------------------------------------------------------------------


def test_extract_finds_founding_assertion():
    """The exact #11227 review sentence, as one line, is a candidate."""
    body = "**Périmètre** : 2 fichiers twins uniquement, aucune autre modification."
    assert extract_perimeter_assertions(body) == [body]


def test_extract_finds_template_file_count_line():
    """The review-template line '**Fichiers:** N fichiers modifiés'."""
    line = "- **Fichiers:** 3 fichiers modifiés"
    assert extract_perimeter_assertions(line) == [line]


def test_extract_finds_bare_exclusivity_with_strong_scope_word():
    assert extract_perimeter_assertions("Aucune autre modification.") == ["Aucune autre modification."]


def test_extract_skips_technical_prose_with_exclusivity_words():
    """Measured false-positive candidates on #11632 -- must NOT be scanned.

    'seulement' / 'uniquement' / 'aucune' in technical prose about the YAML
    block pattern, with no file count and no strong scope word.
    """
    prose = (
        "Nouvelle regle qui detecte les cellules markdown Quarto dont le `---` "
        "initial ouvre un bloc YAML -- pour qu'une PR qui touche un render-list "
        "declenche le guard, pas seulement les PR touchant un `.ipynb` casse.\n"
        "Pandoc le ferme uniquement a la prochaine `---` de la cellule.\n"
        "aucune `---` ulterieure non-fenced avant EOF cellule.\n"
    )
    assert extract_perimeter_assertions(prose) == []


def test_extract_skips_read_only_compound():
    """"only" inside a technical compound is not an exclusivity marker.

    Measured on #11654: the Hermes verdict line "Sinon LGTM sur le périmètre
    — aucun secret, permissions read-only inchangées." was flagged as an
    exclusivity assertion (criterion #11268-2, unnamed workflow) because a
    plain substring match saw "only" inside "read-only" while "périmètre"
    supplied the strong scope word. A permissions adjective is not a
    perimeter quantifier.
    """
    line = ("Sinon LGTM sur le périmètre — note de sécurité : aucun secret, "
            "permissions read-only inchangées.")
    assert extract_perimeter_assertions(line) == []
    assert not __import__("check_pr_perimeter")._has_exclusivity(
        "permissions read-only inchangées")


def test_only_standalone_still_flags():
    """The control positive side: a standalone "only" with a scope word stays
    a live exclusivity assertion -- the fix must not kill the English arm."""
    assert __import__("check_pr_perimeter")._has_exclusivity(
        "only change is the workflow file")
    line = "Only scope change: the workflow file, nothing else."
    assert extract_perimeter_assertions(line) == [line]


def test_extract_skips_markdown_table_rows():
    """A markdown table row is a report structure, not a live assertion.

    Measured on the tool's own PR #11635 (dogfooded): the evidence table
    quoted the founding incident -- '| **#11227** ... « 2 fichiers twins
    uniquement » ... confrontee aux 3 fichiers effectifs |' -- and the guard
    flagged its own PR body against its own 4-file list. Tables carry
    citations; assertions are prose.
    """
    table_row = (
        "| **#11227** (fondatrice) | l'assertion « 2 fichiers twins uniquement » "
        "confrontee aux 3 fichiers effectifs | bloque |"
    )
    assert extract_perimeter_assertions(table_row) == []


def test_extract_skips_fully_quoted_candidacy():
    """A line whose count claim sits inside « ... » quotes reported speech.

    The Hermes review of #11635 cites the founding sentence inside
    guillemets while describing the anti-FP tests -- quoting an assertion is
    not making one.
    """
    quoted = (
        "le test pinne la sentence fondatrice « 2 fichiers twins uniquement, "
        "aucune autre modification. » et la ligne template a cote."
    )
    assert extract_perimeter_assertions(quoted) == []


def test_extract_keeps_live_assertion_with_inline_backlink():
    """A #N backlink in the line does NOT demote a live assertion.

    The founding #11227 Hermes sentence carries an inline issue ref (#2874)
    in the same line and must stay caught -- a backlink exemption would be a
    trivial evasion (append '#1' to any perimeter sentence).
    """
    live = (
        "4. **Périmètre** : 2 fichiers twins uniquement, aucune autre modification. "
        "La note « seul le transfert maitre R2/R3 (#2874) manque » garde le statut."
    )
    assert extract_perimeter_assertions(live) == [live]


def test_extract_keeps_partially_quoted_line_with_unquoted_count():
    """One unquoted count keeps the line live even when other counts are quoted.

    A line quoting '2 fichiers' but also claiming '3 fichiers' bare is a
    live assertion about the current PR -- the unquoted trigger wins.
    """
    partial = "Reprise de « 2 fichiers twins uniquement » mais ici 3 fichiers au total."
    assert extract_perimeter_assertions(partial) == [partial]


def test_scan_thread_composition_rejects_founding_thread():
    """Acceptance 4 at core level: the #11227 thread (review sentence) FAILS.

    extract -> check_assertion is exactly what --scan-thread does per
    body/review, minus the gh fetch. The false '2 fichiers twins uniquement'
    cannot survive the confrontation.
    """
    cands = extract_perimeter_assertions("**Périmètre** : 2 fichiers twins uniquement, aucune autre modification.")
    problems = [p for cand in cands for p in check_assertion(FILES_11227, cand)]
    assert problems
    assert any("lean-knot.yml" in p for p in problems)


def test_scan_thread_composition_accepts_correct_thread():
    cands = extract_perimeter_assertions(
        "Périmètre : 3 fichiers : Invariant.lean, Invariant_en.lean, "
        ".github/workflows/lean-knot.yml."
    )
    problems = [p for cand in cands for p in check_assertion(FILES_11227, cand)]
    assert problems == []


# ---------------------------------------------------------------------------
# Workflow trigger pin (#11648 — edited re-evaluation)
# ---------------------------------------------------------------------------

import pathlib


def _read_perimeter_workflow() -> str:
    """Locate and read the perimeter-review-guard.yml from repo root.

    Resolves from this test file's location so the test is independent of cwd.
    """
    here = pathlib.Path(__file__).resolve()
    # scripts/tests/test_check_pr_perimeter.py → repo root = parents[2]
    repo_root = here.parents[2]
    wf = repo_root / ".github" / "workflows" / "perimeter-review-guard.yml"
    return wf.read_text(encoding="utf-8")


def test_pull_request_trigger_includes_edited_type():
    """Issue #11648: ``pull_request:`` MUST list ``edited`` so an assertion
    correction on the PR body re-triggers the gate.

    Founding measurement: the gate's own body comment claimed "pull_request
    (opened/synchronize/edited)" but the YAML block did not declare ``types:``,
    so GitHub defaulted to ``[opened, synchronize, reopened]`` -- ``edited``
    was silently dropped. A correction on the PR body therefore never
    re-evaluated the gate, leaving the red bar in place (#11646).
    """
    text = _read_perimeter_workflow()
    # Pull the ``on:`` block body: consecutive lines indented by >= 2 spaces.
    # Single fixed-prefix branch (like the sibling sub-block regexes below) --
    # CodeQL HIGH on the previous alternation ``(?:  [^\n]*\n|\s*\n)+?``:
    # whitespace-only lines matched both branches, giving exponential
    # backtracking on runs of blank lines.
    import re
    block = re.search(
        r"^on:\s*\n(?P<body>(?:  [^\n]*\n)+)",
        text,
        re.MULTILINE,
    )
    assert block, "could not locate `on:` block in perimeter-review-guard.yml"
    body = block.group("body")
    # The pull_request sub-block must explicitly name edited.
    pr_block = re.search(
        r"^  pull_request:\s*\n((?:    [^\n]*\n)+)", body, re.MULTILINE
    )
    assert pr_block, "pull_request sub-block not found"
    pr_body = pr_block.group(1)
    assert "types:" in pr_body, (
        "pull_request: block has no types: clause — GitHub will default to "
        "[opened, synchronize, reopened] and silently drop `edited`. "
        "Pin this so a re-eval on PR-body edit actually fires (#11648)."
    )
    assert "edited" in pr_body, (
        "pull_request: types: declared but `edited` missing — without it, "
        "an assertion correction on the PR body will never re-trigger the gate."
    )


def test_pull_request_review_trigger_includes_edited_type():
    """Sibling invariant — the review trigger already had ``edited`` from the
    start (c.342 acceptance), so this test pins that property against
    accidental regression when editing the workflow.
    """
    text = _read_perimeter_workflow()
    import re
    rv_block = re.search(
        r"^  pull_request_review:\s*\n((?:    [^\n]*\n)+)", text, re.MULTILINE
    )
    assert rv_block, "pull_request_review sub-block not found"
    rv_body = rv_block.group(1)
    assert "types:" in rv_body and "edited" in rv_body, (
        "pull_request_review: must keep `types: [submitted, edited]` so "
        "corrected reviews re-trigger the gate."
    )
