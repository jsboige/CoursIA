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
    Candidate,
    check_assertion,
    extract_baseline_moves,
    extract_perimeter_assertions,
    format_report,
    select_candidates,
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
# Workflow trigger pin (#11648)
#
# Authored by po-2023 in PR #11657, closed as redundant once #11654 landed the
# same `types:` fix. The YAML line was duplicated; these two tests were NOT --
# #11654 shipped no test. Carried here so the fix keeps a pin.
# ---------------------------------------------------------------------------

import pathlib  # noqa: E402
import re  # noqa: E402


def _read_perimeter_workflow() -> str:
    """Locate and read perimeter-review-guard.yml, independent of cwd."""
    here = pathlib.Path(__file__).resolve()
    # scripts/tests/test_check_pr_perimeter.py -> repo root = parents[2]
    return (here.parents[2] / ".github" / "workflows"
            / "perimeter-review-guard.yml").read_text(encoding="utf-8")


def test_pull_request_trigger_includes_edited_type():
    """``pull_request:`` MUST list ``edited`` so a body correction re-fires.

    Founding measurement (po-2023, #11648): the gate's own comment claimed
    "pull_request (opened/synchronize/edited)" while the YAML declared no
    ``types:`` at all, so GitHub defaulted to [opened, synchronize, reopened]
    and silently dropped ``edited``. This pin matters MORE after #11648:
    editing the PR body is now the documented lever for a blocking assertion,
    and that lever exists only while ``edited`` is declared here.
    """
    text = _read_perimeter_workflow()
    pr_block = re.search(
        r"^  pull_request:\s*\n((?:    [^\n]*\n)+)", text, re.MULTILINE
    )
    assert pr_block, "pull_request sub-block not found"
    pr_body = pr_block.group(1)
    assert "types:" in pr_body, (
        "pull_request: has no types: clause -- GitHub defaults to "
        "[opened, synchronize, reopened] and drops `edited` (#11648)."
    )
    assert "edited" in pr_body, (
        "pull_request: types: declared but `edited` missing -- the documented "
        "lever for a blocking body assertion would not exist."
    )


def test_pull_request_review_trigger_includes_edited_type():
    """Sibling invariant: a corrected review must re-fire the check."""
    text = _read_perimeter_workflow()
    rv_block = re.search(
        r"^  pull_request_review:\s*\n((?:    [^\n]*\n)+)", text, re.MULTILINE
    )
    assert rv_block, "pull_request_review sub-block not found"
    rv_body = rv_block.group(1)
    assert "types:" in rv_body and "edited" in rv_body, (
        "pull_request_review: must keep `types: [submitted, edited]`."
    )


# ---------------------------------------------------------------------------
# Consequence model (#11648): supersession per author + blocking scope
# ---------------------------------------------------------------------------

def _thread(*rows):
    """Build a fetch_review_thread()-shaped list. rows: (author, ts, body)."""
    return [{"kind": "review (COMMENTED)", "author": a, "body": b,
             "source": "thread", "ts": t} for a, t, b in rows]


def _body(author, text):
    return {"kind": "PR body", "author": author, "body": text,
            "source": "body", "ts": ""}


ASSERT_5 = "Perimetre : 5 fichiers."
ASSERT_7 = "Perimetre : 7 fichiers."


def test_author_later_assertion_supersedes_their_own_earlier_one():
    """#11648-b1, the founding measurement on #11646.

    ai-01 asserted "5 fichiers" at 14:29 then corrected to "7" (the truth) at
    14:48; the stale one still held the PR red. Self-correction must clear
    one's own red.
    """
    cands = select_candidates(_thread(
        ("ai-01", "2026-08-18T14:29:00Z", ASSERT_5),
        ("ai-01", "2026-08-18T14:48:00Z", ASSERT_7),
    ))
    texts = [c.text for c in cands]
    assert ASSERT_7 in texts
    assert ASSERT_5 not in texts, "superseded assertion still confronted"


def test_supersession_is_per_author_not_global():
    """A later review by SOMEONE ELSE must not retract my assertion."""
    cands = select_candidates(_thread(
        ("hermes", "2026-08-18T14:29:00Z", ASSERT_5),
        ("ai-01", "2026-08-18T14:48:00Z", ASSERT_7),
    ))
    by = {c.author: c.text for c in cands}
    assert by == {"hermes": ASSERT_5, "ai-01": ASSERT_7}


def test_later_silent_review_is_not_a_retraction():
    """Silence is not correction: a later review with no perimeter statement
    leaves the author's previous assertion standing."""
    cands = select_candidates(_thread(
        ("hermes", "2026-08-18T14:29:00Z", ASSERT_5),
        ("hermes", "2026-08-18T15:10:00Z", "LGTM, joli travail."),
    ))
    assert [c.text for c in cands] == [ASSERT_5]


def test_equal_timestamps_fall_back_to_thread_order():
    """GitHub can stamp two reviews identically; the later-listed one wins."""
    cands = select_candidates(_thread(
        ("hermes", "2026-08-18T14:29:00Z", ASSERT_5),
        ("hermes", "2026-08-18T14:29:00Z", ASSERT_7),
    ))
    assert [c.text for c in cands] == [ASSERT_7]


def test_pr_body_assertion_is_blocking():
    """POSITIVE CONTROL (#11648 acceptance).

    This test FAILS if the blocking branch is ever removed -- i.e. if someone
    "fixes" a false positive by making everything advisory. A gate whose every
    input is non-blocking is indistinguishable from a disabled gate.
    """
    cands = select_candidates([_body("jsboige", ASSERT_5)])
    assert len(cands) == 1
    assert cands[0].blocking is True, (
        "PR-body assertions must BLOCK: the author owns the body and an edit "
        "re-triggers the workflow, so the green is reachable (#11648-b2)."
    )


def test_third_party_review_assertion_is_signal_only():
    """#11648-b2: not editable by the author, and COMMENTED reviews cannot be
    dismissed -- blocking there leaves no lever (measured on #11642/#11646)."""
    cands = select_candidates(_thread(
        ("clusterManager-Myia", "2026-08-18T14:29:00Z", ASSERT_5),
    ))
    assert len(cands) == 1
    assert cands[0].blocking is False


def test_detection_is_unchanged_for_non_blocking_assertions():
    """The detector is NOT disarmed: a false third-party assertion is still
    extracted and still confronted -- only its exit code changes."""
    cands = select_candidates(_thread(
        ("clusterManager-Myia", "2026-08-18T14:29:00Z",
         "Perimetre : 2 fichiers twins uniquement, aucune autre modification."),
    ))
    assert len(cands) == 1
    problems = check_assertion(FILES_11227, cands[0].text)
    assert problems, "third-party false assertion must still be detected"
    assert cands[0].blocking is False, "...but must not block"


def test_founding_incident_still_blocks_from_the_pr_body():
    """#11227 encoded end to end: the same false assertion, posted where its
    author can fix it, still fails the gate."""
    cands = select_candidates([_body(
        "author",
        "Perimetre : 2 fichiers twins uniquement, aucune autre modification.")])
    blocking = [c for c in cands if c.blocking]
    assert blocking
    assert check_assertion(FILES_11227, blocking[0].text)
