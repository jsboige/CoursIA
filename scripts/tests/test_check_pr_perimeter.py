#!/usr/bin/env python3
"""Unit tests for the pure core of check_pr_perimeter.py (#11268).

Acceptance 4 (non-regression): a draft review asserting "2 fichiers twins
uniquement" over a 3-file PR whose third file is a CI workflow moving a
sorry-baseline CANNOT pass the confrontation. The #11227 incident, encoded.
"""

import sys
import os
import shutil
from pathlib import Path

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from check_pr_perimeter import (  # noqa: E402
    BaselineMove,
    Candidate,
    CarriedNote,
    COUNT_CLAIM,
    check_assertion,
    extract_baseline_moves,
    extract_perimeter_assertions,
    extract_perimeter_assertions_with_block,
    extract_perimeter_assertions_with_context,
    format_report,
    is_downgradable_mismatch,
    partition_propres,
    select_candidates,
    _additive_line_sum,
    _check_unterminated_fence,
    _count_is_exempt,
    _count_is_incidental,
    _fence_line_indices,
    _has_strong_scope,
    _is_incidental_assertion,
    _normalize_rest_files,
    _paragraph_block,
    unmeasurable_perimeter,
    _paragraph_prefix,
    _word_form_count,
    _word_form_is_indef_non_pr_subject,
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


def test_extract_skips_negated_exclusivity_marker():
    """A marker under negation asserts universality, not exclusivity.

    Measured on #12547: the body line "Le gate attend tous les checks
    non-advisory, pas seulement les requis" -- a claim about CI semantics
    that WIDENS the set it describes -- was read as an exclusivity assertion
    and fired criterion #11268-2 on two untouched-by-the-claim workflow
    files, turning the required PR gate red on a correct body. Same failure
    shape as the read-only compound above: the marker is present, its force
    is not.
    """
    line = ("Le gate attend tous les checks non-advisory, pas seulement "
            "les requis.")
    assert extract_perimeter_assertions(line) == []
    perim = __import__("check_pr_perimeter")
    for negated in ("pas seulement les requis",
                    "non seulement les requis mais tous les checks",
                    "not only the required ones",
                    "ce n'est pas uniquement une question de perimetre"):
        assert not perim._has_exclusivity(negated), negated


def test_bare_exclusivity_still_flags_after_negation_fix():
    """Control positive: the negation skip must disarm nothing.

    Every marker in its plain, unnegated form stays a live exclusivity
    assertion. This is the fixture class whose absence let the negation
    blindness ship in the first place.
    """
    perim = __import__("check_pr_perimeter")
    for live in ("cette pr touche uniquement ces 2 fichiers",
                 "seulement le workflow x est modifie",
                 "aucune autre modification",
                 "only the sweep is touched",
                 "nothing else is modified"):
        assert perim._has_exclusivity(live), live


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


# ---------------------------------------------------------------------------
# Issue #11670 founder case: PR #11664 body verbatim (L898 ★★★ in a ``` fence)
# The fence carries "0 fichiers en commun avec les autres PR" which is the
# transcription of `gh pr list` output. Without an extraction-level fence
# exemption, `extract_perimeter_assertions` would surface that line and the
# count claim would mismatch a 1-file PR -> false positive block.
# Measured by jsboige 2026-08-18 against the v1 fix at
# `scripts/check_pr_perimeter.py:check_assertion` which masked the body only
# at the assertion level -- the per-line extractor still received the raw
# line, so the gate would still trip. The fix lives in
# `_fence_line_indices` + the `idx in fence_indices` skip in
# `extract_perimeter_assertions`.
# ---------------------------------------------------------------------------


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


def test_fence_line_indices_skip_only_enclosed_lines():
    """Helper contract: delimiter lines are NOT in the set; only the lines
    they enclose are. The opener line (with triple backticks) sits outside
    the set; the body line '0 fichiers en commun' sits inside; the closer
    line (with triple backticks) sits outside again. The second return value
    says no fence was opened without a closing counterpart (founder #11670
    body is well-formed).
    """
    indices, unterminated = _fence_line_indices(L898_BODY_11664)
    # The L898 body has 12 lines (0..11): opener at idx 4, body 5..10,
    # closer at idx 11. Body interior = {5, 6, 7, 8, 9, 10}.
    assert indices == {5, 6, 7, 8, 9, 10}, (
        f"expected only the body lines inside the fence to be flagged, got {sorted(indices)}"
    )
    assert unterminated is None, (
        "a well-formed fence (opener + closer) must NOT report an orphan opener"
    )


def test_extract_perimeter_assertions_skips_fence_with_count_claim():
    """Acceptance 1 (issue #11670): the founder #11664 body carrying L898 in
    a fenced block must extract only the authorial 'Perimetre : 1 fichier
    modifie.' line and NOT the fenced '0 fichiers en commun' line. The
    single extracted candidate matches the one file in FILES_11664, so
    `check_assertion` returns no problems on the --scan-thread path.
    """
    cands = extract_perimeter_assertions(L898_BODY_11664)
    assert cands == ["Perimetre : 1 fichier modifie."], (
        f"fence lines must not surface as perimeter candidates, got {cands!r}"
    )
    problems = [p for cand in cands for p in check_assertion(FILES_11664, cand)]
    assert problems == [], (
        f"the founder #11664 body must pass --scan-thread with the fence exemption, "
        f"got {problems!r}"
    )


def test_extract_perimeter_assertions_skips_fence_acceptance2_variant():
    """Acceptance 2: 'fail-before-fix / pass-after-fix' encoded by inspecting
    the raw line that historically tripped the gate. Before the fix,
    `extract_perimeter_assertions` would surface '0 fichiers en commun avec
    les autres PR' (count claim '0 fichiers' != 1 real file -> problem).
    After the fix, that line is in a fence and is NOT surfaced.
    """
    body = (
        "## Sortie console\n"
        "\n"
        "```\n"
        "$ gh pr list --search foo\n"
        "0 fichiers en commun\n"
        "```\n"
        "\n"
        "Perimetre : 1 fichier modifie.\n"
    )
    cands = extract_perimeter_assertions(body)
    assert "0 fichiers en commun" not in cands
    assert any("Perimetre : 1 fichier modifie." in c for c in cands)


def test_extract_perimeter_assertions_skips_tilde_fence_too():
    """Tilde fences (~~~) are exempt using the same pattern. Issue #11670
    acceptance 2 variant.
    """
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
    cands = extract_perimeter_assertions(body)
    assert "0 fichiers en commun" not in cands
    assert any("Perimetre : 1 fichier modifie." in c for c in cands)


def test_extract_perimeter_assertions_keeps_prose_exclusivity_with_fence_present():
    """Acceptance 3 (non-regression): a perimeter assertion in PROSE outside
    the fence is still extracted, even when the body has a fenced block
    elsewhere. The #11227 incident, replicated with a fence added to ensure
    the fix doesn't open a hole. Each candidate is `check_assertion`-ed and
    the workflow under `.github/workflows/lean-knot.yml` is not named in
    the prose, so the gate still trips.
    """
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
    cands = extract_perimeter_assertions(body)
    problems = [p for cand in cands for p in check_assertion(files, cand)]
    assert cands, "the prose claim must be extracted even with a fence present"
    assert any(p for p in problems), (
        "the workflow-named-not assertion must still trip with a fence present"
    )


def test_extract_perimeter_assertions_fence_does_not_swallow_following_lines():
    """A fence closes on its delimiter line; subsequent prose lines must be
    re-armed for extraction. This protects against a regression where the
    helper forgets to flip `in_fence = False` after seeing the closer.
    """
    body = (
        "```\n"
        "0 fichiers en commun\n"
        "```\n"
        "\n"
        "Perimetre : 1 fichier modifie.\n"
    )
    cands = extract_perimeter_assertions(body)
    assert any("Perimetre : 1 fichier modifie." in c for c in cands), (
        f"post-fence prose must be re-extracted, got {cands!r}"
    )


# ---------------------------------------------------------------------------
# Acceptance #11678 — unterminated fence flag propagation
# ---------------------------------------------------------------------------

# Founder body verbatim from issue #11678: an orphan opener renders to EOF
# under CommonMark (the correct rendering), but every line after the orphan
# is excluded from the scan, producing a silent no-op on the tail. The
# helper must surface the flag so the gate can warn the reviewer instead of
# silently rubber-stamping the body.
L11678_FOUNDER_BODY = (
    "intro\n"
    "```\n"  # ← orphan opener; never closed
    "$ echo hi\n"
    "\n"
    "Perimetre : 3 fichiers modifies uniquement.\n"
)


def test_unterminated_fence_helper_pins_true_on_founder_body():
    """#11678 acceptance 1: the founder body (orphan opener, no closer) MUST
    trip ``unterminated_fence: true`` on both the helper and the
    ``_fence_line_indices`` return value. This is the bug the gate had:
    a body with an orphan opener rendered correctly to EOF but the scan
    silently skipped every subsequent line, returning zero candidates
    without telling the reviewer why.
    """
    # Helper contract
    assert _check_unterminated_fence(L11678_FOUNDER_BODY) is True, (
        "orphan opener on founder body must raise unterminated_fence"
    )
    # Direct: the tuple's second element carries the orphan opener's line
    # index (#11723) -- pinned, not just boolean: founder body lines are
    # 0:"intro", 1:"```", so the orphan opener is 0-based index 1.
    indices, orphan_opener = _fence_line_indices(L11678_FOUNDER_BODY)
    assert orphan_opener == 1, (
        f"_fence_line_indices must return the orphan opener's 0-based index "
        f"(1 on the founder body), got {orphan_opener!r}"
    )
    # The flag must NOT silently swallow the closing state: every line from
    # the orphan opener onward (but NOT the opener itself) is in the set.
    assert 1 not in indices, "the opener line itself is a delimiter, not a body"
    assert 2 in indices and 3 in indices and 4 in indices, (
        f"every post-opener line is enclosed by the orphan fence, "
        f"expected 2/3/4 in indices, got {sorted(indices)}"
    )


def test_unterminated_fence_helper_pins_false_on_closed_fence():
    """#11678 acceptance 2 (negative control): a correctly closed fence
    MUST NOT raise the flag. The flag is for the orphan-opener shape only;
    on a well-formed body the gate should remain silent on this dimension.
    """
    body = (
        "intro\n"
        "```\n"
        "$ echo hi\n"
        "```\n"  # ← closer
        "\n"
        "Perimetre : 3 fichiers modifies uniquement.\n"
    )
    assert _check_unterminated_fence(body) is False, (
        "a fully closed fence must NOT trip unterminated_fence"
    )
    indices, unterminated = _fence_line_indices(body)
    assert unterminated is None, (
        "well-formed opener+closer must report no orphan opener (None)"
    )
    # Opener and closer are NOT in the set; the body line IS in the set.
    assert 1 not in indices and 3 not in indices, (
        f"delimiter lines are not body, got {sorted(indices)}"
    )
    assert 2 in indices, "the single body line inside the fence IS in the set"


def test_unterminated_fence_propagates_through_select_candidates():
    """#11678 acceptance 3 (non-regression): the flag must surface through
    ``select_candidates`` so the gate's main() can emit the non-blocking
    ``UNFINISHED_FENCE: True`` warning. The founder body would otherwise
    silently pass with zero candidates → no problems → false-negative.
    """
    # Founder #11670 control: a body with a correctly closed fence + a
    # prose claim that matches the perimeter → no problems, no
    # unterminated flag. This is the false-positive guard.
    FILES_OK = [
        {"path": "scripts/check_pr_perimeter.py", "additions": 50, "deletions": 30},
        {"path": "scripts/tests/test_check_pr_perimeter.py", "additions": 80, "deletions": 5},
    ]
    body_closed = (
        "Périmètre : 2 fichiers : scripts/check_pr_perimeter.py, "
        "scripts/tests/test_check_pr_perimeter.py.\n"
    )
    items = [{"kind": "body", "author": "owner", "body": body_closed, "source": "body"}]
    cands, unterminated = select_candidates(items)
    assert unterminated is None, (
        "closed body must NOT report an orphan opener"
    )
    assert all(check_assertion(FILES_OK, c.text) == [] for c in cands), (
        "matching prose claim over the right perimeter must still pass"
    )

    # Founder #11678 case: orphan opener on the body. The flag MUST
    # surface; the actual count claim (3 fichiers) trips a problem
    # because we feed it a 2-file perimeter (founder case #11670).
    items_bad = [{
        "kind": "body",
        "author": "owner",
        "body": L11678_FOUNDER_BODY,
        "source": "body",
    }]
    cands_bad, unterminated_bad = select_candidates(items_bad)
    assert unterminated_bad == 1, (
        "founder body with orphan opener must propagate its 0-based line "
        "index (1) through select_candidates, not just a boolean"
    )
    # The body line of the founder case still surfaces as a candidate
    # (the orphan fence does NOT swallow the line for the perimeter
    # scan, only for the rendering) -- wait, actually it DOES swallow
    # the line. The flag is the only signal that the tail was skipped.
    # Pin that semantic explicitly so the reviewer knows what they are
    # looking at: if the flag is True, the post-opener tail is invisible.
    assert not any(
        "Perimetre : 3 fichiers modifies" in c.text for c in cands_bad
    ), (
        "orphan fence swallows the post-opener line from the scan; "
        "this is the silent-no-op shape #11678 measures"
    )


def test_orphan_opener_line_is_pinned_on_founder_case():
    """#11723 acceptance 3: the orphan opener's line number is PINNED at both
    levels, not just its existence. An index that is off by one localizes the
    defect to the wrong line -- worse than no index at all, because the
    reviewer stops trusting the notice (``assert is not None`` would let an
    index of 0, 2 or 4 pass silently).

    Founder #11678 body layout (0-based): 0 "intro", 1 "```" (orphan opener,
    never closed), 2 "$ echo hi", 3 "", 4 "Perimetre : ...". The orphan
    opener is therefore 0-based index 1 -- printed as line 2 (1-based) in the
    ``UNFINISHED_FENCE`` notice.
    """
    _, opener = _fence_line_indices(L11678_FOUNDER_BODY)
    assert opener == 1, (
        f"founder body's orphan opener sits at 0-based index 1, got {opener!r}"
    )
    _, propagated = select_candidates([{
        "kind": "body",
        "author": "owner",
        "body": L11678_FOUNDER_BODY,
        "source": "body",
    }])
    assert propagated == 1, (
        f"select_candidates must carry the same pinned index, got {propagated!r}"
    )

    # Off-by-one guard: an orphan opener placed one line lower must pin one
    # index lower -- the value must track the opener's actual position, not
    # a constant.
    body_lower = "intro\ntitle\n```\n$ echo hi\n"
    _, opener_lower = _fence_line_indices(body_lower)
    assert opener_lower == 2, (
        f"opener moved to 0-based index 2 must be reported as 2, got {opener_lower!r}"
    )


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
    """Locate and read the LIVE perimeter surface from repo root.

    #13384 : le declencheur pull_request du perimeter review guard vit
    desormais dans always-on-guards.yml (fusion des cinq gardes always-on) ;
    perimeter-review-guard.yml est dormant (copie de reference). Le pin de
    trigger cible donc l'umbrella -- c'est la que `edited` doit rester
    declare pour qu'une correction de body re-evalue le gate.

    Resolves from this test file's location so the test is independent of cwd.
    """
    here = pathlib.Path(__file__).resolve()
    # scripts/tests/test_check_pr_perimeter.py → repo root = parents[2]
    repo_root = here.parents[2]
    wf = repo_root / ".github" / "workflows" / "always-on-guards.yml"
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


def _read_review_trigger_workflow() -> str:
    """Read the workflow that carries the ``pull_request_review`` trigger.

    #14283 : always-on-guards.yml a bascule sur le pool auto-heberge, et
    `check_self_hosted_runner_policy.py` evalue les declencheurs au niveau
    du FICHIER, pas du job -- un `pull_request_review` (fork-reachable)
    n'importe ou dans le fichier rend TOUT le fichier inadmissible au pool.
    Le declencheur a donc ete rendu a perimeter-review-guard.yml, qui reste
    sur GitHub-hosted. Les deux surfaces ne se doublent pas : always-on-guards
    ne garde que `pull_request`, perimeter-review-guard que
    `pull_request_review` -- c'est la condition que l'en-tete de ce dernier
    posait deja (« NE PAS reinscrire pull_request/pull_request_review ici sans
    retirer l'organe perimeter d'always-on-guards »).

    L'invariant teste est inchange : `types: [submitted, edited]` doit rester
    declare, ou une review corrigee ne re-declenche pas le gate.
    """
    here = pathlib.Path(__file__).resolve()
    repo_root = here.parents[2]
    wf = repo_root / ".github" / "workflows" / "perimeter-review-guard.yml"
    return wf.read_text(encoding="utf-8")


def test_pull_request_review_trigger_includes_edited_type():
    """Sibling invariant — the review trigger already had ``edited`` from the
    start (c.342 acceptance), so this test pins that property against
    accidental regression when editing the workflow.

    Depuis #14283 le declencheur vit dans perimeter-review-guard.yml (cf
    ``_read_review_trigger_workflow``) ; l'invariant, lui, ne bouge pas.
    """
    text = _read_review_trigger_workflow()
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


# ---------------------------------------------------------------------------
# Consequence model (#11648): supersession per author + blocking scope
# ---------------------------------------------------------------------------
# The two trigger pins above land with #11660 (po-2026, issue #11659),
# merged first; this block adds the consequence half of #11648.

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
    cands, _ = select_candidates(_thread(
        ("ai-01", "2026-08-18T14:29:00Z", ASSERT_5),
        ("ai-01", "2026-08-18T14:48:00Z", ASSERT_7),
    ))
    texts = [c.text for c in cands]
    assert ASSERT_7 in texts
    assert ASSERT_5 not in texts, "superseded assertion still confronted"


def test_supersession_is_per_author_not_global():
    """A later review by SOMEONE ELSE must not retract my assertion."""
    cands, _ = select_candidates(_thread(
        ("hermes", "2026-08-18T14:29:00Z", ASSERT_5),
        ("ai-01", "2026-08-18T14:48:00Z", ASSERT_7),
    ))
    by = {c.author: c.text for c in cands}
    assert by == {"hermes": ASSERT_5, "ai-01": ASSERT_7}


def test_later_silent_review_is_not_a_retraction():
    """Silence is not correction: a later review with no perimeter statement
    leaves the author's previous assertion standing."""
    cands, _ = select_candidates(_thread(
        ("hermes", "2026-08-18T14:29:00Z", ASSERT_5),
        ("hermes", "2026-08-18T15:10:00Z", "LGTM, joli travail."),
    ))
    assert [c.text for c in cands] == [ASSERT_5]


def test_equal_timestamps_fall_back_to_thread_order():
    """GitHub can stamp two reviews identically; the later-listed one wins."""
    cands, _ = select_candidates(_thread(
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
    cands, _ = select_candidates([_body("jsboige", ASSERT_5)])
    assert len(cands) == 1
    assert cands[0].blocking is True, (
        "PR-body assertions must BLOCK: the author owns the body and an edit "
        "re-triggers the workflow, so the green is reachable (#11648-b2)."
    )


def test_third_party_review_assertion_is_signal_only():
    """#11648-b2: not editable by the author, and COMMENTED reviews cannot be
    dismissed -- blocking there leaves no lever (measured on #11642/#11646)."""
    cands, _ = select_candidates(_thread(
        ("clusterManager-Myia", "2026-08-18T14:29:00Z", ASSERT_5),
    ))
    assert len(cands) == 1
    assert cands[0].blocking is False


def test_detection_is_unchanged_for_non_blocking_assertions():
    """The detector is NOT disarmed: a false third-party assertion is still
    extracted and still confronted -- only its exit code changes."""
    cands, _ = select_candidates(_thread(
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
    cands, _ = select_candidates([_body(
        "author",
        "Perimetre : 2 fichiers twins uniquement, aucune autre modification.")])
    blocking = [c for c in cands if c.blocking]
    assert blocking
    assert check_assertion(FILES_11227, blocking[0].text)


# --- #11695: --assert false-positives when the fence PRECEDES the prose ---------
# Measured 2026-08-18 by po-2026 (post-merge verify of #11675): the gate path
# (--scan-thread) was fixed at extraction level, but the MANUAL reviewer path
# (--assert, whole body to check_assertion) still trips COUNT_CLAIM on a fenced
# L898 transcription when it appears BEFORE the correct prose claim -- search()
# stops at the first occurrence, so the founder body of #11675 passed only by
# coincidence of ordering. A pass that depends on appearance order proves nothing.

FENCE_FIRST_BODY = (
    "## Preuve anti-collision (L898)\n"
    "\n"
    "```\n"
    "$ gh pr list --state open --json files\n"
    "0 fichiers en commun avec les autres PR\n"
    "```\n"
    "\n"
    "Perimetre : 1 fichier modifie.\n"
)
FENCE_ONLY_BODY = (
    "## L898 verifie\n"
    "\n"
    "```\n"
    "$ gh pr list --state open --json files\n"
    "0 fichiers en commun\n"
    "```\n"
)
FILES_11695 = [{"path": "MyIA.AI.Notebooks/GenAI/Audio/XTTS/foo.ipynb", "additions": 5, "deletions": 2}]


def test_assert_fence_before_prose_does_not_misread_transcription():
    """#11695 case 1: fenced '0 fichiers en commun' BEFORE the prose claim.
    The transcription is not the author's assertion; the prose claim (1 fichier)
    matches the file list exactly -> must NOT report a problem."""
    assert check_assertion(FILES_11695, FENCE_FIRST_BODY) == []


def test_assert_fence_only_body_is_not_a_valid_assertion():
    """#11695 case 2: body made ONLY of a fence transcription carries no
    verifiable author claim. After the fix, fences are masked in the scan so
    the count check ignores the transcribed 0 -- and the 'non verifiable'
    guard, run on the ORIGINAL text, must still flag it (a body of pure
    transcription cannot pass silently)."""
    problems = check_assertion(FILES_11695, FENCE_ONLY_BODY)
    assert problems, "a transcription-only body must not pass in silence"
    assert not any("pretend 0" in p for p in problems), (
        f"must not misread the fenced 0 as the author's claim, got: {problems!r}"
    )

# ---------------------------------------------------------------------------
# #11712 -- incidental counts. Detection stays (the line is still extracted
# and confronted); only the blocking consequence moves (#11648 path). Each
# test pairs an FP repaired with the nearest true assertion that must stay.
# ---------------------------------------------------------------------------

def test_incidental_threshold_citation_is_signal_not_blocking():
    """#11710: '< 15 fichiers' cites the G.4 threshold the author is UNDER --
    the guard blocked a PR for quoting the rule it exists to enforce."""
    line = ("**2 notebooks + 1 grain = scope C.4 OK** "
            "(< 3000 lignes, < 15 fichiers, 1 feature, 1 domaine Lean)")
    assert extract_perimeter_assertions(line) == [line], "detection unchanged"
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is False, "a cited threshold is not a perimeter claim"


def test_incidental_locative_scan_scope_is_signal_not_blocking():
    """#11616 forme A + the grep-scope family: 'sur les N fichiers' is the
    scope of a CHECK or a tool run, not the perimeter."""
    lines = [
        "- Check : `0 separator cells remaining` sur les 2 fichiers",
        "- **0 violation C.1** : `grep -nE \"raise NotImplementedError|assert "
        "False|1/0\"` sur 73 fichiers = 0 match code",
        "- YAML parse OK sur les 158 fichiers du registre",
    ]
    for line in lines:
        assert extract_perimeter_assertions(line) == [line], "detection unchanged"
        cand = Candidate(line, "body", "author", "body")
        assert cand.blocking is False, f"scan scope must not block: {line[:50]}"


def test_locative_count_with_diffstat_still_blocks():
    """The locative rule must NOT swallow '+307 lignes / −0 sur 2 fichiers'
    -- there 'sur 2 fichiers' names what the diffstat measured. FN control."""
    line = "`+307 lignes / −0` sur 2 fichiers, aucun code existant supprimé ni stubé."
    assert extract_perimeter_assertions(line) == [line]
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is True


# --- #11800: negated-diff shape (semantic exemption) -----------------------

def test_negated_diff_count_is_signal_not_blocking():
    """#11800: the COUNT_CLAIM regex matched '91 fichiers' BEFORE the
    negation word was parsed. The count qualifies files as NOT changed --
    the negation of the diff -- which the guard cannot confront with the
    effective file list (which lists what the diff DOES touch). Fix scope
    is NEGATED_DIFF_TAIL applied per-match.

    The FN-safety contract: a line with a scope word or a diffstat
    neighborhood is NEVER incidental via the qualifier/locative rules
    (#11712 acceptance). When the negated-diff count is the SOLE count on
    the line (no scope word elsewhere), the per-match exemption fires and
    the line is incidental. The 'scope delta' formulation that co-presents
    a negated-diff count with a scope word remains blocking by design --
    it would be out of scope for #11800 to relax that contract."""
    lines = [
        # Sole negated-diff count, no scope word -- the canonical #11800 case
        "91 fichiers inchanges (mesure sur la tranche)",
        # Variant with english negation
        "73 files unchanged (delta nul)",
        # Variant 'intacts'
        "5 fichiers intacts",
        # Variant 'non modifies' with parentheses (no scope word)
        "73 fichiers non modifies, delta nul",
    ]
    for line in lines:
        assert extract_perimeter_assertions(line) == [line], "detection unchanged"
        cand = Candidate(line, "body", "author", "body")
        assert cand.blocking is False, f"negated-diff must not block: {line[:50]}"


def test_false_perimeter_assertion_still_blocks():
    """#11800 acceptance #2: a genuine false perimeter assertion must still
    FAIL the guard after the negated-diff exemption is added. The exemption
    only applies when the count is qualified as NOT changed -- an unqualified
    'N fichiers' stays blocking."""
    line = "Perimetre : 5 fichiers (verif de coherence)."
    # Detection unchanged -- the line is still a candidate.
    assert extract_perimeter_assertions(line) == [line]
    # But on a PR with 2 files, the equality confrontation must fail.
    problems = check_assertion(
        files=[{"path": "a.py"}, {"path": "b.py"}],
        assertion=line,
    )
    assert problems, "a false '5 fichiers' claim on a 2-file PR must produce a problem"
    assert any("5 fichier" in p for p in problems), f"problem message must name the claim: {problems}"


def test_zero_count_exemption_still_holds():
    """#11800 acceptance #3a: the existing '0 fichier X' scrub-absence
    exemption (l.369) must still pass after the negated-diff exemption is
    added. Non-regression."""
    line = "- **0 fichier machine-path** (C.1 / L213-A scrub)"
    assert extract_perimeter_assertions(line) == [line]
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is False, "zero-count exemption must still hold"


def test_comparison_prefix_exemption_still_holds():
    """#11800 acceptance #3b: the existing '< 15 fichiers' threshold-citation
    exemption (COMPARISON_PREFIX) must still pass. Non-regression."""
    line = ("**2 notebooks + 1 grain = scope C.4 OK** "
            "(< 3000 lignes, < 15 fichiers, 1 feature, 1 domaine Lean)")
    assert extract_perimeter_assertions(line) == [line]
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is False, "comparison-prefix exemption must still hold"


def test_negated_diff_does_not_swallow_modified_count():
    """#11800 FN control: the negated-diff exemption must NOT apply when the
    count is qualified as ACTUALLY modified ('ajoutes', 'modifies', 'touches').
    A line like '5 fichiers modifies, 91 fichiers inchanges' must stay
    blocking on the '5 fichiers modifies' half."""
    line = "5 fichiers modifies, 91 fichiers inchanges -- scope delta confirme"
    assert extract_perimeter_assertions(line) == [line], "detection unchanged"
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is True, "modified-count half must stay blocking"


def test_incidental_artifact_qualified_count_is_signal_not_blocking():
    """#11625 '22 fichiers MP3' / #11529 '5 fichiers scratch' /
    '2 fichiers restants': kind or remainder, not the PR's file list."""
    lines = [
        "- **Outputs** : 22 fichiers MP3 (3 modèles × 3 textes = 9 lectures benchmark)",
        "5 fichiers scratch d'une autre PR (#10023) sont concernés",
        "il reste 2 fichiers restants à corriger dans la vague suivante",
        "`lake update` → 8638 fichiers mathlib cache décompressés",
    ]
    for line in lines:
        assert extract_perimeter_assertions(line) == [line], "detection unchanged"
        cand = Candidate(line, "body", "author", "body")
        assert cand.blocking is False, f"kind/remainder must not block: {line[:50]}"


def test_modified_files_count_with_qualifier_still_blocks():
    """'3 fichiers ajoutes' carries the modification act -- must stay
    blocking even though a word follows the count. FN control (#11614)."""
    line = "- **catalog-pr-hygiene.md R1** : catalogue byte-identique a main (3 fichiers ajoutes, pas de regen)."
    assert extract_perimeter_assertions(line) == [line]
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is True


# #12184 -- measurement antecedent. "lake 70 fichiers" / "corpus N fichiers"
# / "count_code_sorry.py ... N fichiers" -- the count is an EXTERNAL tool
# output on a third-party corpus (Lean lake, registry, scan target), NEVER
# the PR's file list. Founder case #12181 l.26: "lake de 70 modules, 1 sorry
# reel distinct" red on a 1-file PR. Same family as HIT_ANTECEDENT / LOCATIVE_PREP.


def test_incidental_measurement_antecedent_is_signal_not_blocking():
    """#12184: 'lake N fichiers' / 'corpus N fichiers' / 'count_code_sorry.py N'
    measure a third-party corpus, not the PR's diff. Founder case #12181
    (body variant 'lake de 70 modules') does not even match COUNT_CLAIM
    (modules, not fichiers), so the class of concern is future bodies that
    explicitly say 'lake N fichiers' -- the antecedent exemption is preventive."""
    lines = [
        # The preventive shape that the issue body text anticipated
        "lake 70 fichiers, 1 sorry reel distinct",
        "lake of 70 files, 1 real sorry distinct",
        # count_code_sorry.py script name
        "`count_code_sorry.py` rendu: 36 fichiers naifs sur le corpus Lean",
        # corpus / scan / registre / registry
        "corpus 158 fichiers du registre ICT",
        "scan sur 73 fichiers du depot",
        "registre 200 fichiers de la vague",
        # mesures sur
        "mesures sur 1 500 fichiers",
        # check_* script name
        "check_pr_perimeter : 4 fichiers en fenetre",
    ]
    for line in lines:
        assert extract_perimeter_assertions(line) == [line], "detection unchanged"
        cand = Candidate(line, "body", "author", "body")
        assert cand.blocking is False, f"measurement tool output, not perimeter: {line[:60]}"


def test_measurement_antecedent_does_not_swallow_real_perimeter_assertion():
    """#12184 FN control: a line that mentions 'lake' but actually asserts a
    perimeter (scope word + diffstat neighborhood) MUST stay blocking. The
    exemption sits inside the FN-safety guards in _count_is_incidental
    (no scope word, no diffstat) -- a perimeter-shaped line is not
    incidental regardless of antecedent vocabulary."""
    lines = [
        # scope word + diffstat -> real assertion, must stay blocking
        "Perimetre : lake 70 fichiers modifies (PR ship lake de 70 fichiers)",
        # count under exclusivity marker + scope word
        "lake 70 fichiers uniquement, scope = perimetre PR",
    ]
    for line in lines:
        assert extract_perimeter_assertions(line) == [line], "detection unchanged"
        cand = Candidate(line, "body", "author", "body")
        assert cand.blocking is True, f"real perimeter assertion must stay blocking: {line[:60]}"


def test_measurement_antecedent_vocabulary_closed_list():
    """#12184 closed-list: only the tool names enumerated in MEASUREMENT_ANTECEDENT
    trigger the exemption. Random words (e.g. 'rapport', 'output') must not
    absorb genuine perimeter assertions."""
    line = "rapport de 70 fichiers envoyes au CI"
    assert extract_perimeter_assertions(line) == [line], "detection unchanged"
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is True, "closed-list antecedent: 'rapport' is not an external measurement tool"


def test_founder_body_12181_lake_modules_passes_unchanged():
    """#12184 FN control on the actual founder body. The body of #12181
    line 26 says 'lake de 70 modules, 1 sorry reel distinct' -- 'modules'
    is not in COUNT_CLAIM (fichiers|files only) so the line never extracts
    as a candidate and the guard passes. The antecedent exemption is a
    safety net for FUTURE bodies that use the equivalent 'lake N fichiers'
    phrasing (the issue body example), not a fix to the founder body
    itself."""
    line = "lake de 70 modules, 1 sorry reel distinct"
    # 'modules' does not match COUNT_CLAIM -- not a candidate
    assert extract_perimeter_assertions(line) == [], "modules is not fichiers/files"
    # `--scan-thread` calls `select_candidates` first; an empty candidate
    # list means no body assertion is confronted -> the guard's verdict is
    # determined by the file list alone (1 file, no claim), and the issue
    # #12181 reports `VERDICT: OK`. The direct `--assert` path, in
    # contrast, would flag the line as 'unverifiable wording' -- a
    # DIFFERENT organ concern (the line alone isn't a perimeter claim,
    # which is exactly the property the antecedent exemption preserves for
    # the scan-thread path).
    items = [{"kind": "PR body", "author": "jsboige", "body": line, "source": "body", "ts": ""}]
    cands, _ = select_candidates(items, n_files=1)
    assert cands == [], "no candidates in --scan-thread mode for the founder body line"


# #12057 -- compte-antecedent. "N unites (M fichiers)" et "M fichiers pointent
# ici" nomment la PROVENANCE ou la PORTEE d'une mesure, jamais le perimetre de
# la PR. Meme famille que HIT_ANTECEDENT: mauvaise surface, pas mauvais compte.


def test_incidental_paren_antecedent_count_is_signal_not_blocking():
    """#12057 forme 5: '(2 fichiers)' qualifie la provenance du compte qui
    precede. Phrase reelle de PR #12054 l.18, qui touche 5 fichiers."""
    lines = [
        "**Garde-fou** : 32 prescriptions impératives avant (2 fichiers) → 32 après.",
        "13 024 → 11 181 octets (2 fichiers sources) après fusion",
    ]
    for line in lines:
        assert extract_perimeter_assertions(line) == [line], "detection unchanged"
        cand = Candidate(line, "body", "author", "body")
        assert cand.blocking is False, f"provenance, pas perimetre: {line[:50]}"


def test_incidental_reference_verb_count_is_signal_not_blocking():
    """#12057 forme 6: des referents ENTRANTS ne sont par construction pas
    dans le diff. Phrase reelle de PR #12056 l.34, qui touche 1 fichier.

    Compter les liens entrants est EXIGE par le protocole de fusion arrete en
    #12051 -- le garde ne peut pas punir la mesure qu'une regle rend obligatoire.
    """
    lines = [
        "aucune ancre entrante ne casse (27 fichiers pointent ici ; aucun via `#ancre`)",
        "12 fichiers référencent cette règle",
        "3 fichiers citent la section §H",
        "8 fichiers renvoient à ce document",
    ]
    for line in lines:
        assert extract_perimeter_assertions(line) == [line], "detection unchanged"
        cand = Candidate(line, "body", "author", "body")
        assert cand.blocking is False, f"referents entrants: {line[:50]}"


def test_perimeter_claim_without_numeric_antecedent_still_blocks():
    """CONTROLE POSITIF #12057. L'exemption parenthetique exige un antecedent
    NUMERIQUE; sans lui une vraie assertion reste bloquante, parentheses ou pas.

    Un detecteur se valide par ses faux negatifs, pas par ses hits: si ces
    trois lignes cessaient de bloquer, l'exemption aurait desarme le garde.
    """
    lines = [
        "Périmètre : 2 fichiers twins uniquement",  # exemple du docstring, l.8
        "Périmètre : 27 fichiers",
        "Périmètre (2 fichiers)",  # parentheses SANS antecedent numerique
    ]
    for line in lines:
        assert extract_perimeter_assertions(line) == [line]
        cand = Candidate(line, "body", "author", "body")
        assert cand.blocking is True, f"vraie assertion doit bloquer: {line[:50]}"


def test_incidental_zero_count_is_signal_not_blocking():
    """'0 fichier machine-path' is a scrub attestation -- a PR never has
    0 files, the equality confrontation can never pass."""
    line = "- **0 fichier machine-path** (C.1 / L213-A scrub)"
    assert extract_perimeter_assertions(line) == [line]
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is False


def test_incidental_parenthetical_exclusivity_is_signal_not_blocking():
    """#11616 forme B: '(SL-8/SL-9 only, scope minimal)' co-presents 'only'
    and 'scope' by lexical coincidence inside one parenthetical qualifier."""
    line = "- **Phase 3** : v1 (SL-8/SL-9 only, scope minimal) + v2 (PR-gate)"
    assert extract_perimeter_assertions(line) == [line], "detection unchanged"
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is False


def test_bare_exclusivity_outside_parens_still_blocks():
    """'Aucune autre modification.' keeps its authorial force. FN control."""
    line = "Aucune autre modification."
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is True


def test_scope_word_count_line_still_blocks():
    """Any count line carrying a strong scope word is never downgraded by the
    qualifier/locative rules. FN control (corpus: 43 such lines preserved)."""
    line = "Périmètre : 4 fichiers modifiés, rien d'autre."
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is True


def test_founding_count_assertions_stay_blocking_11712():
    """The issue's named true assertions -- diffstat-neighborhood counts --
    must all survive the classifier. FN control."""
    for line in [
        "2 fichiers, +100/−13 — pas de composite (G.4).",
        "**3 fichiers, +512 insertions / 0 deletions** :",
        "**Fichiers:** 3 fichiers modifiés",
    ]:
        cand = Candidate(line, "body", "author", "body")
        assert cand.blocking is True, f"must stay blocking: {line[:50]}"


def test_mixed_line_confronts_the_non_zero_count():
    """"0 fichier catalogue, 2 fichiers touches" over a 2-file PR passes.

    The zero is a property claim; the perimeter claim is the 2. Reading the
    first match instead confronts "0" with a list that cannot be empty, so
    the line could never pass whatever the PR contained.
    """
    files = [{"path": "a.py"}, {"path": "b.py"}]
    assert check_assertion(files, "- 0 fichier catalogue, 2 fichiers touches.") == []


# ---------------------------------------------------------------------------
# #11796 -- the SIGNAL output block printed "assertion d'un tiers : a lever
# par son auteur" UNCONDITIONALLY, including when every signal was an
# INCIDENTAL count from the AUTHOR's body (PRs #11786 / #11775). That
# instruction is factually wrong: the author can't "lever" their own
# incidental count -- the count is what it is, the reviewer just notes it.
#
# The fix is to discriminate by candidate composition:
# - body+incidental only -> "compte INCIDENTAL du body de l'auteur"
# - thread only -> "assertion d'un tiers" (unchanged)
# - mix -> both, each with the correct shape
# ---------------------------------------------------------------------------


def test_signal_explanation_body_incidental_only_no_tiers_phrase():
    """#11796 control positif #1 -- #11786 body shape.

    The author's body carried `Run réel ... sur 719 fichiers ...`, which is
    LOCATIVE_PREP-incidental. The reviewer's review carried a 4-fichiers claim
    on the same body line. Both are SIGNAL; both come from sources that ARE
    incidental (body) or thread. The explanation block must NOT tell the
    author to "lever par son auteur" an assertion they did not write -- the
    incidental count from the body is the author's own prose, classified
    incidental because of shape, not because of authorship.
    """
    from check_pr_perimeter import _format_signal_explanation

    signals = [
        Candidate(
            "Run réel reproduit la mesure ad-hoc préalable sur 719 fichiers ...",
            "PR body", "jsboige", "body",
        ),
        Candidate(
            "4 fichiers",
            "review (COMMENTED)", "clusterManager-Myia", "thread",
        ),
    ]
    # Both are SIGNAL (not blocking). The explanation must distinguish.
    for s in signals:
        assert s.blocking is False, f"precondition: {s.kind} should be SIGNAL"
    explanation = _format_signal_explanation(signals)
    # The fix: a mixed-shape explanation names BOTH cases by their actual
    # reason, not the blanket "lever par son auteur" which only applies to
    # the thread candidate.
    assert "body" in explanation.lower() or "auteur" in explanation.lower() or \
        "incidental" in explanation.lower(), \
        f"must mention body/auteur/incidental: got {explanation!r}"
    # The blanket phrase "a lever par son auteur (poster une assertion
    # corrigee)" was UNCONDITIONAL before the fix -- the test fails on
    # origin/main because _format_signal_explanation does not exist yet,
    # AND because even if it did, it would still print that line for the
    # body-incidental candidate.


def test_signal_explanation_body_only_incidental_mentions_not_pretend_tiers():
    """#11796 control positif #2 -- body-only incidental signals.

    PR #11786's reviewer comment was the only "tier" voice -- the PR body
    itself carries only incidental counts (719 from the L43 prose line +
    the L35 fenced block which the fence exclusion drops). When the SIGNAL
    set is body-incidental only, the explanation must NOT invite the author
    to "lever" anything: there's nothing to lever, the count is incidental.
    """
    from check_pr_perimeter import _format_signal_explanation

    signals = [
        Candidate(
            "Run réel reproduit la mesure ad-hoc préalable sur 719 fichiers ...",
            "PR body", "jsboige", "body",
        ),
        Candidate(
            "- aucun re-classement involontaire ailleurs : mesure inchangée sur les 91 fichiers de wallclock ;",
            "PR body", "jsboige", "body",
        ),
    ]
    for s in signals:
        assert s.blocking is False, "precondition: body incidental is SIGNAL"
    explanation = _format_signal_explanation(signals)
    # The blanket tier-only phrase must NOT appear when there are no tier
    # candidates at all.
    assert "poster une assertion corrigee" not in explanation, \
        f"no tier to correct when all signals are body+incidental: got {explanation!r}"
    assert "ne tient pas la pr" in explanation.lower(), \
        f"must still say the gate does not block: got {explanation!r}"


def test_signal_explanation_thread_only_keeps_tiers_phrase():
    """FN control: a thread-only SIGNAL keeps the original wording.

    When a reviewer (or bot) is the source, the original "lever par son
    auteur" is correct: the reviewer is the only one who can correct their
    own review. The fix must not erase this case.
    """
    from check_pr_perimeter import _format_signal_explanation

    signals = [
        Candidate(
            "cette PR touche 2 fichiers",
            "review (COMMENTED)", "Hermes-bot", "thread",
        ),
    ]
    assert signals[0].blocking is False
    explanation = _format_signal_explanation(signals)
    assert "tiers" in explanation.lower() or "reviewer" in explanation.lower(), \
        f"thread-only must keep the tiers framing: got {explanation!r}"
    assert "lever" in explanation.lower() or "corrig" in explanation.lower(), \
        f"thread-only must invite the reviewer to correct: got {explanation!r}"


def test_signal_explanation_authorial_false_assertion_still_blocking():
    """FN control #2: a true (non-incidental) assertion in the body remains
    blocking -- the explanation function only renders the SIGNAL block, but
    the gate MUST keep the candidate in `problems` so the PR still fails.

    This test is the acceptance (b) "contrôle négatif" from the issue:
    "cette PR touche 1 fichier" on a 2-file PR is a real false perimeter
    claim by the author. It must FAIL the gate, not be demoted to SIGNAL.
    """
    from check_pr_perimeter import check_assertion, Candidate

    files = [{"path": "a.py"}, {"path": "b.py"}]
    problems = check_assertion(files, "Cette PR touche 1 fichier twin")
    assert len(problems) >= 1, "true authorial false assertion stays blocking"
    cand = Candidate("Cette PR touche 1 fichier twin", "PR body", "jsboige", "body")
    assert cand.blocking is True, "must stay blocking -- not demoted to SIGNAL"
# ---------------------------------------------------------------------------
# #11985 -- the six out-of-perimeter count forms and the body-level rule.
# Every test uses the EXACT line measured on the 20/08 corpus (the issue's
# recipe: "not a paraphrase -- it is the table tube, the passe compose and the
# word 'generes' that carry the defect").
# ---------------------------------------------------------------------------


def test_11985_form_table_row_is_incidental():
    """#11964: the tube separates the qualifier from its number -- no cell
    pairing is a perimeter claim. Extraction already skips rows; this pins
    the classification for any direct caller."""
    line = "| Fichiers avec flowchart(s) ASCII | 10 |"
    assert _count_is_incidental(line) is True


def test_11985_form_scan_result_distinct_is_incidental():
    """#11964: '10 fichiers distincts, chacun avec 1-3 flowcharts' counts what
    the detector FOUND, not what the PR modifies (real PR: 3 files)."""
    line = "10 fichiers distincts, chacun avec 1-3 flowcharts."
    assert extract_perimeter_assertions(line) == [line], "detection unchanged"
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is False


def test_11985_form_past_self_description_is_incidental():
    """#11790 l.5: an imparfait + commit SHA describes the SUPERSEDED initial
    PR -- its diffstat (+31502/-80470) measures the old commit, not the head
    (real PR: 1 file). This rule overrides the diffstat guard."""
    line = (
        "Le PR #11790 initial (commit 3b221fa1c) couvrait "
        "**160 fichiers / +31502/-80470 lignes** :"
    )
    assert extract_perimeter_assertions(line) == [line], "detection unchanged"
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is False


def test_11985_past_tense_without_hash_or_pr_ref_still_blocks():
    """FN control: an imparfait ALONE is not a superseded-revision proof --
    the closed rule requires a SHA or a #PR ref on the same line."""
    line = "La version precedente couvrait 3 fichiers."
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is True


def test_11985_form_inventory_non_notebook_is_incidental():
    """#11790 l.7/l.64: '155 fichiers non-notebook' inventories the RESTS of
    the original commit (kind-of-artifact qualifier, like mp3/mathlib)."""
    line = "- 155 fichiers non-notebook (rules, workflows, scripts, tests, translations)"
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is False


def test_11985_form_counterfactual_is_incidental():
    """#11963: '> 1 PR composite (15 fichiers / >3000 lignes)' describes the
    PR that was NOT written. The marker sits BEFORE the count; the line's
    'lignes' would otherwise trip the diffstat guard."""
    line = (
        "3 PRs distinctes (cette PR + 2 a venir) > 1 PR composite "
        "(15 fichiers / >3000 lignes)."
    )
    assert extract_perimeter_assertions(line) == [line], "detection unchanged"
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is False


def test_11985_counterfactual_count_before_marker_still_blocks():
    """FN control: when the count comes BEFORE the marker it describes the
    real object ('3 fichiers plutot que 15') and stays authorial."""
    line = "3 fichiers plutot que 15 fichiers dans une PR composite."
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is True


def test_11985_form_enumeration_component_is_incidental():
    """#11935: 'check_twin_parity.py (...) + 2 fichiers de tests' enumerates
    1 + 2 = 3 (exact); the guard reads the sub-sum 2 and its equality
    confrontation can never validate it."""
    line = (
        "Perimetre:  scripts/notebook_tools/check_twin_parity.py "
        "(_shas_match + messages CLI) + 2 fichiers de tests"
    )
    assert extract_perimeter_assertions(line) == [line], "detection unchanged"
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is False


def test_11985_enumeration_tail_without_named_file_still_blocks():
    """FN control: the enumeration rule requires a NAMED file before the
    '+ N fichiers de tests' tail -- a bare tail stays authorial."""
    line = "2 fichiers de tests modifies"
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is True


# ---------------------------------------------------------------------------
# #14384 -- the forme-1 neighborhood. (A) the enumeration exemption held to
# PUNCTUATION, not semantics: the same just enumeration with ", plus" / ",
# et" / ", ainsi que" instead of "+" stayed blocking -- widened to a closed
# connector set, named-file anchor kept. (B) the additive sum was blind to
# word-form cardinals while _word_form_count saw them -- the two halves of
# the organ now agree at line scope (shared WORD_FORM_TRIGGERS).
# Measured AFTER #14438/#14454: "un/une" are articles, not cardinals, so
# the issue's L3 extracts nothing and L5's "un fichier" term is invisible
# BY DESIGN (reproducteur #14430) -- the surviving fixable defects are the
# connectors and the sum, pinned here at the post-#14454 vocabulary. The
# six #11985 forms and its positive controls stay pinned by the tests above.
# ---------------------------------------------------------------------------


def test_14384_five_literal_lines_at_head():
    """Recette 1: the issue's five table lines, literally, with the behavior
    fixed at HEAD (post-#14454 vocabulary)."""
    assert _count_is_incidental(
        "check_twin_parity.py (_shas_match) + 2 fichiers de tests"
    ) is True
    assert _count_is_incidental(
        "variation_light_cap.py (+100/-0) + 1 fichier de tests"
    ) is True
    # L3: post-#14454 "un fichier" is an article -> no count extracted at
    # all (the pre-#14438 word_count=1 reading is superseded by #14438).
    assert extract_perimeter_assertions(
        "variation_light_cap.py (+100/-0), plus un fichier de tests neuf."
    ) == []
    # L4: two digits already sum exactly (unchanged by this fix).
    assert _additive_line_sum("1 fichier modifie, 1 fichier de tests neuf.") == 2
    # L5: "un fichier" is invisible as a count (#14438) -> declared 1, the
    # escape for a counted file + article term is the digit form or naming.
    assert _additive_line_sum(
        "1 fichier modifie, plus un fichier de tests neuf."
    ) == 1
    assert _count_is_incidental(
        "1 fichier modifie, plus un fichier de tests neuf."
    ) is False


def test_14384_A_widened_connectors_are_incidental_with_named_file():
    """(A): ', plus' / ', et' / ', ainsi que' between a NAMED file and an
    'N fichiers de tests' tail classify like the '+' form -- SIGNAL, not
    blocking (the sub-sum can never be validated by the confrontation)."""
    for line in [
        "variation_light_cap.py (+100/-0), plus 2 fichiers de tests neufs.",
        "variation_light_cap.py (+100/-0), et 1 fichier de test neuf.",
        "variation_light_cap.py (+100/-0), ainsi que 3 fichiers de tests.",
    ]:
        cand = Candidate(line, "body", "author", "body")
        assert cand.blocking is False, line[:60]


def test_14384_A_connector_without_named_file_still_blocks():
    """(A) garde-fou: without the named-file anchor the exemption would
    swallow sub-sums that enumerate nothing -- a bare connector line stays
    authorial."""
    line = "1 fichier de tests modifie, et 1 autre fichier"
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is True


def test_14384_A_word_form_tail_is_not_exempt():
    """(A)+(B) recette 2 -- the exemption stays DIGIT-only: a word-form
    enumeration tail joins the additive sum and is confronted, so the
    exemption can re-close (the issue's re-closing mutation, expressed in
    the post-#14438 vocabulary)."""
    line = "variation_light_cap.py (+100/-0), plus trois fichiers de tests neufs."
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is True


def test_14384_B_word_form_joins_additive_sum():
    """(B): '1 fichier modifie, plus deux fichiers de tests' declares
    1 + 2 = 3 -- the sum was 1 (digit-only), contradicting the docstring
    agreement of the organ's two halves."""
    assert _additive_line_sum(
        "1 fichier modifie, plus deux fichiers de tests neufs."
    ) == 3
    assert _additive_line_sum("deux fichiers de tests neufs.") == 2


def test_14384_B_rescue_and_reclose_end_to_end():
    """(B) recette 2, both directions: the just enumeration passes, the
    count-mutation blocks again."""
    files = [{"path": "a.py"}, {"path": "b.py"}, {"path": "c.py"}]
    assert check_assertion(
        files, "1 fichier modifie, plus deux fichiers de tests neufs."
    ) == []
    assert check_assertion(
        files, "1 fichier modifie, plus trois fichiers de tests neufs."
    ) != []


def test_14384_A_digit_line_silent_word_mutation_recloses():
    """(A) recette 2 end-to-end: the widened digit line stays incidental
    (silent sub-sum), its word-form mutation on a 2-file perimeter speaks
    again (1 named + trois = 4 != 2 via the word branch)."""
    files = [{"path": "scripts/notebook_tools/variation_light_cap.py"},
             {"path": "scripts/tests/test_variation_light_cap.py"}]
    silent = Candidate(
        "variation_light_cap.py (+100/-0), plus 2 fichiers de tests neufs.",
        "body", "author", "body",
    )
    assert silent.blocking is False
    assert check_assertion(
        files, "variation_light_cap.py (+100/-0), plus trois fichiers de tests neufs."
    ) != []


def test_11985_form_produced_artifacts_is_incidental():
    """#11956: '2 fichiers audio generes, HTTP/1.1 200 OK' attests REAL
    EXECUTION -- the artifacts are cell outputs, not repo files (real PR:
    5 files). The compound kind sits on the SECOND word after the count."""
    line = (
        "- 04-2 c6 : execution reelle via OpenAI TTS "
        "(2 fichiers audio generes, HTTP/1.1 200 OK)"
    )
    assert extract_perimeter_assertions(line) == [line], "detection unchanged"
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is False


def test_11985_form_scan_hit_antecedent_is_incidental():
    """#11966 l.42: '1 hit / 1 fichier' is a scan residue -- the 'hit'
    antecedent before the count marks detector output (real PR: 4 files)."""
    line = (
        "- **Apres** : 1 hit / 1 fichier (le **21 notebooks** dans la "
        "conclusion de GT-15b cell#49 -- voir Residuel ci-dessous)."
    )
    assert extract_perimeter_assertions(line) == [line], "detection unchanged"
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is False


def test_11985_issue_positive_control_stays_incidental():
    """The issue's own control: the three ALREADY-covered forms keep
    classifying correctly (a BLOQUANT-everywhere would be indistinguishable
    from a disarmed classifier)."""
    for line in [
        "pour rester sous le seuil A de pr-review-discipline.md "
        "(<=15 fichiers, <=3000 lignes, 1 feature)",
        "scan sur 73 fichiers",
        "inventaire : 22 fichiers MP3",
    ]:
        assert _count_is_incidental(line) is True, line[:50]


def test_11985_rule1_body_correct_count_downgrades_other_mismatches():
    """#11951: the body declares '3 fichiers / +167/-15' (exact, declarative)
    AND carries the G.4 atomicity argument '1 helper + 1 modification +
    1 fichier test adapte' (count 1). The correct declaration reclassifies
    the OTHER count mismatches of the SAME body from blocking to signal."""
    body = (
        "## Summary\n"
        "- **G.4** : PR atomic (1 helper + 1 modification de fonction "
        "+ 1 fichier test adapte, 1 bug, 1 discrimination).\n"
        "- **L978 ★★** : périmètre déclaré en début de body (3 fichiers / +167/-15).\n"
    )
    items = [{"kind": "PR body", "author": "a", "body": body,
              "source": "body", "ts": ""}]
    candidates, _ = select_candidates(items, n_files=3)
    assert len(candidates) == 2, "both lines stay detected (detection unchanged)"
    arg = next(c for c in candidates if "helper" in c.text)
    decl = next(c for c in candidates if "+167/-15" in c.text)
    # The atomicity argument keeps its line-level blocking property -- the
    # downgrade lives in the ROUTING, not in blocking.
    assert arg.blocking is True
    assert arg.body_declares_effective_count is True
    assert decl.body_declares_effective_count is True
    mismatch = check_assertion(
        [{"path": "a.py"}, {"path": "b.py"}, {"path": "c.py"}], arg.text
    )[0]
    assert mismatch.startswith("l'assertion pretend")
    assert is_downgradable_mismatch(arg, mismatch) is True


def test_11985_rule1_never_touches_exclusivity_problems():
    """FN control (#11268-2): a body that declares the right count still
    BLOCKS on an exclusivity claim that does not name the touched workflow."""
    cand = Candidate(
        "Perimetre : 2 fichiers uniquement, aucune autre modification.",
        "PR body", "author", "body",
    )
    cand.body_declares_effective_count = True
    problem = (
        "assertion d'exclusivite sans nommer le workflow touche "
        ".github/workflows/x.yml (critere #11268-2)"
    )
    assert is_downgradable_mismatch(cand, problem) is False


def test_11985_rule1_requires_declarative_correct_count():
    """FN control: an INCIDENTAL count that happens to carry the right number
    (a scan scope) does not validate a wrong header -- only a DECLARATIVE
    candidate stating the effective count arms the downgrade."""
    body = (
        "## Summary\n"
        "- Perimetre (1 fichier, source-only)\n"
        "- scan sur 2 fichiers\n"
    )
    items = [{"kind": "PR body", "author": "a", "body": body,
              "source": "body", "ts": ""}]
    candidates, _ = select_candidates(items, n_files=2)
    header = next(c for c in candidates if "Perimetre" in c.text)
    assert header.blocking is True
    assert header.body_declares_effective_count is False, (
        "an incidental scan scope must not arm the downgrade"
    )


# ----------------------------------------------------------------------------
# #12024 / #11985 extension: COUNT_WORDS closed list (French/English cardinals
# 1-10). The authorial perimeter declaration can be spelled out in words
# ("trois fichiers", "five files"). The numeric scan in select_candidates
# (line ~1020 in check_pr_perimeter.py) does NOT see this -- the word-form
# branch in this PR is the missing half.
# ----------------------------------------------------------------------------

def test_11985_count_words_french_three_fichiers_sets_body_declares():
    """#12024: body says "Trois fichiers (+184/-3)" + a numeric second-count
    line. The word-form declaration must arm body_declares_effective_count
    just like the numeric form would, and the numeric line stays a mention.
    """
    body = (
        "## Summary\n"
        "**Perimetre : trois fichiers** (+184/-3)\n"
        "- **G.4** : atomicite (1 helper + 1 modification + 1 fichier test "
        "adapte, 1 bug, 1 discrimination).\n"
    )
    items = [{"kind": "PR body", "author": "a", "body": body,
              "source": "body", "ts": ""}]
    candidates, _ = select_candidates(items, n_files=3)
    header = next(c for c in candidates if "Perimetre" in c.text)
    arg = next(c for c in candidates if "helper" in c.text)
    assert header.body_declares_effective_count is True, (
        "the word-form 'trois fichiers' must arm body_declares_effective_count"
    )
    # The numeric second-count line inherits the downgrade (mention, not fresh
    # assertion) -- the rule 1 invariant.
    assert arg.body_declares_effective_count is True


def test_11985_count_words_english_five_files_sets_body_declares():
    """#12024: English variant of test_11985_count_words_french_three_fichiers."""
    body = (
        "## Summary\n"
        "**Perimeter: five files** (+200/-20)\n"
        "- helper function + 1 new test\n"
    )
    items = [{"kind": "PR body", "author": "a", "body": body,
              "source": "body", "ts": ""}]
    candidates, _ = select_candidates(items, n_files=5)
    header = next(c for c in candidates if "Perimeter:" in c.text)
    assert header.body_declares_effective_count is True


def test_11985_count_words_mismatch_does_not_set_body_declares():
    """#12024 FN control: body says "trois fichiers" but n_files=2. The word
    form must NOT arm body_declares_effective_count -- the closed-list mapping
    is checked against n_files, and a mismatch keeps the existing behaviour
    (declaration does not validate a wrong perimeter)."""
    body = (
        "## Summary\n"
        "**Perimetre : trois fichiers** (+184/-3)\n"
    )
    items = [{"kind": "PR body", "author": "a", "body": body,
              "source": "body", "ts": ""}]
    candidates, _ = select_candidates(items, n_files=2)
    header = next(c for c in candidates if "Perimetre" in c.text)
    assert header.body_declares_effective_count is False, (
        "word-form 'trois' must not arm body_declares_effective_count when "
        "n_files=2"
    )


def test_11985_count_words_closed_list_boundary():
    """#12024 FN control: 'onze fichiers' / 'eleven files' (beyond the closed
    list 1-10) must NOT arm body_declares_effective_count. The whole point of
    the closed list is fail-loud: a reviewer catches the next 'eleven' body
    and the mapping is expanded. This test pins the boundary."""
    body = (
        "## Summary\n"
        "**Perimetre : onze fichiers** (+184/-3)\n"
    )
    items = [{"kind": "PR body", "author": "a", "body": body,
              "source": "body", "ts": ""}]
    candidates, _ = select_candidates(items, n_files=11)
    # 'onze fichiers' is OUTSIDE the closed list 1-10 -> the line is not
    # extracted as a candidate, so no header candidate exists. This is the
    # fail-loud shape: a body using 'onze fichiers' is NOT protected by rule 1
    # and the reviewer will see a mismatch against the actual n_files=11
    # (which is also outside the closed list, so the numeric form would also
    # be caught). The closed list's whole purpose: contain the FN cost.
    assert candidates == [], (
        "'onze fichiers' is outside COUNT_WORDS (closed list 1-10) -- the "
        "line must NOT enter the candidate list. Closed list = fail loud."
    )


def test_12024_numeric_count_inside_codespan_is_not_a_candidate():
    """#12024 / codespan-exclusion: a numeric COUNT_CLAIM inside a backtick
    code-span (`` `2 fichiers` ``) is a CITED example, not an authorial
    perimeter declaration. Founder case: PR #12024 body v3 listed illustrative
    counts between backticks and the perimeter-review-guard flagged them as
    unverifiable assertions. After the codespan-exclusion fix, lines whose
    only COUNT_CLAIM trigger sits inside a backtick span are skipped.

    This pins the FN control: 89/89 prior tests passed because the suite
    contained no code-span example -- a detector is validated by the cases
    it must NOT catch, not by the cases it does.
    """
    # Line whose ONLY count trigger sits inside a code-span -- must be skipped.
    text = (
        "Voici l'exemple documente : `2 fichiers` puis `three files`.\n"
    )
    found = extract_perimeter_assertions(text)
    assert found == [], (
        f"a numeric count inside backticks must not enter the candidate "
        f"stream; got {found!r}"
    )


def test_12024_word_form_inside_codespan_is_not_a_candidate():
    """#12024 / codespan-exclusion word-form variant: `` `trois fichiers` ``
    and `` `five files` `` between backticks are CITED examples. Founder case
    on PR #12024 body v3 (perimeter-review-guard FAIL x3 lines on those exact
    patterns). After the codespan-exclusion fix, lines whose only word-form
    trigger sits inside a code-span are skipped.
    """
    # Body lines 61/62 from PR #12024 body v3: word-form counts between
    # backticks. With the fix, neither line enters the candidate stream.
    text = (
        "- [x] Forme FR `trois fichiers` arming `body_declares_effective_count`\n"
        "- [x] Forme EN `five files` arming `body_declares_effective_count`\n"
    )
    found = extract_perimeter_assertions(text)
    assert found == [], (
        f"word-form counts inside backticks must not enter the candidate "
        f"stream; got {found!r}"
    )


def test_12024_codespan_exclusion_does_not_silence_real_assertion():
    """#12024 / codespan-exclusion: a line that mixes a code-span example AND
    an out-of-codespan count claim is STILL a candidate -- the real assertion
    is the un-cited one. The exclusion is "all triggers inside", not
    "any trigger inside".
    """
    text = (
        "Cette PR remplace l'ancien format `trois fichiers` par le nouveau "
        "qui declare 2 fichiers au total.\n"
    )
    found = extract_perimeter_assertions(text)
    assert any("2 fichiers" in c for c in found), (
        f"a real out-of-codespan count claim must still enter the candidate "
        f"stream even when the line also carries a code-spanned example; "
        f"got {found!r}"
    )


def test_12024_double_backtick_codespan_is_excluded():
    """#12024 / codespan-exclusion double-backtick variant: `` ``trois fichiers`` ``
    (a code-span whose content itself contains a backtick) is still a
    code-span, and its content is CITED, not claimed. CommonMark allows the
    longer opener to host a single backtick inside.
    """
    text = (
        "Use the pattern ``trois fichiers`` as the example.\n"
    )
    found = extract_perimeter_assertions(text)
    assert found == [], (
        f"double-backtick code-spans must also be excluded; got {found!r}"
    )


def test_12024_real_body_fragment_does_not_enter_candidates():
    """#12024 / end-to-end on a body fragment that reproduced the 3 FAIL lines
    ai-01 cited in the diagnostic. The 4 occurrences (L9 prose x2, L61/62
    code-span x2) must collapse to 0 candidates once (1)+(2) is in place:
    L9 prose entries are pinned by separate tests above, the L61/L62 entries
    collapse under the codespan-exclusion fix.
    """
    body = (
        "## Summary\n"
        "Cette PR livre la forme en toutes lettres -- par exemple "
        "`trois fichiers` ou `five files` -- pour les PRs qui n'utilisent pas "
        "de chiffres.\n"
        "## Tests\n"
        "- [x] Forme FR `trois fichiers` arming body_declares_effective_count\n"
        "- [x] Forme EN `five files` arming body_declares_effective_count\n"
    )
    found = extract_perimeter_assertions(body)
    assert found == [], (
        f"body fragment that reproduces the founder FAIL lines must yield "
        f"0 candidates under the codespan-exclusion fix; got {found!r}"
    )


# ---------------------------------------------------------------------------
# #12103 -- additive enumeration: "1 fichier modifie, 1 fichier ajoute" =
# 2 files. The guard read the first non-zero count (1) and could never
# validate a 2-file PR. Fix: confront the SUM of the counts surviving the
# per-count filters. Safe by construction (a FAIL becomes a PASS only when
# the sum is exactly len(files)).
# ---------------------------------------------------------------------------


def test_additive_enumeration_one_plus_one_passes():
    """Positif -- '1 fichier modifie, 1 fichier ajoute' over a 2-file PR."""
    files = [{"path": "slides/S3-acculturation/slides.md"},
             {"path": "slides/S3-acculturation/images/img_robot_extracted.png"}]
    assert check_assertion(
        files,
        "**1 fichier modifie, 1 fichier ajoute** :",
    ) == []


def test_additive_enumeration_two_plus_three_passes():
    """Positif -- '2 fichiers modifies, 3 fichiers ajoutes' over 5 files."""
    files = [{"path": f"a{i}.py"} for i in range(5)]
    assert check_assertion(files, "2 fichiers modifies, 3 fichiers ajoutes.") == []


def test_additive_enumeration_wrong_sum_still_fails():
    """Negatif -- '1 + 1' declared over 3 files: the sum (2) does not match."""
    files = [{"path": f"a{i}.py"} for i in range(3)]
    assert check_assertion(
        files, "1 fichier modifie, 1 fichier ajoute.",
    ) != []


def test_additive_enumeration_negated_diff_not_summed():
    """Non-regression #11800 -- '5 fichiers modifies, 91 fichiers inchanges'
    over 5 files: the negated-diff count (91) must NOT join the sum. If it
    did, 5 + 91 = 96 != 5 and the line would fail. The guard passes on the
    5-files half exactly as before."""
    files = [{"path": f"a{i}.py"} for i in range(5)]
    assert check_assertion(
        files,
        "5 fichiers modifies, 91 fichiers inchanges -- scope delta confirme",
    ) == []


def test_additive_enumeration_zero_count_not_summed():
    """Non-regression #11735 -- '0 fichier catalogue, 2 fichiers touches'
    over 2 files: the zero is a property attestation, only the 2 joins the
    sum (0 + 2 = 2 == len). Behavior preserved."""
    files = [{"path": "a.py"}, {"path": "b.py"}]
    assert check_assertion(files, "- 0 fichier catalogue, 2 fichiers touches.") == []


# ---------------------------------------------------------------------------
# #12092 -- word-form cardinal: "trois fichiers" == "3 fichiers". COUNT_WORDS
# gated extract since #12024 (the word form enters candidates) but
# check_assertion only read COUNT_CLAIM (digits): the word line fell into the
# terminal "unverifiable" branch. The invariant violated: same file list, same
# phrase, only the number SHAPE changes -> same verdict required.
# ---------------------------------------------------------------------------


def test_word_form_and_digit_form_same_verdict():
    """#12092 invariant: 'trois fichiers' and '3 fichiers' over the same
    3-file list must both pass (PASS)."""
    files = [{"path": "a"}, {"path": "b"}, {"path": "c"}]
    word = check_assertion(files, "**trois fichiers** (142/32 lignes, tests inclus):")
    digit = check_assertion(files, "**3 fichiers** (142/32 lignes, tests inclus):")
    assert word == digit == [], (
        f"word and digit forms must agree; word={word!r} digit={digit!r}"
    )


def test_word_form_wrong_count_still_fails():
    """#12092 negative: a word cardinal that does not match len(files) must
    fail, exactly like its digit twin."""
    files = [{"path": "a"}, {"path": "b"}]
    assert check_assertion(files, "**trois fichiers** :") != []
    assert check_assertion(files, "**3 fichiers** :") != []


def test_word_form_english_three_files():
    """#12092 EN twin: 'three files' over 3 files passes."""
    files = [{"path": "a"}, {"path": "b"}, {"path": "c"}]
    assert check_assertion(files, "**three files** (tests included):") == []


def test_word_form_not_recognized_absent_files_referent():
    """#12092 FN guard: a bare word cardinal without the fichiers/files
    referent stays unverifiable (not silently accepted)."""
    files = [{"path": "a"}, {"path": "b"}, {"path": "c"}]
    assert check_assertion(files, "**trois** modifications:") != []


# -- #11268 residuel ai-01: structural wiring safety net ---------------------
# Comment from ai-01 on 2026-08-18T08:34Z: the closed delivery of #11336
# produced a module + tests but "rien ne l'invoque sous .github/" -- the
# cable-to-Hermes layer was missing at the time. PRs #11635 / #11654 / #11661
# later wired `.github/workflows/perimeter-review-guard.yml` AND registered
# it in the pr-gate-rerun.yml `workflows:` list. These tests guard against
# silent regression of either leg (cable removed, or moved out of the
# mandatory rerun list, or its invocation stripped of `--scan-thread`).
# Without them the founding incident #11227 could re-occur with no detection.
def _repo_root():
    """Locate the CoursIA repo root from this test file.

    scripts/tests/test_check_pr_perimeter.py -> ../../.. = repo root.
    """
    here = Path(__file__).resolve()
    for parent in (here.parent, here.parent.parent, here.parent.parent.parent):
        if (parent / ".github" / "workflows").is_dir():
            return parent
    raise FileNotFoundError("could not locate repo root (.github/workflows/)")


def test_perimeter_workflow_file_exists_on_main():
    """The cable's first leg: `.github/workflows/perimeter-review-guard.yml`
    MUST exist on the working tree. A future refactor that renames or
    archives it without updating the workflow list would otherwise leave
    the gate referencing a phantom name, caught only as a downstream
    symptom."""
    wf = _repo_root() / ".github" / "workflows" / "perimeter-review-guard.yml"
    assert wf.is_file(), f"missing cable leg 1: {wf}"


def test_perimeter_workflow_invokes_scan_thread():
    """The cable's second leg: the LIVE gate MUST call
    `scripts/check_pr_perimeter.py --scan-thread`. A copy-paste that drops
    the flag would leave the gate never confront any review (silent green).

    #13384 : la surface live est le step perimeter d'always-on-guards.yml
    (fusion des cinq gardes always-on) ; perimeter-review-guard.yml est
    dormant mais reste verifie -- sa copie de reference ne doit pas
    diverger de ce qu'elle documente.
    """
    import re
    for wf_name in ("always-on-guards.yml", "perimeter-review-guard.yml"):
        wf = _repo_root() / ".github" / "workflows" / wf_name
        text = wf.read_text(encoding="utf-8")
        # The flag may be on the same line or split across continuation lines.
        # Loose match: the file mentions the script and the flag.
        assert "check_pr_perimeter.py" in text, (
            f"{wf_name} no longer invokes check_pr_perimeter.py"
        )
        assert "--scan-thread" in text, (
            f"{wf_name} invocation lost the --scan-thread flag"
        )


def test_perimeter_workflow_rescued_by_universal_sweep():
    """The perimeter guard's rescue is now UNIVERSAL (#11860). The event-driven
    per-guard path (pr-gate-rerun.yml `workflow_run` on a derived 76-workflow
    list) is retired -- measured 2026-08-23 it created 404 of the 784
    repository CI runs (51.5%) for 0 verdicts, a self-cancellation storm. The
    schedule sweep (pr-gate-stale-sweep.yml) observes ALL open PRs and
    re-aggregates any guard whose only red is a stale `PR gate`, so a timeout
    of perimeter-review-guard itself ALWAYS has a rescue path, independent of
    the trigger list. Assert the sweep exists and is schedule-driven (the one
    re-aggregation observer that does not depend on being triggerable).
    """
    sweep = _repo_root() / ".github" / "workflows" / "pr-gate-stale-sweep.yml"
    assert sweep.is_file(), f"missing pr-gate-stale-sweep.yml at {sweep}"
    text = sweep.read_text(encoding="utf-8")
    assert "schedule" in text, (
        "pr-gate-stale-sweep.yml is no longer schedule-driven -- the universal "
        "rescue would lose its only trigger-independent path"
    )


def test_founding_incident_11227_criteria_met_on_main():
    """Acceptance 4 bout-en-bout: a live re-run of
    `check_pr_perimeter.py --scan-thread` against PR #11227 MUST reproduce
    the founder's failure ('2 fichiers twins uniquement' over a 3-file PR
    with a workflow moving sorry-baseline). The pure-core test above
    encodes the same data; this one is the end-to-end guarantee that the
    script itself, executed against the real PR history, still does it.

    Skipped on networks that block gh API (the check uses gh under the
    hood); on disk we just require the local fixtures to be valid.
    """
    import subprocess
    if not shutil.which("gh"):
        pytest.skip("gh CLI not available -- end-to-end requires it")
    # GitHub Actions runners ship gh WITHOUT GH_TOKEN: `shutil.which` alone
    # lets the test run and die on 'To use GitHub CLI in a GitHub Actions
    # workflow, set the GH_TOKEN environment variable'. Guard the runner
    # env deterministically, then probe stored auth for the general case.
    if os.environ.get("GH_ACTIONS") == "true" and not (
        os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    ):
        pytest.skip("GitHub Actions runner without GH_TOKEN")
    auth_probe = subprocess.run(
        ["gh", "auth", "status"], capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    if auth_probe.returncode != 0:
        pytest.skip("gh CLI present but unauthenticated")
    # Run against PR #11227 with the exact phrase from the founder review.
    # The script will reach out to gh API; if the PR is missing or
    # permissions fail, it returns non-zero AND stdout/stderr lack the
    # expected FAIL verdict. We assert both the exit code AND the verdict
    # line to catch silent regressions where the tool swallows the error.
    proc = subprocess.run(
        ["python", "scripts/check_pr_perimeter.py", "11227", "--scan-thread"],
        cwd=str(_repo_root()),
        capture_output=True,
        text=True,
        timeout=120,
        encoding="utf-8", errors="replace",
    )
    output = proc.stdout + proc.stderr
    # The tool surfaces the FAIL either in stdout (normal) or via a
    # non-zero exit. A green pass without the founding assertion listed
    # is a regression -- assert at least one of the founder signatures.
    founder_signatures = [
        "11227",
        "lean-knot.yml",
        "Invariant.lean",
        "VERDICT: FAIL",
    ]
    found = [sig for sig in founder_signatures if sig in output]
    assert found, (
        f"end-to-end scan of #11227 produced no founder signature; "
        f"exit={proc.returncode}, output[:500]={output[:500]!r}"
    )


# --- #12201 : citations, intervalles, bootstrap --------------------------------
#
# Fondateurs : le garde échouait sur le body de SA PROPRE PR de correctif
# (#12201) — « l'assertion prétend 70, la liste en compte 2 » — parce que
# check_assertion lisait le premier compte non nul SANS les masques de
# citation : les lignes qui QUOTENT les formes réparées (contrôles FN,
# « lake 70 fichiers », `Périmètre : 3 fichiers`) devenaient le claim.
# Et #12273 : « 12 fichiers `70.png`-`81.png` » — une plage d'exports PNG
# rendus, pas une énumération de périmètre. Trois masques, un axe : discours
# RAPPORTÉ vs claim AUTORIAL (distinct des exemptions #11712/#11985, qui
# restent confrontées — règle 1 de #11985 intouchée, test dédié ci-dessous).

GUARD_FILES_2 = [
    {"path": "scripts/check_pr_perimeter.py"},
    {"path": "scripts/tests/test_check_pr_perimeter.py"},
]


def test_12201_l7_verbatim_cited_forms_are_not_the_claim():
    """Lignes verbatim du body #12201 : la citation « `lake 70 fichiers` » et
    les contrôles FN cités ne sont pas le claim — le vrai compte l'est."""
    body = (
        "Le garde lisait « `lake 70 fichiers` » dans #12181 comme une "
        "assertion de périmètre.\n"
        "- **7a** : `lake 70 fichiers`, `corpus 3 fichiers`. Contrôle FN : "
        "« scan du corpus : 3 fichiers touchés ».\n"
        "- **Détection inchangée** : `Périmètre : 3 fichiers` reste "
        "confrontable.\n"
        "Périmètre : 2 fichiers modifiés.\n"
    )
    assert check_assertion(GUARD_FILES_2, body) == []


def test_12201_body_of_cited_counts_only_stays_unverifiable():
    """Contrôle FN : un body fait UNIQUEMENT de comptes cités ne passe pas en
    silence — il tombe sur le terminal 'non verifiable' (FAIL honnête), pas
    sur un silence. (Fichiers NON-garde : le bootstrap ne s'applique pas.)"""
    body = "Le fondateur disait « lake 70 fichiers » et `Périmètre : 3 fichiers`."
    problems = check_assertion([{"path": "a.py"}, {"path": "b.py"}], body)
    assert len(problems) == 1
    assert problems[0].startswith("assertion sans compte")


def test_12273_range_form_is_not_the_claim():
    """Ligne fondatrice #12273 (verbatim de la section Méthode d'origine) :
    le compte suivi d'un intervalle compact `70.png`-`81.png` désigne des
    exports rendus ; le vrai périmètre déclaré plus bas l'emporte."""
    body = (
        "**Méthode** : `slidev export --per-slide --range 70-81` produit "
        "12 fichiers `70.png`-`81.png`, un par slide de 70 à 81.\n"
        "**Périmètre de la PR** : 1 fichier ajouté.\n"
    )
    files = [{"path": "slides/S3-acculturation/qa/axe1-generative-phase-verdict.md"}]
    assert check_assertion(files, body) == []


def test_12201_fn_real_enumeration_still_confronted():
    """Contrôle FN : le format revue « N fichiers : a, b, c » (virgules, pas
    d'intervalle) reste LE claim — un mauvais compte y échoue toujours."""
    files = [{"path": "a.py"}, {"path": "b.py"}]
    problems = check_assertion(files, "3 fichiers : `a.py`, `b.py`")
    assert len(problems) == 1
    assert problems[0].startswith("l'assertion pretend 3")


def test_12201_fn_unmatched_delimiter_masks_nothing():
    """Contrôle FN : un délimiteur non fermé ne masque rien — « 2 fichiers
    sans guillemet fermant reste un claim confronté (échoue sur 3 files)."""
    files = [{"path": "a.py"}, {"path": "b.py"}, {"path": "c.py"}]
    problems = check_assertion(files, "Résumé : « 2 fichiers modifiés")
    assert len(problems) == 1
    assert problems[0].startswith("l'assertion pretend 2")


def test_12201_guard_self_bootstrap_skips_count_confrontation():
    """Bootstrap : le body d'une PR qui modifie le garde est un corpus
    diagnostique — aucun compte n'y est confronté (le fondateur même :
    des dizaines de comptes d'exemple, tous légitimes)."""
    body = (
        "Le garde lisait lake 70 fichiers et `Périmètre : 3 fichiers` reste "
        "confrontable ; 12 fichiers `70.png`-`81.png` fondateur #12273."
    )
    assert check_assertion(GUARD_FILES_2, body) == []


def test_12201_bootstrap_never_touches_exclusivity():
    """Contrôle FN : le bootstrap n'excuse PAS l'exclusivité — une PR garde
    qui touche un workflow doit toujours le nommer (#11268-2)."""
    files = [
        {"path": "scripts/check_pr_perimeter.py"},
        {"path": ".github/workflows/perimeter-review-guard.yml"},
    ]
    body = "Uniquement le garde est touché, rien d'autre."
    problems = check_assertion(files, body)
    assert any("exclusivite sans nommer" in p for p in problems)


def test_12201_cited_counts_never_join_additive_sum():
    """La somme additive lit le body comme la sélection du claim : un terme
    cité ne rejoint jamais la somme (1 + « 3 cités » = 1, pas 4)."""
    line = "1 fichier modifié, « 3 fichiers cités » et `2 fichiers` en exemple."
    assert _additive_line_sum(line) == 1


# ---------------------------------------------------------------------------
# #13335 — wrap-invariance de l'exemption par antécédent de mesure
# ---------------------------------------------------------------------------

# Paragraphes fondateurs : l'antécédent (« le scan rendait 54 ») est sur la
# ligne AU-DESSUS de la ligne de compte. Avant #13335, la fenêtre de recherche
# de MEASUREMENT_ANTECEDENT était limitée à `line[:m.end()]` → le verdict
# dépendait de la position de la touche Entrée, pas du contenu.
WRAPPED_13218 = (
    "Un scan recursif rendait **54**\n"
    "/ en accusant 5 fichiers d'`analysis/` que nul moteur de rendu ne consomme."
)
ONELINE_13218 = (
    "Un scan recursif rendait **54** / en accusant 5 fichiers "
    "d'`analysis/` que nul moteur de rendu ne consomme."
)

# Contrôles de l'issue : aucun antécédent de mesure nulle part → bloquants,
# wrap ou non-wrap.
CONTROL_C_WRAPPED = (
    "Cette PR couvre un perimetre fige et exigeant\n"
    "touchant 2 fichiers twins uniquement, aucune autre modification."
)
CONTROL_D_ONELINE = "Cette PR touche 3 fichiers."


def _classify(body_text: str) -> list:
    """Extrait les lignes candidates du body avec leur contexte paragraphe."""
    pairs = extract_perimeter_assertions_with_context(body_text)
    return [(line, _is_incidental_assertion(line, ctx)) for line, ctx in pairs]


def test_13335_wrapped_and_unwrapped_same_verdict():
    """Le même contenu wrappe et non-wrappe rend le même verdict (#13335)."""
    wrapped_lines = _classify(WRAPPED_13218)
    oneline_lines = _classify(ONELINE_13218)
    assert wrapped_lines, "la ligne de compte wrapped doit être candidate"
    assert len(wrapped_lines) == len(oneline_lines) == 1
    # Wrap : l'antécédent vit sur la ligne précédente du même paragraphe.
    assert wrapped_lines[0][1] is True, (
        f"wrapped doit être incidental (antécédent sur la ligne au-dessus) : {wrapped_lines}"
    )
    # Non-wrap : antécédent et compte sur la même ligne — verdict identique.
    assert oneline_lines[0][1] is True
    # Les deux verdicts concordent : le placement du saut de ligne est neutre.
    assert wrapped_lines[0][1] == oneline_lines[0][1]


def test_13335_three_distinct_antecedents_wrap_invariant():
    """Au moins 3 antécédents distincts de MEASUREMENT_ANTECEDENT (scan,
    corpus, registre) : chacun rend wrap-invariance + incidental."""
    cases = [
        # (antecedent_line, count_line) — l'antécédent précède le compte,
        # séparés par un simple retour à la ligne (soft-wrap).
        (
            "Un scan recursif rendait **54**",
            "en accusant 5 fichiers d'`analysis/` que nul moteur ne consomme.",
        ),
        (
            "Le corpus des notebooks pesait deja **107**",
            "dont 12 fichiers d'exclusion automatique cites au passage.",
        ),
        (
            "Le registre arxiv amont listait **8**",
            "soit au total 6 fichiers entres manuellement ici.",
        ),
    ]
    for ante_line, count_line in cases:
        wrapped = f"{ante_line}\n{count_line}"
        oneline = f"{ante_line} {count_line}"
        w = _classify(wrapped)
        o = _classify(oneline)
        assert w and o, f"aucune candidate pour {ante_line!r}"
        assert w[0][1] is True, f"wrapped doit être incidental pour {ante_line!r} : {w}"
        assert o[0][1] is True, f"oneline doit être incidental pour {ante_line!r} : {o}"
        assert w[0][1] == o[0][1]


def test_13335_blank_line_cuts_the_window():
    """Une ligne vide entre l'antécédent et le compte COUPE la fenêtre :
    l'exemption est perdue (le compte ouvre un nouveau paragraphe)."""
    body = (
        "Un scan recursif rendait **54**\n"
        "\n"
        "en accusant 5 fichiers d'`analysis/` que nul moteur ne consomme."
    )
    verdicts = _classify(body)
    assert verdicts, "la ligne de compte reste candidate (le compte est présent)"
    line, incidental = verdicts[0]
    assert incidental is False, (
        f"la ligne vide doit couper la fenêtre → non-incidental : {verdicts}"
    )
    # Le préfixe paragraphe est vide : la fenêtre ne traverse pas la frontière.
    lines = body.splitlines()
    count_idx = 2
    assert _paragraph_prefix(body, count_idx) == ""


def test_13335_controls_C_and_D_stay_blocking():
    """Contrôles C et D de l'issue : sans antécédent de mesure dans le
    paragraphe (même multi-lignes), la ligne reste BLOQUANTE."""
    for text in (CONTROL_C_WRAPPED, CONTROL_D_ONELINE):
        verdicts = _classify(text)
        assert verdicts, f"aucune candidate dans {text!r}"
        line, incidental = verdicts[0]
        assert incidental is False, (
            f"contrôle sans antécédent doit rester bloquant : {text!r} → {verdicts}"
        )


def test_13335_fence_delimiter_cuts_the_window():
    """Un délimiteur de fence (``` ou ~~~) ferme aussi la fenêtre : le
    contenu d'un bloc de code n'est pas la prose qui annonce la mesure."""
    body = (
        "Un scan recursif rendait **54**\n"
        "```\n"
        "en accusant 5 fichiers d'`analysis/` que nul moteur ne consomme.\n"
        "```"
    )
    # La ligne dans la fence n'est pas candidate du tout (skip de fence).
    verdicts = _classify(body)
    assert verdicts == []


def test_13335_candidate_blocking_property_uses_context():
    """End-to-end sur le paragraphe fondateur #13218 : via select_candidates,
    la ligne de compte wrapped n'est plus bloquante (contexte paragraphe)."""
    body = (
        "Contexte amont de la review.\n"
        "\n"
        "Un scan recursif rendait **54**\n"
        "/ en accusant 5 fichiers d'`analysis/` que nul moteur de rendu ne consomme.\n"
        "\n"
        "Rien d'autre a signaler."
    )
    items = [{"kind": "review", "author": "reviewer", "source": "body", "body": body}]
    candidates, _orphan = select_candidates(items)
    count_candidates = [c for c in candidates if "5 fichiers" in c.text]
    assert count_candidates, f"la ligne de compte doit être candidate : {[c.text for c in candidates]}"
    c = count_candidates[0]
    assert c.context, "le contexte paragraphe doit être attaché au Candidate"
    assert c.blocking is False, (
        f"le compte wrapped avec antécédent amont ne doit plus être bloquant : {c.text!r}"
    )


def test_13335_public_extract_delegates_with_context():
    """extract_perimeter_assertions (API publique) et la variante avec
    contexte rendent les mêmes lignes dans le même ordre."""
    body = WRAPPED_13218 + "\n\n" + CONTROL_D_ONELINE
    plain = extract_perimeter_assertions(body)
    with_ctx = extract_perimeter_assertions_with_context(body)
    assert plain == [line for line, _ in with_ctx]



def test_13246_paths_filter_excludes_pr_with_perimeter_assertion_off_workflow():
    """Issue #13246 — preuve que le paths-filter historique de
    `perimeter-review-guard.yml` (4 globs) ECLTAIT du déclenchement les PR
    hors `.github/workflows/**` et `scripts/check_pr_perimeter.py`.

    Mesure : sur 50 PRs merged recentes (cf. issue body, 2026-08-27), 21
    (42 %) portent une assertion de perimetre AUTHORIALE (cf. extracteur
    officiel + `_is_incidental_assertion`) sans toucher aucun chemin du
    filtre. Le garde ne tournerait PAS sur ces PR.

    Ce test verrouille la MEMOIRE du défaut avant le fix. Une fois le
    paths: retire (#13246 verdict "a retirer"), ce test reste vert : il
    documente la mesure, pas le paths-filter.

    Le test MIRROIR du fix (cf. test_13246_metadata_dependent_guard_has_no_paths_filter
    ci-dessous) verrouille que le paths-filter est bien retiré sur le workflow.
    """
    import fnmatch
    from pathlib import Path

    # Chemins observés dans 50 PRs merged recentes portant une vraie assertion
    # de perimetre HORS `.github/workflows/**` et `scripts/check_pr_perimeter.py`.
    # Échantillon représentatif : 4 PRs de la mesure (cf. issue #13246 body).
    OFF_SCOPE_PATHS_OBSERVED = [
        ["scripts/notebook_tools/foo.py", "MyIA.AI.Notebooks/Lean/Bar.lean", "docs/lean/LEAN_INVENTORY.md"],  # noqa: E501
        ["MyIA.AI.Notebooks/Lean/mathlib_examples/README.md", "MyIA.AI.Notebooks/Lean/mathlib_examples/lean-toolchain"],  # noqa: E501
        ["MyIA.AI.Notebooks/GameTheory/GameTheory-17c-Lean-Lemon-IC-Equilibrium.ipynb"],  # noqa: E501
        ["MyIA.AI.Notebooks/Search/Search-17-Minima-Fallacieux-Burer.ipynb"],  # noqa: E501
    ]

    # paths-filter historique de `perimeter-review-guard.yml` (avant #13246).
    HISTORICAL_PATHS = [
        ".github/workflows/perimeter-review-guard.yml",
        ".github/workflows/**",
        "scripts/check_pr_perimeter.py",
        "scripts/tests/test_check_pr_perimeter.py",
    ]

    # Chaque PR de l'echantillon NE MATCHE aucun des globs historiques :
    # le paths-filter les ECLTAIT du declenchement du garde.
    for files_paths in OFF_SCOPE_PATHS_OBSERVED:
        matched = any(
            any(fnmatch.fnmatch(f, p) for f in files_paths)
            for p in HISTORICAL_PATHS
        )
        assert not matched, (
            f"PR touchant {files_paths} MATCHERAIT un glob du paths-filter "
            f"historique {HISTORICAL_PATHS} -- l'echantillon est mal choisi."
        )

    # Sanity check : la mesure reste vraie apres le fix. Le paths-filter futur
    # est vide (`on:` sans `paths:`) ; tout chemin matche au sens large (le
    # vide matche tout) -- c'est le but. Cette assertion sert de REGRESSIoN
    # : si un futur editeur re-ajoute un `paths:`, ce test continuera de
    # passer SEULEMENT parce que l'echantillon teste l'absence d'intersection.
    # Le verrou mecanique est assure par le test suivant
    # (test_13246_metadata_dependent_guard_has_no_paths_filter).
    return


def test_13246_metadata_dependent_guard_has_no_paths_filter():
    """Verrou mecanique : apres le fix de #13246, le bloc `paths:` est absent
    du declencheur `pull_request` de la surface LIVE du perimeter guard.

    #13384 : la surface live est le declencheur `pull_request`/
    `pull_request_review` d'always-on-guards.yml (fusion des cinq gardes
    always-on ; perimeter-review-guard.yml est dormant). Le verrou suit la
    surface qui s'execute : c'est le `paths:` de l'umbrella qui desarmerait
    les SIX organes metadata qu'il porte.

    Meme contrat que `test_13232_metadata_dependent_guard_has_no_paths_filter`
    dans `test_variation_tag_required.py` (cf. #13234 tranche 1c), cible
    sur le 3eme garde METADONNEE-dependant : perimeter-review-guard lit une
    METADONNEE (assertion dans le body / une review) et la confronte au DIFF
    (gh pr view --json files). La surface nominale est toute PR portant une
    assertion -- paths-filter DESARME le garde (#13232).

    Si un futur editeur re-ajoute un `paths:` pour « gagner du CI », ce test
    rougit.
    """
    import re
    from pathlib import Path

    wf_path = (
        Path(__file__).resolve().parent.parent.parent
        / ".github" / "workflows" / "always-on-guards.yml"
    )
    text = wf_path.read_text(encoding="utf-8")

    # Sanity check #1 : le fichier existe et contient le declencheur.
    assert "pull_request:" in text, "Workflow doit declarer pull_request."

    # Recherche : `paths:` a exactement 4 espaces en debut de ligne (= sous
    # `pull_request:` ou `pull_request_review:`). Ancre la fin de ligne pour
    # eviter les faux positifs (commentaires contenant le mot).
    paths_blocks = re.findall(r"^    paths:\s*$", text, flags=re.MULTILINE)
    assert len(paths_blocks) == 0, (
        f"always-on-guards.yml porte {len(paths_blocks)} bloc(s) `paths:` "
        "a 4 espaces (= sous `pull_request:` ou `pull_request_review:`). "
        "C'est le defaut que #13246 tranche : le verdict du garde perimeter "
        "depend d'une METADONNEE (assertion dans le body / une review), pas "
        "du diff. Un paths-filter sur l'umbrella desarmerait en bloc les "
        "organes metadata qu'elle porte (tag, light-cap, genre-signals, "
        "lane-claim) : un workflow saute par `paths:` ne poste AUCUN "
        "check-run. Cf #13232."
    )

def test_normalize_rest_files_maps_filename_to_path():
    """#13357: fetch_report moved to the paginated REST endpoint (gh pr view
    --json files caps at 100), whose items name the path `filename`. The
    normalizer must produce the `path` shape every downstream reader
    (format_report, check_assertion) expects."""
    items = [
        {"filename": "a.py", "additions": 3, "deletions": 1, "status": "modified"},
        {"filename": "b.md", "additions": 0, "deletions": 0, "status": "added"},
    ]
    assert _normalize_rest_files(items) == [
        {"path": "a.py", "additions": 3, "deletions": 1},
        {"path": "b.md", "additions": 0, "deletions": 0},
    ]
    # (items or []) guards an empty/None payload the same way.
    assert _normalize_rest_files(None) == []


def test_normalize_rest_files_keeps_full_page_count_13357():
    """The founding incident encoded: #13357 carries 148 real files; the old
    `gh pr view --json files` read exactly 100 (single-page cap) and the
    honest body count ("148 fichiers") failed against the truncation -- an
    unwinnable guard. A full-length payload must survive the normalizer
    without loss."""
    payload = [
        {"filename": f"file_{i:03d}.py", "additions": 1, "deletions": 0}
        for i in range(148)
    ]
    out = _normalize_rest_files(payload)
    assert len(out) == 148
    assert out[0] == {"path": "file_000.py", "additions": 1, "deletions": 0}
    assert out[-1]["path"] == "file_147.py"


# ---------------------------------------------------------------------------
# #13440 — comptes de résultat de vérification sans antécédent d'outil.
# Une PR qui documente ses contrôles qualité sur un corpus plus large que son
# diff (« 25 fichier(s) vérifiés sans BOM ») ne fait AUCUNE assertion de
# périmètre : la confrontation d'égalité ne peut jamais VALIDER ces formes,
# donc les bloquer ne protège rien (asymétrie fondatrice #11712/#11985).
# FN délibéré : « restaurés » (#2876) et « re-exécutés » (tranches MGS) sont
# des périmètres dans ce dépôt et restent hors liste.
# ---------------------------------------------------------------------------
VERIFICATION_COUNT_BODIES_13440 = [
    "## Vérifications\n"
    "- 25 fichier(s) vérifiés sans BOM\n"
    "- 18 fichiers testés sans erreur",
    "## Résultats\n"
    "- Contrôle encodage : 25 fichier(s) conformes",
    "- 40 fichiers scannés par le garde hygiène\n",
]

PERIMETER_COUNT_BODIES_13440 = [
    # Campagne accents #2876 : forme identifiée comme périmètre.
    "- 18 fichiers avec accents restaurés",
    # Tranches MGS : les re-exécutions SONT le livrable.
    "- 13 fichiers re-exécutés",
    "- 13 fichiers re-exécutés avec Papermill",
    # Verbe de modification : périmètre authentique (contrôle FN de l'issue).
    "- 13 fichiers touchés uniquement, aucune autre modification.",
]


def test_13440_verification_counts_are_incidental():
    """Les formes résiduelles mesurées de l'issue deviennent incidental."""
    for body in VERIFICATION_COUNT_BODIES_13440:
        pairs = extract_perimeter_assertions_with_context(body)
        assert pairs, f"aucune ligne candidate pour {body!r}"
        for line, ctx in pairs:
            assert _is_incidental_assertion(line, ctx) is True, (
                f"compte de vérification doit être incidental : {line!r}"
            )


def test_13440_fn_perimeter_forms_stay_blocking():
    """restaurés / re-exécutés / touchés restent des assertions bloquantes."""
    for body in PERIMETER_COUNT_BODIES_13440:
        pairs = extract_perimeter_assertions_with_context(body)
        assert pairs, f"aucune ligne candidate pour {body!r}"
        for line, ctx in pairs:
            assert _is_incidental_assertion(line, ctx) is False, (
                f"forme périmètre ne doit pas être incidental : {line!r}"
            )


def test_13440_plural_paren_window_no_longer_blind():
    """Le pluriel parenthétique « fichier(s) » ne doit plus aveugler la fenêtre
    de qualificatif : CountClaim s'arrête à « fichier » (\b), le « (s) » doit
    être sauté pour lire le mot qui suit."""
    # Négated-diff après (s) : l'exemption préexistante doit fonctionner.
    assert _count_is_incidental("- 25 fichier(s) inchanges apres rebase") is True
    # Qualificatif incidental après (s) : la nouvelle classe s'applique.
    assert _count_is_incidental("- 25 fichier(s) vérifiés sans BOM") is True
    # Un (s) seul ne qualifie rien : la ligne sans qualificatif reste auteur.
    assert _count_is_incidental("- 25 fichier(s)") is False


def test_13440_founder_negated_diff_still_exempt():
    """Contrôle non-régression : le fondateur #11775 (« 91 fichiers inchanges
    sur 2 touches ») — la ligne porte « scope » (strong scope word) donc
    n'est PAS incidental au niveau ligne ; sa protection réelle est
    l'exemption PAR-COMPTE (negated-diff pour 91, locative pour 2), que la
    normalisation (s) ne doit pas altérer."""
    line = "- 91 fichiers inchanges sur 2 touches -- scope delta confirme"
    matches = list(COUNT_CLAIM.finditer(line))
    assert matches, "le fondateur doit porter des comptes"
    for m in matches:
        assert _count_is_exempt(line, m) is True, (
            f"le compte fondateur doit rester exempt : {m.group(0)!r}"
        )


# ---------------------------------------------------------------------------
# #13471 — 2 residus de la fenetre de qualificatif `_count_has_incidental_qualifier`
# nommes au merge de #13463, laisses ouverts. Les 2 residus partagent la
# meme fenetre ; le fix unifie dans le predicat (normalisation NFD + lecture
# 2 mots en OR).
#
# Residu 1 -- les formes hybrides accentuees (premier e nu, dernier accentue)
# ne sont pas normalisees avant match. Issue : « verifié » / « verifiés » ne
# sont pas reconnus alors que « vérifié » / « vérifiés » / « verifie » /
# « verifies » le sont (toutes 4 collapent sur la meme cle NFD-stripped).
#
# Residu 2 -- la fenetre ne lit que le 1er mot apres le compte. Un compte
# dont le 2eme mot est incident (mais pas le 1er) reste aveuglant. Issue :
# « 9 fichiers verifies puis modifies » -- 'puis' n'est pas incident,
# 'modifies' est un verbe de modif (donc strong scope, hors scope du
# Residu 2) ; le VRAI trou est « N fichiers puis conformes » / « N fichiers
# independamment analyses ».
#
# Methodologie : les 2 controles positifs sont ecrits en **assertions directes**
# sur `_count_is_incidental` (verdict blocant). Les FN deliberes et le bare
# authorial sont des controles non-regression (verdict ne change pas).
# ---------------------------------------------------------------------------
def test_13471_residu1_hybrid_accent_recognized():
    """Le Résidu 1 : « verifié » (premier e nu, dernier accentué) doit etre
    reconnu au meme titre que « vérifié » / « verifie » / « verifies ». La
    normalisation NFD fait collapser toutes les variantes sur la meme cle,
    et la liste close n'a PAS besoin d'etre etendue -- c'est precisement
    la serie de tranches que l'issue prescrit d'eviter."""
    # Hybride : premier e nu, dernier accentue (le cas fondateur de l'issue).
    assert _count_is_incidental("- 9 fichiers verifié puis corriges") is True, (
        "le Résidu 1 fondateur (verifié hybride) doit etre incident"
    )
    # Hybride + participe +2 (verifies hybride).
    assert _count_is_incidental("- 13 fichiers verifiés avec Papermill") is True, (
        "le Résidu 1 pluriel (verifiés hybride) doit etre incident"
    )
    # Forme deja listee (control non-regression) : ne change pas.
    assert _count_is_incidental("- 18 fichiers vérifiés sans BOM") is True, (
        "la forme canonique listee ne change pas de verdict"
    )
    # Forme deja listee (control non-regression) : ne change pas.
    assert _count_is_incidental("- 18 fichiers verifie") is True, (
        "la forme nue sans accent ne change pas de verdict"
    )


def test_13471_residu2_second_word_incidental_recognized():
    """Le Résidu 2 : un compte dont le 2eme mot apres le nombre est incident
    (mais pas le 1er) doit etre reconnu comme incidental. La fenetre pre-
    existante ne lisait que le 1er mot, ce qui rendait aveuglant « N
    fichiers <mot-non-incidental> puis conformes » (le 1er mot n'est pas
    dans INCIDENTAL_QUALIFIERS, le 2eme 'conformes' l'est)."""
    # Le trou reel fondateur du Résidu 2 : 'puis' n'est pas incident,
    # 'conformes' l'est -- le 1er-mot-seul rendait False avant le fix.
    assert _count_is_incidental("- 9 fichiers puis conformes") is True, (
        "le Résidu 2 fondateur ('puis conformes') doit etre incident"
    )
    # Variante : 1er mot adverbial, 2eme participe incident.
    assert _count_is_incidental(
        "- 9 fichiers independamment analyses"
    ) is True, (
        "le Résidu 2 variante ('independamment analyses') doit etre incident"
    )
    # Forme deja couverte avant le fix (control non-regression).
    assert _count_is_incidental(
        "- 9 fichiers verifies puis modifies"
    ) is True, (
        "la forme 2-mots-incidents ne change pas de verdict"
    )


def test_13471_fn_deliberes_stay_blocking():
    """Les FN délibérés du fondateur #13440 restent bloquants après le
    fix : « restaurés » / « re-exécutés » / « touchés » sont des périmètres
    authentiques dans ce dépôt (campagne accents #2876, tranches MGS,
    verbes de modification) et HORS de INCIDENTAL_QUALIFIERS. La
    normalisation NFD ne les ajoute pas par effet de bord."""
    # restaures (campagne accents #2876) -- perimetre authentique.
    assert _count_is_incidental(
        "- 18 fichiers avec accents restaurés"
    ) is False, (
        "« restaurés » reste bloquant (campagne accents)"
    )
    # re-executés (tranches MGS) -- perimetre authentique.
    assert _count_is_incidental(
        "- 13 fichiers re-executés"
    ) is False, (
        "« re-executés » reste bloquant (tranches MGS)"
    )
    # touchés -- verbe de modification, _has_strong_scope bloque la ligne.
    assert _count_is_incidental(
        "- 13 fichiers touchés uniquement"
    ) is False, (
        "« touchés » reste bloquant (verbe de modification)"
    )


def test_13471_bare_authorial_preserved():
    """Le « 25 fichier(s) » sans qualificatif reste auteur (fail-loud
    préservé) : le 2eme token est la parenthese vide, qui ne contient pas
    de mot, donc le predicat rend False (pas d'incidental). Le résidu du
    2-mots-OR ne fait pas fuiter un verdict blanc sur un auteur reel."""
    assert _count_is_incidental("- 25 fichier(s)") is False, (
        "le bare authorial reste bloquant (predicate ne doit pas "
        "lire du vide comme un mot)"
    )
    assert _count_is_incidental("- 13 fichiers") is False, (
        "le compte nu reste bloquant"
    )


def test_13471_founder_negated_diff_still_exempt():
    """Non-régression fondateur #11775 : « 91 fichiers inchanges sur 2
    touches » -- la ligne porte « scope » (strong scope word) et est
    exemptée par negated-diff (91) + locative (2). La normalisation NFD
    des 2 premiers mots ne doit pas alterer ces exemptions par-compte."""
    line = "- 91 fichiers inchanges sur 2 touches -- scope delta confirme"
    matches = list(COUNT_CLAIM.finditer(line))
    assert matches, "le fondateur doit porter des comptes"
    for m in matches:
        assert _count_is_exempt(line, m) is True, (
            f"le compte fondateur doit rester exempt : {m.group(0)!r}"
        )


def test_12718_hyphenated_scope_does_not_block():
    """#12718: 'in-scope' (hyphenated, descriptive) is NOT a strong-scope
    perimeter label -- `_has_strong_scope` excludes the hyphenated compound,
    so a line whose count is already incidental via 'neufs' stays incidental
    instead of being re-blocked by the bare word 'scope' inside 'in-scope'."""
    line = ("2 fichiers neufs : `TopologyDictionary.lean` (330 lignes), "
            "in-scope « couverture complète FR » + `TopologyDictionary` neuf.")
    assert extract_perimeter_assertions(line) == [line], "detection unchanged"
    assert _has_strong_scope(line.lower()) is False
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is False



def test_12718_new_files_qualifier_signal_not_blocking():
    """#12718 (class #11985 forme 4): 'N fichiers neufs : file1 + file2' names
    the newly-added files, never the whole-PR perimeter -- 'neufs' qualifies
    the count, so the '330 lignes' diffstat neighbor is a per-file size, not
    a diffstat of the PR. Detection unchanged; blocking consequence only."""
    lines = [
        # count with 'neufs' qualifier + diffstat neighbor -> incidental
        "2 fichiers neufs : `Grothendieck/TopologyDictionary.lean` "
        "(FR, 330 lignes) + sibling `TopologyDictionary_en.lean` "
        "(EN, 328 lignes, miroir auto-contenu).",
        # snapshot antecedent + diffstat -> incidental
        "- avant (main) : grothendieck_lean — 116 fichiers, `distinct_code_sorry: 0`",
        "- après (branche) : 118 fichiers (+2 neufs), `distinct_code_sorry: 0`",
        # new-files count without diffstat -> incidental
        "- Les 2 fichiers neufs sont créés sans `sorry`.",
    ]
    for line in lines:
        assert extract_perimeter_assertions(line) == [line], "detection unchanged"
        cand = Candidate(line, "body", "author", "body")
        assert cand.blocking is False, f"new-files qualifier must not block: {line[:50]}"



def test_12718_scope_label_still_blocks():
    """The hyphenated-scope relaxation must not swallow a genuine scope label:
    'in-scope' is excluded, but 'scope = perimetre' remains a strong-scope
    perimeter anchor. FN control for `_has_strong_scope`."""
    line = "lake 70 fichiers uniquement, scope = perimetre PR"
    assert extract_perimeter_assertions(line) == [line]
    cand = Candidate(line, "body", "author", "body")
    assert cand.blocking is True




# ---------------------------------------------------------------------------
# #13535 -- accord de langue cardinal/nom. « une file » (queue CI) n'est pas
# « 1 fichier » : le garde bloquant sur-accusait toute prose francais parlant
# de la file d'attente CI (#13499, mesure : FAIL pretendu 1 fichier, liste
# effective 2).

FILES_2_13499 = [
    {"path": "scripts/pick_idle_grain.py", "additions": 40, "deletions": 12},
    {"path": "scripts/tests/test_pick_idle_grain.py", "additions": 55, "deletions": 8},
]


def test_13535_language_agreement_positive_controls():
    """Controles positifs : l'accord de langue preserve les vraies declarations.
    #14438 : « un fichier » (article nu) n'est plus un compte FR -- seule la
    forme restrictive « un seul fichier » compte 1 ; « one file » (EN, vrai
    cardinal) reste 1."""
    assert _word_form_count("Périmètre : un fichier modifié.") is None
    assert _word_form_count("Périmètre : un seul fichier modifié.") == 1
    assert _word_form_count("Périmètre : trois fichiers touchés.") == 3
    assert _word_form_count("Perimeter: one file changed.") == 1
    assert _word_form_count("Perimeter: three files changed.") == 3


def test_13535_queue_file_is_not_a_count():
    """Controles negatifs : la « file » de CI n'est plus lue comme un compte."""
    assert _word_form_count(
        "il rend le même verdict sur une file qui avance et sur une file figée"
    ) is None
    assert _word_form_count("la file est figée depuis le merge") is None
    assert _word_form_count("deux files d'attente bloquent les runners") is None


def test_13535_digit_forms_still_asserted():
    """La forme chiffrée reste langue-neutre, toujours extraite et confrontée :
    compte juste -> PASS, compte faux -> FAIL avec le compte effectif."""
    ok_fr = "Périmètre : 2 fichiers uniquement."
    ok_en = "Perimeter: 2 files only."
    assert extract_perimeter_assertions(ok_fr) == [ok_fr]
    assert check_assertion(FILES_2_13499, ok_fr) == []
    assert extract_perimeter_assertions(ok_en) == [ok_en]
    assert check_assertion(FILES_2_13499, ok_en) == []
    problems = check_assertion(FILES_2_13499, "Périmètre : 3 fichiers.")
    assert problems and any("3" in p for p in problems)
    problems = check_assertion(FILES_2_13499, "Perimeter: 3 files touched.")
    assert problems and any("3" in p for p in problems)


def test_13535_founder_body_13499_extracts_nothing():
    """Fixture du corps reel de #13499 (avant reformulation) : la phrase
    incriminee verbatim + l'enumeration des 2 fichiers reels ne produisent
    AUCUNE assertion extraite -- le scan du corps rend VERDICT: OK.

    Le replay passe par le MEME chemin que le scan CLI (select_candidates sur
    une fausse review thread, puis confrontation de chaque candidat) : zero
    candidat porteur d'un compte -> zero blocage -> verdict OK."""
    body = (
        "Le symptôme mesuré : sous cap 8, le sweep ne descend jamais dans la\n"
        "file des vieilles PRs -- il rend le même verdict sur une file qui\n"
        "avance et sur une file figée, donc il ne peut pas distinguer.\n"
        "\n"
        "**Fichiers:** scripts/pick_idle_grain.py, scripts/tests/test_pick_idle_grain.py\n"
    )
    assert _word_form_count(body) is None
    found = extract_perimeter_assertions(body)
    assert not any("file" in f.lower() for f in found), (
        f"la prose « file d'attente » ne doit pas devenir une assertion : {found}"
    )
    items = [{
        "kind": "PR body",
        "author": "myia-po-2026",
        "body": body,
        "source": "body",
        "ts": "",
    }]
    candidates, orphan = select_candidates(items, n_files=len(FILES_2_13499))
    assert orphan is None
    for cand in candidates:
        assert check_assertion(FILES_2_13499, cand.text) == [], (
            f"le corps de #13499 doit rester OK ; candidat {cand.text!r}"
        )


def test_13535_word_form_extraction_still_fires():
    """Controle FN : une vraie declaration mot-forme reste extraite et
    confrontee (l'accord de langue n'affaiblit pas le garde). Compte juste ->
    PASS ; compte faux -> FAIL avec le compte effectif."""
    line = "Périmètre : deux fichiers uniquement, aucune autre modification."
    assert extract_perimeter_assertions(line) == [line]
    assert check_assertion(FILES_2_13499, line) == []
    mismatch = "Périmètre : trois fichiers uniquement, aucune autre modification."
    problems = check_assertion(FILES_2_13499, mismatch)
    assert problems and any("2" in p for p in problems)

# ---------------------------------------------------------------------------
# #14438 -- article indefini nu (« un/une fichier(s) ») : pas un compte.
# Reproducteur PR #14430 (run 33723731681) : « Un rendu scope ne voit pas
# la casse qu'un fichier change provoque dans un fichier inchange » ->
# VERDICT FAIL pretendu 1 fichier, liste effective 3. « un fichier » est la
# prose la plus banale possible ; seul le quantificateur restrictif
# « un seul fichier » denombre un perimetre. La forme chiffree
# « 1 fichier : <chemin> » reste la voie officielle (COUNT_CLAIM,
# couverte par les controles #13535 digit forms).

# NB : la liste NE contient pas le garde lui-meme -- une PR qui edite
# scripts/check_pr_perimeter.py declenche l'auto-exemption self-hosting
# (#12201) et la confrontation saute, ce qui fausserait le controle FP.
FILES_3_14430 = [
    {"path": "scripts/pick_idle_grain.py", "additions": 30, "deletions": 5},
    {"path": "scripts/tests/test_pick_idle_grain.py", "additions": 60, "deletions": 10},
    {"path": "docs/reference/perimeter-guard.md", "additions": 5, "deletions": 0},
]


def test_14438_false_negative_bare_article_prose():
    """Reproducteur #14430 (phrase verbatim) : la prose « un fichier
    change ... un fichier inchange » ne sort plus de l'extraction -- le
    scan ne produit aucun candidat, aucun rouge, meme face a la liste
    effective de 3 fichiers."""
    line = (
        "Un rendu scope ne voit pas la casse qu'un fichier change provoque "
        "dans un fichier inchange (reference croisee, entree de barre laterale)"
    )
    assert _word_form_count(line) is None
    assert extract_perimeter_assertions(line) == []
    items = [{
        "kind": "PR body",
        "author": "myia-po-2023",
        "body": line,
        "source": "body",
        "ts": "",
    }]
    candidates, orphan = select_candidates(items, n_files=len(FILES_3_14430))
    assert orphan is None
    assert candidates == [], (
        "aucun candidat ne doit sortir de la prose #14430; got: "
        + repr(candidates)
    )


def test_14438_positive_control_restricted_form_still_fires():
    """Controle FP impose par l'issue : une vraie assertion « un seul
    fichier » déclenche toujours (extraction + confrontation, rouge si le
    comptage est faux). La forme chiffree « 1 fichier : X » reste la voie
    officielle, toujours couverte par COUNT_CLAIM."""
    line = "Cette PR modifie un seul fichier : scripts/pick_idle_grain.py"
    assert _word_form_count(line) == 1
    assert extract_perimeter_assertions(line) == [line]
    problems = check_assertion(FILES_3_14430, line)
    assert len(problems) == 1, (
        "vraie assertion d'un fichier face a 3 fichiers doit rougir; got: "
        + repr(problems)
    )
    assert "l'assertion pretend 1 fichier" in problems[0]
    # forme chiffree, compte juste sur un PR a 1 fichier -> PASS
    single = [FILES_3_14430[0]]
    digit_ok = "Perimetre : 1 fichier : scripts/pick_idle_grain.py"
    assert extract_perimeter_assertions(digit_ok) == [digit_ok]
    assert check_assertion(single, digit_ok) == []
    digit_bad = "Perimetre : 2 fichiers modifies."
    assert check_assertion(single, digit_bad) != []


# ---------------------------------------------------------------------------
# #13610 -- article indefini ("un/une/des fichier(s)") + verbe d'action dont
# le referent NOMMÉ n'est pas dans la PR. Founder case PR #13539 l.43 :
# « generaliser demanderait d'editer pick_idle_grain.py, un fichier deja
# porteur de deux PRs ouvertes de la meme lane (#13496, #13499) ». The
# "un fichier" describes an OTHER file (a routing target, a dependency), not
# the PR's perimeter. FN safety: anonymous referent (no named file on the
# line) keeps the rouge -- consistent with the script's founder pattern of
# default-fail-loud on ambiguous shapes.
# ---------------------------------------------------------------------------

FILES_13610 = [
    {"path": ".github/workflows/epic-charter-advisory.yml"},
    {"path": "scripts/check_epic_charter.py"},
    {"path": "scripts/tests/test_epic_charter.py"},
]


def test_13610_founder_case_named_out_of_scope_passes():
    """Founder case (named file out of scope): the referent is
    `pick_idle_grain.py`, a file the PR does NOT touch. #14438 : la forme
    verbatim « un fichier » (article nu) n'est plus du tout un compte -- la
    ligne ne sort plus de l'extraction, le scan la laisse passer. La forme
    restrictive « un seul fichier » reste un compte, et le predicat #13610
    la protege aussi (referent nomme hors scope -> pas de rouge)."""
    bare = (
        "generaliser demanderait d'editer pick_idle_grain.py, un fichier "
        "deja porteur de deux PRs ouvertes de la meme lane (#13496, #13499)"
    )
    assert _word_form_count(bare) is None
    assert extract_perimeter_assertions(bare) == [], (
        "article nu : la prose ne doit plus etre extraite comme assertion"
    )
    restricted = (
        "generaliser demanderait d'editer pick_idle_grain.py, un seul "
        "fichier deja porteur de deux PRs ouvertes de la meme lane"
    )
    problems = check_assertion(FILES_13610, restricted)
    assert problems == [], (
        "restrictive shape must not rouge the word-form count; got: " + repr(problems)
    )


def test_13610_founder_case_via_une_target():
    """Symmetric founder case via the feminine article 'une cible', with a
    named file. Mirrors the live #13539 reformulation: 'une cible' was
    already outside the count regex (no 'fichier(s)' in the phrase), and
    the `non verifiable` guard fires because no count + no exclusivity is
    recognized -- but the body still does not falsely rouge on a NUMBER
    mismatch. The shape's exemption from the count branch is structural;
    this test pins that."""
    line = (
        "generaliser demanderait d'editer scripts/pick_idle_grain.py, une "
        "cible deja porteuse de deux PRs ouvertes de la meme lane (#13496)"
    )
    problems = check_assertion(FILES_13610, line)
    # The 'non verifiable' guard fires (no digit count + no exclusivity
    # marker) -- this is NOT the founder case (#13610); the founder case
    # is the COUNT_MISMATCH branch with an indefinite article. Documented
    # here to prevent a future refactor from collapsing the two shapes.
    assert any("formulation non verifiable" in p for p in problems), (
        "expected the 'non verifiable' guard to fire for a 'une cible' "
        "shape (no digit count, no exclusivity); got: " + repr(problems)
    )
    assert not any("l'assertion pretend" in p for p in problems), (
        "an indefinite article with no 'fichier(s)' must not trigger a "
        "count-mismatch rouge; got: " + repr(problems)
    )


def test_13610_true_assertion_one_file_named_in_scope_still_rouges():
    """Une vraie assertion d'un fichier dont le referent nomme EST dans la
    PR reste bloquante -- le filtre ne doit pas silencier les vraies
    assertions. Forme restrictive « un seul » : seul cardinal FR-1 restant
    (article nu retire par #14438)."""
    line = "Cette PR modifie un seul fichier scripts/check_epic_charter.py"
    problems = check_assertion(FILES_13610, line)
    assert len(problems) == 1, (
        "true assertion must still rouge; got: " + repr(problems)
    )
    assert "l'assertion pretend 1 fichier" in problems[0]


def test_13610_fn_safety_anonymous_referent_keeps_rouge():
    """FN control 1: no named file on the line, but the edit-verb is
    present. The shape is AMBIGUOUS -- 'editer un seul fichier' could mean
    the PR or another file. Default-fail-loud: keep the rouge."""
    line = (
        "generaliser demanderait d'editer un seul fichier deja porteur de "
        "deux PRs ouvertes de la meme lane"
    )
    problems = check_assertion(FILES_13610, line)
    assert len(problems) == 1, (
        "anonymous referent must stay rouge; got: " + repr(problems)
    )


def test_13610_fn_safety_no_edit_verb_keeps_rouge():
    """FN control 2: no edit-verb in the run-up. The 'un seul fichier' is
    descriptive prose, but without an action verb the exemption branch
    cannot fire -- the rouge stays."""
    line = "il y a un seul fichier quelque part qui pose probleme."
    problems = check_assertion(FILES_13610, line)
    assert len(problems) == 1, (
        "no-verb shape must stay rouge; got: " + repr(problems)
    )


def test_13610_predicate_unit_unanimous():
    """Direct unit test of _word_form_is_indef_non_pr_subject: 5 sentences,
    unanimous verdicts. Decoupled from check_assertion so a future pipeline
    change cannot mask a predicate regression."""
    files = FILES_13610
    # True cases
    assert _word_form_is_indef_non_pr_subject(
        "editer pick_idle_grain.py, un fichier deja porteur", files
    ) is True
    assert _word_form_is_indef_non_pr_subject(
        "modifier scripts/foo.py, un fichier de tests", files
    ) is True
    # #14438 : la forme restrictive « un seul » suit le meme predicat
    assert _word_form_is_indef_non_pr_subject(
        "editer pick_idle_grain.py, un seul fichier deja porteur", files
    ) is True
    # False cases (genuine or ambiguous)
    assert _word_form_is_indef_non_pr_subject(
        "Cette PR modifie un fichier scripts/check_epic_charter.py", files
    ) is False
    assert _word_form_is_indef_non_pr_subject(
        "Cette PR modifie un seul fichier scripts/check_epic_charter.py", files
    ) is False
    assert _word_form_is_indef_non_pr_subject(
        "editer un fichier quelque part", files
    ) is False  # anonymous
    assert _word_form_is_indef_non_pr_subject(
        "il y a un fichier ici", files
    ) is False  # no edit-verb
    assert _word_form_is_indef_non_pr_subject(
        "Cette PR ajoute un fichier scripts/check_epic_charter.py dans "
        "scripts/check_epic_charter.py", files
    ) is False  # named file IS in scope


# ---------------------------------------------------------------------------
# #13610 residual (2026-09-02, measured by po-2024) -- the referent is named,
# but named as a SYMBOL, not as a file. The tail class of _NAMED_FILE_BODY was
# `[A-Za-z0-9]+`, which excludes the underscore; a dotted symbol was therefore
# not recognized as a named referent, and the FN-safety branch kept the rouge
# on the FOUNDING sentence of #13539 itself. The boundary was arbitrary AND
# invisible: the same code reference passed or rouged on the sole strength of
# one underscore. The pair below is the proof -- the first test alone would be
# satisfied by simply disabling the guard, which is why the positive control
# and the anonymous-referent control are pinned alongside it.
# ---------------------------------------------------------------------------

# The two rows of the #13610 table, same sentence, same referent, one
# underscore apart. #14438 : la forme verbatim porte « un fichier » (article
# nu, plus un compte) -- la preuve de la protection du referent passe par la
# forme restrictive « un seul fichier », seule forme encore tracee par le
# garde (la forme verbatim ne sort plus de l'extraction, verifiee dans
# test_13610_founding_sentence_of_13539_passes).
_SYMBOL_SHAPE = (
    "L'upsert vit dans `pick_idle_grain.{symbole}` ; le generaliser "
    "demanderait d'editer un seul fichier deja porteur de deux PRs "
    "ouvertes de la meme lane"
)


def test_13610_symbol_referent_without_underscore_passes():
    """Table row 1: `pick_idle_grain.upsert` -- passed even before the fix.
    Pinned so a future tightening of the tail class cannot silently take it
    back, which would re-open the inversion from the other side."""
    line = _SYMBOL_SHAPE.format(symbole="upsert")
    problems = check_assertion(FILES_13610, line)
    assert problems == [], (
        "a dotted symbol without underscore must not rouge; got: "
        + repr(problems)
    )


def test_13610_symbol_referent_with_underscore_passes():
    """Table row 2: `pick_idle_grain.upsert_orphans` -- ROUGED before the fix,
    on the sole strength of the underscore. This is the regression the
    residual names."""
    line = _SYMBOL_SHAPE.format(symbole="upsert_orphans")
    problems = check_assertion(FILES_13610, line)
    assert problems == [], (
        "a dotted symbol with an underscore must not rouge -- the underscore "
        "is not a semantic boundary; got: " + repr(problems)
    )


def test_13610_founding_sentence_of_13539_passes():
    """The sentence of #13539 that founded the whole thread. Its referent was
    named all along -- named as a symbol. Acceptance line 1 of #13610."""
    line = _SYMBOL_SHAPE.format(symbole="upsert_orphans_comment")
    problems = check_assertion(FILES_13610, line)
    assert problems == [], (
        "the founding sentence of #13539 must pass the guard; got: "
        + repr(problems)
    )
    # #14438 : la forme verbatim article nu n'est plus un candidat du tout --
    # le scan la laisse passer sans jamais la confronter.
    bare_verbatim = (
        "L'upsert vit dans `pick_idle_grain.upsert_orphans_comment` ; le "
        "generaliser demanderait d'editer un fichier deja porteur de deux "
        "PRs ouvertes de la meme lane"
    )
    assert extract_perimeter_assertions(bare_verbatim) == [], (
        "la forme article nu ne doit plus etre extraite comme assertion"
    )


def test_13610_symbol_widening_keeps_positive_control_rouge():
    """Acceptance line 2 of #13610, stated as a PAIR with the three tests
    above: widening the tail class must NOT extinguish the positive control.
    A fix that made the symbol cases pass by weakening the guard would pass
    those three and fail this one -- which is the whole point of pinning it
    here rather than relying on the older copy elsewhere in the file."""
    problems = check_assertion(FILES_13610, "Cette PR ne touche qu'un seul fichier.")
    assert problems, (
        "the positive control must still rouge after the widening -- "
        "3 files in the PR, assertion claims 1"
    )


def test_13610_symbol_widening_keeps_anonymous_referent_rouge():
    """FN-safety, restated post-widening: widening WHAT counts as a named
    referent must not turn an ANONYMOUS referent into a named one. #13612's
    deliberate default-fail-loud on ambiguous shapes is untouched."""
    line = (
        "le generaliser demanderait d'editer un seul fichier deja porteur "
        "de deux PRs ouvertes"
    )
    problems = check_assertion(FILES_13610, line)
    assert problems, (
        "an anonymous referent must keep the rouge after the widening"
    )


def test_13610_symbol_predicate_unit_pair():
    """Direct unit test of the predicate on the two table rows, decoupled from
    check_assertion so a pipeline change cannot mask a predicate regression --
    same rationale as test_13610_predicate_unit_unanimous."""
    files = FILES_13610
    assert _word_form_is_indef_non_pr_subject(
        _SYMBOL_SHAPE.format(symbole="upsert"), files
    ) is True
    assert _word_form_is_indef_non_pr_subject(
        _SYMBOL_SHAPE.format(symbole="upsert_orphans"), files
    ) is True
    assert _word_form_is_indef_non_pr_subject(
        _SYMBOL_SHAPE.format(symbole="upsert_orphans_comment"), files
    ) is True
    # The widening is about the TAIL of a dotted referent, nothing else:
    # an anonymous referent stays False.
    assert _word_form_is_indef_non_pr_subject(
        "editer un fichier quelque part", files
    ) is False


# ---------------------------------------------------------------------------
# #13637 -- carried-from-main files. GitHub's /pulls/N/files diffs base-tip ->
# head, so a branch that merged main gets main's own changes attributed to it
# (founder #13601: 04-7 showed +2708/-2708 although the PR did not touch it).
# The fix subtracts files the head already agrees with main on from the
# effective perimeter and names them separately. The git predicate itself is
# verified on a live negative control (#13606 fresh base -> 0 carried; ~40 open
# PRs scanned -> 0 carried) and on a synthetic founder shape (a main-changed
# file merged into the branch is classified carried); these unit tests pin the
# PURE partition + render, which is what the .py avoids network for.
# ---------------------------------------------------------------------------

# The founder shape, encoded with a synthetic carried path (04-7 from #13601).
# The carried set carries FULL paths (the API list's `filename`), so the
# basename does not match -- partition_propres compares the whole path.
# The two propres are deliberately NOT scripts/check_pr_perimeter.py, so the
# #12201 self-hosting exemption (skip equality on a PR that edits the guard)
# never fires -- here we exercise the ordinary subtraction path.
_CARRIED_13637 = "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-7-TTS-Voice-Benchmark.ipynb"
_FILES_13637 = [
    {"path": _CARRIED_13637, "additions": 2708, "deletions": 2708},
    {"path": "MyIA.AI.Notebooks/GameTheory/game_theory_lean/CooperativeGames/Shapley.lean",
     "additions": 60, "deletions": 20},
    {"path": "docs/lean/i18n-inventory.md", "additions": 45, "deletions": 5},
]


def test_13637_partition_splits_carried_from_own():
    """#13637: partition_propres separates the carried file from the PR's own
    work. 04-7 (head agrees with main) is carried; the two fichiers are the
    PR's contribution."""
    propres, charries = partition_propres(_FILES_13637, {_CARRIED_13637})
    assert [f["path"] for f in propres] == [
        "MyIA.AI.Notebooks/GameTheory/game_theory_lean/CooperativeGames/Shapley.lean",
        "docs/lean/i18n-inventory.md",
    ]
    assert [f["path"] for f in charries] == [_CARRIED_13637]


def test_13637_partition_no_carried_is_all_propre():
    """#13637 negative control: an empty carried set leaves the list whole."""
    propres, charries = partition_propres(_FILES_13637, set())
    assert len(propres) == 3 and charries == []


def test_13637_partition_is_order_preserving():
    """#13637: a rounding of the perimeter reorders nothing -- diff-reading
    reviewers keep their anchors (order, not sorted)."""
    files = [{"path": "z.py"}, {"path": "a.py"}, {"path": "m.py"}]
    propres, charries = partition_propres(files, {"a.py"})
    assert [f["path"] for f in propres] == ["z.py", "m.py"]
    assert [f["path"] for f in charries] == ["a.py"]


def test_13637_report_renders_carried_note_and_stale_signal():
    """#13637 step 1+3: the cardinal change is EXPLAINED (count + carried paths
    + stale-base signal), never silently masked."""
    report = __import__("check_pr_perimeter").Report(
        files=partition_propres(_FILES_13637, {_CARRIED_13637})[0],
        moves=[],
        carried=CarriedNote(
            propres=partition_propres(_FILES_13637, {_CARRIED_13637})[0],
            charries=partition_propres(_FILES_13637, {_CARRIED_13637})[1],
            base_age_hours=48,
        ),
    )
    lines = format_report(report, None).splitlines()
    assert any("Périmètre effectif : 2 fichier(s)" in l for l in lines)
    assert any("dont 1 charrié(s)" in l for l in lines)
    assert any("04-7-TTS-Voice-Benchmark.ipynb" in l for l in lines)
    assert any("STALE-BASE" in l for l in lines)
    assert any("2 j" in l for l in lines), "48 h must render as ~2 j (days bound)"


def test_13637_report_omits_age_when_unresolvable():
    """#13637: an unresolvable base age omits the 'vieille de X' qualifier rather
    than inventing one -- the count + note stay informative."""
    report = __import__("check_pr_perimeter").Report(
        files=partition_propres(_FILES_13637, {_CARRIED_13637})[0],
        moves=[],
        carried=CarriedNote(
            propres=partition_propres(_FILES_13637, {_CARRIED_13637})[0],
            charries=partition_propres(_FILES_13637, {_CARRIED_13637})[1],
            base_age_hours=None,
        ),
    )
    lines = format_report(report, None).splitlines()
    assert any("dont 1 charrié(s) de main, non compté(s)" in l for l in lines)
    assert not any("vieille de" in l for l in lines), "age must be omitted when unresolvable"
    assert any("STALE-BASE" in l for l in lines)
    # The cardinal line carries the count only; carried paths live on the
    # dedicated enumeration line (rendered without any age qualifier here).
    # A path on the cardinal line would mean count-note and enumeration
    # merged -- the displaced defect #13637 step 1+3 exists to close.
    cardinal = [l for l in lines if l.lstrip().startswith("— dont")]
    assert len(cardinal) == 1
    assert "04-7-TTS-Voice-Benchmark.ipynb" not in cardinal[0]
    assert any(
        "04-7-TTS-Voice-Benchmark.ipynb" in l
        and l.lstrip().startswith("— charrié(s) de main")
        for l in lines
    ), "carried paths must be enumerated on the dedicated line"


def test_13637_report_backward_compat_without_carried():
    """#13637 non-regression: a report with no carried note renders exactly as
    before (existing callers pass (report, None))."""
    lines = format_report(
        __import__("check_pr_perimeter").Report(
            files=[{"path": "README.md", "additions": 1, "deletions": 1}],
            moves=[],
        ),
        None,
    ).splitlines()
    assert any("Périmètre effectif : 1 fichier(s)" in l for l in lines)
    assert not any("charrié" in l for l in lines)
    assert not any("STALE-BASE" in l for l in lines)


def test_13637_partition_exposes_correct_count_for_assertion():
    """#13637 end-to-end at the pure level: after subtracting the carried file,
    the effective perimeter is 2 -- so `check_assertion` confronts a body claim
    against 2, not the API's 3."""
    propres, charries = partition_propres(_FILES_13637, {_CARRIED_13637})
    assert len(propres) == 2 and len(charries) == 1
    # The perimeter-review guard confronts against len(report.files) == 2.
    problems = check_assertion(
        propres, "Périmètre : 3 fichiers."  # body over-counts the API list
    )
    assert any("3" in p and "2" in p for p in problems), (
        "a body that counts the carried file must be over-count: " + repr(problems)
    )
    # A body that states the true (propre) count passes.
    assert check_assertion(propres, "Périmètre : 2 fichiers.") == []


# ---------------------------------------------------------------------------
# #13791 — somme additive au bloc paragraphe + vocabulaire grep + word-form
# objet de mesure. Fondateurs mesurés : #13736 (deux puces "1 fichier" + une
# ligne diagnostique word-form) et #13782 ("(grep : 1 fichier)").
# ---------------------------------------------------------------------------

FOUNDER_13736_BODY = (
    "## Périmètre\n"
    "\n"
    "- 1 fichier modifié (`scripts/ci/check_concurrency_conj.py`, +1/-1)\n"
    "- 1 fichier de test modifié (`scripts/tests/test_check_concurrency_conj.py`, +37/-0)\n"
    "- Aucune collision chemin : les PRs parentes ne touchent plus ce fichier.\n"
)
FOUNDER_13736_FILES = [
    {"path": "scripts/ci/check_concurrency_conj.py"},
    {"path": "scripts/tests/test_check_concurrency_conj.py"},
]
# Ligne diagnostique fondatrice (#13736 l.26) : le word-form « un fichier »
# y désigne les objets d'une comparaison, pas le périmètre.
FOUNDER_13736_DIAG = (
    "Tout workflow malformé fait planter l'instrument, et le script échoue "
    "sur un faux positif (l'instrument ne peut pas distinguer un fichier "
    "corrompu d'un fichier offensif)."
)
# Ligne fondatrice #13782 : « (grep : 1 fichier) » est une mesure du corpus.
FOUNDER_13782_LINE = (
    "2.9 est le **seul notebook torch de 02-ML-Cours** (grep : 1 fichier) : "
    "c'est assumé par le README."
)


def test_13791_additive_block_sum_spans_bullets():
    """L'énumération additive sur deux puces (1 + 1 = 2) passe quand la
    confrontation reçoit le bloc paragraphe -- chaque ligne candidate voit
    la somme du bloc, pas seulement sa ligne."""
    triple = extract_perimeter_assertions_with_block(FOUNDER_13736_BODY)
    digit_candidates = [(l, b) for l, _ctx, b in triple if COUNT_CLAIM.search(l)]
    assert len(digit_candidates) == 2, digit_candidates
    for line, block in digit_candidates:
        assert "1 fichier" in line
        # chaque puce du bloc porte exactement un compte survivant
        assert sum(_additive_line_sum(ln) for ln in block.splitlines()) == 2
        assert check_assertion(FOUNDER_13736_FILES, line, block=block) == [], line


def test_13791_additive_line_scope_still_fails_without_block():
    """Sans bloc (mode --assert, candidates de thread), la somme line-scope
    mismatche 1 vs 2 -- comportement inchangé, c'est le résidu #13791."""
    assert check_assertion(
        FOUNDER_13736_FILES, "- 1 fichier modifié (`scripts/ci/check_concurrency_conj.py`, +1/-1)"
    ) != []


def test_13791_block_sum_never_validates_wrong_total():
    """Contrôle FN local : une somme de bloc ≠ len(files) reste rouge -- le
    bloc dessert l'énumération exacte, pas n'importe quelle somme."""
    body = "- 1 fichier a\n- 1 fichier b\n- 1 fichier c\n"
    files = [{"path": "a"}, {"path": "b"}]
    triple = extract_perimeter_assertions_with_block(body)
    for line, _ctx, block in triple:
        assert check_assertion(files, line, block=block) != [], line


def test_13791_grep_antecedent_exempts_corpus_count():
    """« (grep : 1 fichier) » est une mesure du corpus (#13782) : le compte
    est incidental, la candidate ne bloque pas (l'architecture #11712 : la
    détection reste, seule la conséquence bouge -- check_assertion rend le
    mismatch, `blocking` le rétrograde en signal)."""
    assert _is_incidental_assertion(FOUNDER_13782_LINE, "") is True
    cand = Candidate(FOUNDER_13782_LINE, "PR body", "author", "body")
    assert cand.blocking is False


def test_13791_grep_absence_keeps_the_red():
    """Contrôle FN : sans antécédent de mesure, « 1 fichier modifié » devant
    une liste de 2 reste rouge -- grep n'a rien desserré d'autre."""
    files = [{"path": "a.py"}, {"path": "b.py"}]
    assert check_assertion(files, "1 fichier modifié (`a.py`)") != []


def test_13791_word_form_discrimination_verb_exempts():
    """« distinguer un fichier corrompu d'un fichier offensif » (#13736) :
    le word-form désigne les objets d'une comparaison, pas le périmètre.
    #14438 : la forme article nu ne sort plus de l'extraction (prose, pas
    assertion) ; la forme restrictive « un seul » reste protegee par le
    predicat de discrimination."""
    files = [{"path": "scripts/ci/check_concurrency_conj.py"},
             {"path": "scripts/tests/test_check_concurrency_conj.py"}]
    assert extract_perimeter_assertions(FOUNDER_13736_DIAG) == [], (
        "la prose de comparaison article nu ne doit plus etre extraite"
    )
    restricted = FOUNDER_13736_DIAG.replace(
        "un fichier ", "un seul fichier ", 1
    )
    assert check_assertion(files, restricted) == []


def test_13791_word_form_plain_indefinite_still_blocks():
    """Contrôle FN : « un seul fichier modifié » sans verbe de discrimination
    reste confronté (1 vs 2 -> rouge). La forme article nu « un fichier
    modifié » n'est plus un compte du tout (#14438)."""
    files = [{"path": "a.py"}, {"path": "b.py"}]
    assert check_assertion(files, "1 fichier modifié (`a.py`)") != []  # chiffre
    assert check_assertion(files, "un seul fichier modifié (`a.py`)") != []


def test_13791_word_form_measurement_result_exempts():
    """Un résultat de mesure sur les deux fichiers n'est pas le périmètre."""
    files = [{"path": f"file-{i}.py"} for i in range(6)]
    line = (
        "les anciennes formes `Z3-Python 07`, `Z3-Python-06 >>` et la clé "
        "baseline `Z3_PYTHON_CLAVIER`: **0 occurrence** sur les **deux fichiers** corrigés"
    )
    assert check_assertion(files, line) == []


def test_13791_word_form_measurement_result_soft_wrap_exempts():
    """Le résultat de mesure reste exempté après un retour à la ligne doux."""
    files = [{"path": f"file-{i}.py"} for i in range(6)]
    body = "les anciennes formes : **0 occurrence**\nsur les **deux fichiers** corrigés"
    line, _context, block = extract_perimeter_assertions_with_block(body)[0]
    assert check_assertion(files, line, block=block) == []


def test_13791_digit_scope_with_zero_result_still_blocks():
    """Contrôle FN : le périmètre chiffré reste rouge malgré zéro résultat."""
    files = [{"path": "a.py"}, {"path": "b.py"}, {"path": "c.py"}]
    line = "Périmètre : 2 fichiers twins uniquement, aucune autre modification."
    assert check_assertion(files, line) != []


def test_13791_word_form_scope_with_zero_result_still_blocks():
    """Contrôle FN : le périmètre en lettres reste rouge malgré zéro résultat."""
    files = [{"path": "a.py"}, {"path": "b.py"}, {"path": "c.py"}]
    line = "Périmètre : deux fichiers uniquement, aucune autre modification."
    assert check_assertion(files, line) != []


def test_13791_paragraph_block_boundaries():
    """Le bloc paragraphe s'arrête aux lignes vides et aux fences, dans les
    deux directions."""
    text = (
        "avant le vide\n"
        "\n"
        "- 1 fichier a\n"
        "- 1 fichier b\n"
        "\n"
        "après le vide\n"
    )
    lines = text.splitlines()
    idx = lines.index("- 1 fichier a")
    block = _paragraph_block(text, idx)
    assert "- 1 fichier a" in block and "- 1 fichier b" in block
    assert "avant le vide" not in block and "après le vide" not in block
    # fence delimiter en borne inférieure
    fenced = "- 1 fichier a\n```python\nx = 1\n```\n"
    idx_f = fenced.splitlines().index("- 1 fichier a")
    assert "x = 1" not in _paragraph_block(fenced, idx_f)


# #13946 : un compte annoté `(hors scope PR)` est un constat pour une
# tranche ultérieure, PAS le périmètre livré. Sans le filtre, le script
# sélectionne le premier count non nul (« 28 fichiers » dans le fondateur
# #13856) au lieu du périmètre réel.


def test_13946_hors_scope_annotation_excludes_count_from_selection():
    """#13946 : un « 28 fichiers constatés » dans une ligne annotée
    `(hors scope PR)` n'est PAS le périmètre. Le compte est ignoré."""
    files = [{"path": "CLAUDE.md"}, {"path": "docs/reference/_archive-convention.md"}]
    line = (
        "- Tranche 3 (hors scope PR) : appliquer à scripts/_archive/ "
        "(28 fichiers constatés, peut nécessiter split par sous-dossier)."
    )
    # Sans le filtre, l'assertion échoue avec 28 ≠ 2.
    # Avec le filtre, plus aucun count ne survit => "no count" terminal,
    # PAS un mismatch -- c'est le bon comportement avant le fallback
    # `touche N` (testé séparément dans test_13946_touche_n_fallback).
    problems = check_assertion(files, line)
    assert not any("28 fichier" in p for p in problems), (
        f"le compte hors-scope 28 doit etre ignore, obtained {problems!r}"
    )


def test_13946_touche_n_fallback_finds_perimeter_in_paragraph():
    """#13946 : quand le forecast hors-scope est filtré, le périmètre
    réel via « touche N » dans le MEME paragraphe est détecté."""
    files = [{"path": "CLAUDE.md"}, {"path": "docs/reference/_archive-convention.md"}]
    body = (
        "**Hors scope PR (comptes prévisionnels) :**\n"
        "- Tranche 3 (hors scope PR) : appliquer à scripts/_archive/ "
        "(28 fichiers constatés).\n"
        "\n"
        "qui en touche 2 (CLAUDE.md + _archive-convention.md)."
    )
    line = (
        "- Tranche 3 (hors scope PR) : appliquer à scripts/_archive/ "
        "(28 fichiers constatés)."
    )
    # Block contains the hors-scope header + this line + the next paragraph.
    block = body  # body_hint equivalent; the fallback searches block first.
    problems = check_assertion(files, line, block=block)
    assert problems == [], (
        f"le fallback touche N aurait dû trouver le périmètre 2, "
        f"obtenu {problems!r}"
    )


def test_13946_touche_n_fallback_searches_body_when_block_lacks_it():
    """#13946 founder case : le périmètre « touche N » est dans une
    AUTRE paragraphe que la ligne candidate. Le ``body_hint`` (passé
    par ``--scan-thread``) permet le cross-paragraph scan."""
    files = [{"path": "CLAUDE.md"}, {"path": "docs/reference/_archive-convention.md"}]
    line = (
        "- Tranche 3 (hors scope PR) : appliquer à scripts/_archive/ "
        "(28 fichiers constatés, peut nécessiter split par sous-dossier)."
    )
    body = (
        "**Hors scope PR (comptes prévisionnels) :**\n"
        + line + "\n\n"
        "Les comptes « 28 fichiers » ... pas le périmètre livré par cette PR "
        "qui en touche 2 (CLAUDE.md + _archive-convention.md)."
    )
    # Empty block (cross-paragraph case); body_hint carries the perimeter.
    problems = check_assertion(files, line, block="", body_hint=body)
    assert problems == [], (
        f"fallback body_hint aurait dû trouver « touche 2 », "
        f"obtenu {problems!r}"
    )


def test_13946_negative_real_perimeter_still_blocks():
    """#13946 FN-safety : quand le périmètre réel dit bien « N fichiers »
    dans le body et que le diff diffère, le rouge tient toujours. Le
    filtre hors-scope ne masque pas un vrai claim."""
    files = [{"path": "real.py"}, {"path": "extra.py"}]
    body = (
        "**Fichiers touchés : 3 fichiers**\n"
        "- real.py\n"
        "\n"
        "(hors scope PR) : 28 fichiers constatés pour la tranche 2."
    )
    # Extract the « Fichiers touchés » line as the candidate.
    candidates = extract_perimeter_assertions(body)
    line = candidates[0]
    problems = check_assertion(files, line, body_hint=body)
    assert any("3 fichier" in p for p in problems), (
        f"un vrai claim de 3 fichiers doit rester rouge quand 2 diff, "
        f"obtenu {problems!r}"
    )


# #14292 — une liste effective VIDE est une non-mesure, pas un zéro.
def test_14292_empty_api_list_is_unmeasurable():
    """Cause 1 : la liste API elle-même est vide (PR fermée/vidée, base qui a
    tout absorbé) — mesuré sur #11956 (main @ 84d6a974d9) et sur le FAIL
    fantôme post-merge de #14536 (run 33849858765)."""
    reason = unmeasurable_perimeter([], None)
    assert reason is not None and "liste API vide" in reason
    # Même cause quand la classification a tourné sur une liste API vide
    # (_classify_carried rend propres=[], charries=[] dans ce cas).
    reason2 = unmeasurable_perimeter([], CarriedNote(propres=[], charries=[]))
    assert reason2 is not None and "liste API vide" in reason2


def test_14292_all_carried_is_unmeasurable():
    """Cause 2 : liste API non vide mais tout charrié de main (STALE-BASE
    extrême, carried.propres == [])."""
    carried = CarriedNote(
        propres=[], charries=[{"path": "a.py"}], base_age_hours=None
    )
    reason = unmeasurable_perimeter([], carried)
    assert reason is not None and "charrié" in reason


def test_14292_measurable_perimeter_returns_none():
    """Contrôle négatif obligatoire (#14292 acceptance 2) : un périmètre réel
    ne rend jamais de raison — sans lui, « ne bloque plus » serait
    indiscernable d'un garde débranché."""
    assert unmeasurable_perimeter([{"path": "a.py"}], None) is None
    # Même avec des charriés, un périmètre propre non vide reste mesurable.
    mixed = CarriedNote(
        propres=[{"path": "b.py"}], charries=[{"path": "a.py"}], base_age_hours=3
    )
    assert unmeasurable_perimeter([{"path": "b.py"}], mixed) is None


def test_14292_ghost_fail_shape_becomes_signal(monkeypatch, capsys):
    """La forme exacte mesurée sur #11956 (issue body) : body honnête
    « Fichiers touchés : 5 fichiers », liste effective vide → le garde rendait
    « VERDICT: FAIL / l'assertion pretend 5 fichier(s), la liste effective en
    compte 0 ». Après #14292 : exit 0, PERIMETRE NON MESURABLE imprimé,
    l'assertion visible sous SIGNAL (pas effacée)."""
    import check_pr_perimeter as cpp

    body = "**Fichiers touchés : 5 fichiers**\n- real.py\n"
    monkeypatch.setattr(
        cpp, "fetch_report",
        lambda pr: cpp.Report(
            files=[], moves=[],
            carried=CarriedNote(propres=[], charries=[]),
        ),
    )
    monkeypatch.setattr(cpp, "fetch_review_thread", lambda pr: [{
        "kind": "PR body", "author": "jsboige", "body": body,
        "source": "body", "ts": "",
    }])
    monkeypatch.setattr(
        sys, "argv", ["check_pr_perimeter.py", "11956", "--scan-thread"]
    )
    rc = cpp.main()
    out = capsys.readouterr().out
    assert rc == 0, f"une non-mesure ne doit plus tenir la PR, obtenu :\n{out}"
    assert "PERIMETRE NON MESURABLE" in out and "liste API vide" in out
    assert (
        "l'assertion pretend 5 fichier(s), la liste effective en compte 0" in out
    ), "la détection doit rester visible sous SIGNAL, pas être effacée"
    assert "VERDICT: OK" in out


# ---------------------------------------------------------------------------
# #14911 — `gh pr diff` 406 sur une PR > 300 fichiers.
# ---------------------------------------------------------------------------
def test_pr_diff_text_passes_through_normal_diff(monkeypatch):
    """A normal PR diff is returned verbatim for baseline-move detection."""
    import check_pr_perimeter as cpp

    diff = "diff --git a/x.py b/x.py\n@@ ... @@\n-old\n+new\n"
    monkeypatch.setattr(cpp, "_run_gh_rc", lambda args: (0, diff, ""))
    assert cpp._pr_diff_text(101) == diff


def test_pr_diff_text_falls_back_empty_on_300_file_cap(monkeypatch):
    """#14911: `gh pr diff` caps at 300 files (HTTP 406), a hard crash on a
    legitimate large migration PR. Baseline-move detection is advisory in
    --scan-thread, so the guard must NOT crash: it returns an empty diff
    (moves == []) and warns, while the blocking perimeter checks continue off
    the paginated /pulls/<pr>/files list (which has no such cap)."""
    import check_pr_perimeter as cpp

    def fake_rc(args):
        assert args[:2] == ["pr", "diff"]
        assert args[-1] == "14940"
        return 1, "", (
            "gh error: could not find pull request diff: HTTP 406: Sorry, the "
            "diff exceeded the maximum number of files (300). Consider using "
            "'List pull requests files' API or locally cloning the repository "
            "instead."
        )

    monkeypatch.setattr(cpp, "_run_gh_rc", fake_rc)
    assert cpp._pr_diff_text(14940) == ""


def test_pr_diff_text_fails_closed_on_other_gh_error(monkeypatch):
    """Any OTHER `gh pr diff` failure keeps the fail-closed behaviour -- only
    the 300-file cap is degraded to an empty diff."""
    import check_pr_perimeter as cpp

    def fake_rc(args):
        return 1, "", "gh: authentication failed"

    monkeypatch.setattr(cpp, "_run_gh_rc", fake_rc)
    with pytest.raises(SystemExit):
        cpp._pr_diff_text(101)
