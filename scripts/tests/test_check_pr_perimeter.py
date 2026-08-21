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
    is_downgradable_mismatch,
    select_candidates,
    _check_unterminated_fence,
    _count_is_incidental,
    _fence_line_indices,
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
