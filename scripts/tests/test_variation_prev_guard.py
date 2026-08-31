#!/usr/bin/env python3
"""Unit tests for variation_prev_guard.py -- the BLOCKING prev: close-keyword
gate (#10093).

The #10093 incident: a COMMIT MESSAGE carrying `prev: MED/fix #10067` made
GitHub auto-close PR #10067 at the squash-merge of #10063 -- the PR body of
#10063 was sane (`MED/tooling`). The gate must therefore scan BOTH the body
AND the commit messages, and block (exit 1) when a `prev:` genre is a closing
keyword.

Run:
    python -m pytest scripts/tests/test_variation_prev_guard.py
"""
import sys
from pathlib import Path

# Insert `scripts/ci/` so the script under test is importable from a flat
# `import variation_prev_guard` (same convention as test_variation_tag_required.py).
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import variation_prev_guard as vpg  # noqa: E402


CLEAN_BODY = "Grain: MED/tooling -- lane myia-po-2025:CoursIA-2 -- prev: MED/infra #10067"


def test_clean_body_passes():
    v = vpg.check(CLEAN_BODY)
    assert v["guard_pass"] is True
    assert v["hits"] == {"body": [], "commits": [], "prev_invalid": []}


def test_offending_body_blocks():
    # A `prev: MED/fix #10067` in the BODY -> block.
    v = vpg.check(
        "Grain: MED/fix -- lane myia-po-2024:CoursIA-2 -- prev: MED/fix #10067 (c.1331+50)"
    )
    assert v["guard_pass"] is False
    assert v["hits"]["body"] == [{"tier": "MED", "genre": "fix"}]
    assert "refactor" in v["reason"] or "guard" in v["reason"] or "tooling" in v["reason"]


def test_commit_message_only_blocks():
    # The #10093 incident case: the BODY is clean, the COMMIT carries the
    # offending `prev: MED/fix #10067`. A body-only gate would miss it.
    commits = [
        "feat(ci): some normal commit",
        "Grain: MED/fix -- prev: MED/fix #10067 (c.1331+50)",
    ]
    v = vpg.check(CLEAN_BODY, commits)
    assert v["guard_pass"] is False
    assert len(v["hits"]["body"]) == 0
    assert len(v["hits"]["commits"]) == 1
    assert v["hits"]["commits"][0]["commit_index"] == 1
    assert v["hits"]["commits"][0]["genre"] == "fix"
    assert "commit" in v["reason"]


def test_clean_commits_pass():
    # Commits with a non-closing prev: genre pass.
    commits = [
        "Grain: DEEP/lean -- prev: DEEP/lean #2159",
        "Fixes #100 (intended close, no prev: prefix -> NOT flagged)",
    ]
    v = vpg.check(CLEAN_BODY, commits)
    assert v["guard_pass"] is True


def test_intended_close_not_flagged():
    # A standalone `Fixes #100` / `Closes #456` (no `prev:` prefix) is an
    # INTENDED close and must NOT be flagged -- catalog-pr-hygiene HARD 4
    # relies on `Closes #N`. Only the prev: genre slot is in scope.
    v = vpg.check(
        "Grain: MED/refactor -- lane x:y\n\nThis PR fixes a bug. Fixes #100. Closes #456."
    )
    assert v["guard_pass"] is True


def test_all_canonical_genres_in_prev_pass():
    # Every canonical genre in a prev: field passes (no closing keyword).
    for genre in ("lean", "guard", "refactor", "tooling", "docs", "test",
                  "readme", "ledger", "qc", "training", "genai",
                  "notebook-python", "notebook-dotnet", "slides", "research-code"):
        v = vpg.check(f"prev: MED/{genre} #100")
        assert v["guard_pass"] is True, f"canonical genre {genre} must pass"


def test_both_body_and_commit_hits_aggregated():
    # Offending prev: in BOTH body and a commit -> both reported.
    body = "Grain: LIGHT/close -- prev: LIGHT/close #1"
    commits = ["prev: MED/fixes #2"]
    v = vpg.check(body, commits)
    assert v["guard_pass"] is False
    assert len(v["hits"]["body"]) == 1
    assert len(v["hits"]["commits"]) == 1


def test_empty_inputs_pass():
    assert vpg.check(None)["guard_pass"] is True
    assert vpg.check("")["guard_pass"] is True
    assert vpg.check("", [])["guard_pass"] is True


# --- PREV-INVALID (#13475) ---------------------------------------------
#
# The original gate (#10093) only checked the GENRE slot of the `prev:`
# field. The acceptance of #13475 extended the gate with three invariants on
# the PR-reference slot -- the `genre #N` tail -- each of which silently
# breaks the genre-adjacency measurement G-VAR-3 enforces. Tests below pin
# each invariant by FALSIFYING the bare assertion: stash the source change,
# each test goes red. With the change applied, the gate blocks the three
# measured witnesses (#12875 / #13473 / #13439) and lets a sane tag pass.

CLEAN_PREV_BODY = (
    "Grain: LIGHT/refactor -- lane myia-po-2026:CoursIA "
    "-- prev: LIGHT/refactor #13826"
)
CLEAN_PREV_TARGETS = {"13826": {"kind": "pr", "merged": True}}


def test_prev_self_reference_blocks():
    # #12875 measured: `prev: MED/notebook-python #12875` on PR #12875
    # itself -- the adjacency is vacuous (grain compared to itself).
    v = vpg.check(
        "Grain: MED/notebook-python -- lane myia-po-2023:CoursIA-2 "
        "-- prev: MED/notebook-python #12875",
        current_pr=12875,
        prev_targets={"12875": {"kind": "pr", "merged": True}},
    )
    assert v["guard_pass"] is False
    assert any(h["kind"] == "prev-self" and h["prev_pr"] == 12875
               for h in v["hits"]["prev_invalid"])


def test_prev_self_in_commit_message_blocks():
    # The #10093 precedent says commit messages are in scope (squash-merge
    # publishes them). A PREV-SELF in a commit must be flagged the same way.
    commits = [
        "feat: normal commit",
        "Grain: MED/refactor -- prev: MED/refactor #13473",
    ]
    v = vpg.check(
        "Grain: MED/refactor -- lane x:y -- prev: MED/refactor #13473",
        commits=commits,
        current_pr=13473,
        prev_targets={"13473": {"kind": "pr", "merged": True}},
    )
    assert v["guard_pass"] is False
    kinds_by_loc = {(h["location"], h["kind"]) for h in v["hits"]["prev_invalid"]}
    assert ("body", "prev-self") in kinds_by_loc
    assert ("commits[1]", "prev-self") in kinds_by_loc


def test_prev_self_abstains_when_current_pr_unknown():
    # FN-safety: when the caller didn't tell us who we are, the gate must
    # NOT block on PREV-SELF (we can't evaluate identity). The original
    # (a)-only behaviour is the silent backstop; broadening the silent
    # zone is worse than partial coverage.
    v = vpg.check(
        "Grain: MED/refactor -- prev: MED/refactor #99999"
        # NOTE: no `current_pr=` keyword -> abstention on PREV-SELF.
    )
    assert v["guard_pass"] is True


def test_prev_not_merged_blocks():
    # #13473 measured: `prev: feat/notebook #13465` on PR #13473, where
    # #13465 was OPEN at the time of the tag (the predecessor is a moving
    # target whose genre could still change before merge).
    v = vpg.check(
        "Grain: feat/module -- lane myia-po-2026:CoursIA "
        "-- prev: feat/notebook #13465",
        current_pr=13473,
        prev_targets={"13465": {"kind": "pr", "merged": False}},
    )
    assert v["guard_pass"] is False
    assert any(h["kind"] == "prev-not-merged" and h["prev_pr"] == 13465
               for h in v["hits"]["prev_invalid"])


def test_prev_not_pr_blocks():
    # #13439 measured: `prev: MED/refactor #13436` where #13436 is an
    # ISSUE (never mergeable). The cap silently compared the grain to a
    # target whose genre was structurally unevaluable.
    v = vpg.check(
        "Grain: MED/guard -- lane myia-po-2026:CoursIA "
        "-- prev: MED/refactor #13436",
        current_pr=13439,
        prev_targets={"13436": {"kind": "issue"}},
    )
    assert v["guard_pass"] is False
    assert any(h["kind"] == "prev-not-pr" and h["prev_pr"] == 13436
               for h in v["hits"]["prev_invalid"])


def test_prev_not_pr_or_merged_abstains_when_metadata_missing():
    # FN-safety: a target the workflow couldn't resolve (network blip,
    # rate-limit, gh 404 on a draft PR) must NOT be flagged. The
    # silent-acceptance defect that #13475 measures is at the
    # SUFFICIENT-information end (the metadata is right there, we just
    # didn't read it) -- not at the unresolvable end.
    v = vpg.check(
        "Grain: MED/refactor -- lane x:y -- prev: MED/refactor #99999",
        current_pr=100,
        prev_targets={},  # metadata intentionally absent
    )
    assert v["guard_pass"] is True


def test_prev_invalid_clean_tag_passes():
    # The baseline: a sane tag (`prev:` points at a MERGED PR distinct
    # from the current one) passes BOTH invariants (a) and (b).
    v = vpg.check(CLEAN_PREV_BODY, current_pr=13918,
                  prev_targets=CLEAN_PREV_TARGETS)
    assert v["guard_pass"] is True
    assert v["hits"] == {"body": [], "commits": [], "prev_invalid": []}


def test_combined_close_keyword_and_prev_self_reports_both():
    # (a) and (b) defects in the same tag -- the verdict surfaces BOTH so
    # the worker fixes both in one edit instead of being told only one and
    # discovering the other at re-run.
    v = vpg.check(
        "Grain: MED/fix -- lane x:y -- prev: MED/fix #13465",
        current_pr=13465,
        prev_targets={"13465": {"kind": "pr", "merged": False}},
    )
    assert v["guard_pass"] is False
    assert any(h["genre"] == "fix" for h in v["hits"]["body"])
    assert any(h["kind"] == "prev-self" for h in v["hits"]["prev_invalid"])
    assert any(h["kind"] == "prev-not-merged" for h in v["hits"]["prev_invalid"])
    # Both reasons appear in the human-readable summary.
    assert "closing keywords" in v["reason"]
    assert "invariant" in v["reason"]


def test_find_prev_self_references_helper():
    # Helper-level test: the regex pulls every `prev: ... #N` whose #N
    # equals `current_pr`, even when multiple `prev:` clauses coexist
    # (multi-grain body -- extremely rare but the regex must not stop at
    # the first hit).
    text = (
        "Grain: MED/refactor -- lane x:y\n"
        "previous body. prev: MED/refactor #1\n"
        "Then a self-ref: prev: LIGHT/refactor #99999\n"
        "And a clean one: prev: DEEP/lean #2"
    )
    hits = vpg.find_prev_self_references(text, current_pr=99999)
    assert len(hits) == 1
    assert hits[0]["prev_pr"] == 99999
    assert "prev: LIGHT/refactor #99999" in hits[0]["match"]


def test_find_prev_target_pr_numbers_helper():
    # Helper: deduplicates and respects the `prev:` prefix (a `Refs #5`
    # outside `prev:` is NOT a target).
    text = (
        "Grain: MED/refactor -- lane x:y -- prev: MED/refactor #5\n"
        "Refs #5 (a sibling ref, not a target).\n"
        "Also prev: MED/guard #5\n"   # same #5, dedup
        "And prev: DEEP/lean #7"
    )
    targets = vpg.find_prev_target_pr_numbers(text)
    assert targets == [5, 7]


def test_validate_prev_targets_helper():
    # Helper: builds the right hit dict per kind.
    targets = [1, 2, 3]
    meta = {
        "1": {"kind": "pr", "merged": True},     # clean
        "2": {"kind": "pr", "merged": False},    # PREV-NOT-MERGED
        "3": {"kind": "issue"},                  # PREV-NOT-PR
        # "4" absent on purpose -> abstain
    }
    hits = vpg.validate_prev_targets(targets, meta, location="body")
    kinds = sorted(h["kind"] for h in hits)
    assert kinds == ["prev-not-merged", "prev-not-pr"]


def test_prev_invalid_check_unaffected_by_existing_close_keyword_tests():
    # Regression guard for the #10093 surface: the original invariants
    # still fire when only `prev_targets` is passed. This pins the fact
    # that the extension is ADDITIVE -- it doesn't break the existing
    # close-keyword detection.
    v = vpg.check(
        "Grain: MED/fix -- lane x:y -- prev: MED/fix #100",
        current_pr=200,
        prev_targets={"100": {"kind": "pr", "merged": True}},
    )
    assert v["guard_pass"] is False
    assert any(h["genre"] == "fix" for h in v["hits"]["body"])
    # PREV-SELF is NOT flagged (current_pr=200, prev=#100, distinct).
    assert not any(h["kind"] == "prev-self" for h in v["hits"]["prev_invalid"])
