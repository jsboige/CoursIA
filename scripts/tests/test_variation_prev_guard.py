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
import json
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


# ---------------------------------------------------------------------------
# resolve_prev_targets -- the half of #13475 that had no test, and was wrong.
#
# The workflow used to ask `gh pr view N --json state,merged`. `merged` is not
# a field this `gh` exposes, so the call failed for EVERY target, fell through
# to `gh issue view` (which answers for pull requests too), and returned
# `kind="issue"` for every PR -- making `prev-not-pr` fire on 100 % of PRs,
# this one included (#13922 blocked on `prev-not-pr -> [14225]`, while #14225
# is a PR merged at 2026-09-03T10:28:59Z).
#
# `FakeGh` replays the three classes measured on this repo on 2026-09-03.
# Every test below is a positive control: each asserts a DIFFERENT verdict, so
# a resolver that collapses the classes (which is exactly what the defect did)
# cannot pass them all.
# ---------------------------------------------------------------------------

class _Completed:
    def __init__(self, returncode, stdout="", stderr=""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


class FakeGh:
    """Replay `gh` for a fixed world of numbers, faithful to the real CLI.

    `world` maps a number to `("pr", "MERGED")`, `("pr", "OPEN")`, or
    `("issue", "OPEN")`. Two real behaviours are reproduced because both
    matter to the resolver's correctness:

      * an **unknown --json field** makes `gh pr view` exit 1 with
        `Unknown JSON field: "<name>"` -- this is what killed the original;
      * `gh issue view` **succeeds on pull requests**, so it can never be
        the discriminant between the two kinds.
    """

    #: fields this fake `gh pr view` knows about (mirrors the real one).
    PR_FIELDS = {"state", "number", "title", "mergedAt"}

    def __init__(self, world):
        self.world = world
        self.calls = []

    def __call__(self, argv, capture_output=True, text=True, timeout=None):
        self.calls.append(list(argv))
        _gh, verb, _view, number, _json_flag, fields = argv[:6]
        n = int(number)
        requested = set(fields.split(","))
        kind, state = self.world.get(n, (None, None))
        if verb == "pr":
            unknown = requested - self.PR_FIELDS
            if unknown:
                return _Completed(1, "", 'Unknown JSON field: "%s"\n'
                                  % sorted(unknown)[0])
            if kind != "pr":
                return _Completed(
                    1, "",
                    "GraphQL: Could not resolve to a PullRequest with the "
                    "number of %d. (repository.pullRequest)\n" % n)
            return _Completed(0, json.dumps({"state": state}))
        # `gh issue view` answers for issues AND pull requests.
        if kind is None:
            return _Completed(1, "", "GraphQL: Could not resolve to an "
                                     "Issue with the number of %d.\n" % n)
        return _Completed(0, json.dumps({"state": state}))


WORLD = {14225: ("pr", "MERGED"),      # merged PR   -> the #13922 witness
         13922: ("pr", "OPEN"),        # open PR
         14513: ("issue", "OPEN")}     # issue


def test_resolve_prev_targets_merged_pr_is_a_merged_pr():
    gh = FakeGh(WORLD)
    assert vpg.resolve_prev_targets([14225], runner=gh) == {
        "14225": {"kind": "pr", "merged": True}}
    # PR-first ordering: the issue endpoint is never consulted for a PR.
    assert [c[1] for c in gh.calls] == ["pr"]


def test_resolve_prev_targets_open_pr_is_a_pr_not_merged():
    assert vpg.resolve_prev_targets([13922], runner=FakeGh(WORLD)) == {
        "13922": {"kind": "pr", "merged": False}}


def test_resolve_prev_targets_issue_is_an_issue():
    gh = FakeGh(WORLD)
    assert vpg.resolve_prev_targets([14513], runner=gh) == {
        "14513": {"kind": "issue"}}
    # Both endpoints were tried, in that order.
    assert [c[1] for c in gh.calls] == ["pr", "issue"]


def test_resolve_prev_targets_unresolvable_target_is_omitted():
    # Neither endpoint resolves -> absent from the dict -> validate_prev_targets
    # abstains. A lookup failure must never become an accusation.
    assert vpg.resolve_prev_targets([999999], runner=FakeGh(WORLD)) == {}


def test_issue_view_alone_cannot_discriminate_a_pr_from_an_issue():
    # Pins WHY the resolver must call `gh pr view` first: the issue endpoint
    # answers identically for #14225 (a PR) and #14513 (an issue). Any future
    # rewrite that reorders the two calls fails here.
    gh = FakeGh(WORLD)
    pr_answer = gh(["gh", "issue", "view", "14225", "--json", "state"])
    issue_answer = gh(["gh", "issue", "view", "14513", "--json", "state"])
    assert pr_answer.returncode == issue_answer.returncode == 0
    assert "state" in json.loads(pr_answer.stdout)
    assert "state" in json.loads(issue_answer.stdout)


def test_original_state_merged_field_set_misclassifies_a_merged_pr():
    r"""The defect, reproduced -- and the reason this test file exists.

    This replays the ORIGINAL algorithm verbatim (ask for ``state,merged``,
    accept the payload only if it carries a ``merged`` key, else fall back to
    ``gh issue view``) against the same fake `gh`. It returns ``issue`` for
    #14225 -- a PR merged at 2026-09-03T10:28:59Z -- which is precisely the
    verdict that blocked #13922 on ``prev-not-pr -> [14225]``.

    Kept as an executable record: it fails the moment someone reintroduces a
    non-existent field into the query.
    """
    gh = FakeGh(WORLD)

    def original_algorithm(n):
        pr = gh(["gh", "pr", "view", str(n), "--json", "state,merged"])
        if pr.returncode == 0:
            payload = json.loads(pr.stdout)
            if "merged" in payload:
                return {"kind": "pr", "merged": bool(payload["merged"])}
        issue = gh(["gh", "issue", "view", str(n), "--json", "state"])
        if issue.returncode == 0 and "state" in json.loads(issue.stdout):
            return {"kind": "issue"}
        return None

    assert original_algorithm(14225) == {"kind": "issue"}          # the defect
    assert vpg.resolve_prev_targets([14225], runner=FakeGh(WORLD)) == {
        "14225": {"kind": "pr", "merged": True}}                   # the repair


def test_check_passes_on_a_prev_pointing_at_a_resolved_merged_pr():
    # End-to-end shape of the #13922 tag once the resolver is correct.
    body = ("Grain: MED/guard -- lane myia-po-2026:CoursIA -- "
            "prev: LIGHT/cleanup #14225")
    targets = vpg.resolve_prev_targets(
        vpg.find_prev_target_pr_numbers(body), runner=FakeGh(WORLD))
    v = vpg.check(body, current_pr=13922, prev_targets=targets)
    assert v["hits"]["prev_invalid"] == []
    assert v["guard_pass"] is True


# --------------------------------------------------------------------------
# #14550 -- a `prev:` clause inside backticks is a CITATION, not a declaration
# --------------------------------------------------------------------------

# Shape of the real #14559 body: a valid tag pointing at a MERGED PR, and a
# quoted tag of ANOTHER grain in the prose. Before the fix, the quotation won:
# `finditer` swept the whole body, found #14548 (still open), and the guard
# rejected the PR on `prev-not-merged` -- accusing a lane of a defect it had
# taken care to avoid.
CITING_BODY = (
    "Grain: DEEP/research-code -- lane myia-po-2026:CoursIA-2 -- "
    "prev: DEEP/research-code #14501\n"
    "\n"
    "## Cause instrumentale\n"
    "Le meme defaut que NanoClaw a nomme sur `Grain: MED/qc -- lane a:b -- "
    "prev: MED/qc #14548` : `play_round` echantillonne `x` puis le jette.\n"
)


def test_backticked_prev_is_a_citation_not_a_declaration():
    # The real #14559 case. `prev:` is declared at #14501 (merged); the body
    # also QUOTES another lane's tag pointing at #14548 (open).
    targets = {"14501": {"kind": "pr", "merged": True},
               "14548": {"kind": "pr", "merged": False}}
    v = vpg.check(CITING_BODY, current_pr=14559, prev_targets=targets)
    assert 14548 not in vpg.find_prev_target_pr_numbers(CITING_BODY)
    assert v["hits"]["prev_invalid"] == []
    assert v["guard_pass"] is True


def test_backticked_self_reference_does_not_trip_prev_self():
    # Symmetric half: quoting a tag that happens to name the CURRENT PR is
    # documentation, not a self-reference.
    body = ("Grain: MED/guard -- lane myia-ai-01:CoursIA -- prev: MED/test #14501\n"
            "Le garde a rejete `prev: MED/guard #4242` sur cette PR.\n")
    assert vpg.find_prev_self_references(body, 4242) == []


def test_fenced_block_is_masked_too():
    body = ("Grain: MED/guard -- lane a:b -- prev: MED/guard #14501\n"
            "```\n"
            "Grain: MED/qc -- lane c:d -- prev: MED/qc #14548\n"
            "```\n")
    assert vpg.find_prev_target_pr_numbers(body) == [14501]


def test_plain_prev_at_an_open_pr_still_fails():
    # NEGATIVE CONTROL -- the invariant is not weakened. A `prev:` written in
    # plain text (the canonical tag) at a still-open PR must still be rejected.
    body = "Grain: MED/guard -- lane a:b -- prev: MED/guard #14548"
    v = vpg.check(body, current_pr=99999,
                  prev_targets={"14548": {"kind": "pr", "merged": False}})
    assert v["hits"]["prev_invalid"] == [
        {"location": "body", "kind": "prev-not-merged", "prev_pr": 14548}]
    assert v["guard_pass"] is False


def test_plain_prev_self_still_fails():
    # NEGATIVE CONTROL -- prev-self stays blocking.
    body = "Grain: MED/guard -- lane a:b -- prev: MED/guard #4242"
    v = vpg.check(body, current_pr=4242)
    assert v["guard_pass"] is False


def test_fully_backticked_tag_is_still_evaluated():
    # BLIND-SPOT CONTROL -- this is what `_declared_prev_pr` exists for.
    #
    # Masking alone would hand any lane a trivial bypass: wrap the tag line in
    # backticks and every `prev:` invariant goes silent. `grain_tag.parse_prev`
    # strips backticks before reading, so the DECLARATION is unioned back in.
    # Remove that union and this test goes green in the wrong direction.
    body = "`Grain: MED/guard -- lane a:b -- prev: MED/guard #14548`\nSuite."
    assert vpg.find_prev_target_pr_numbers(body) == [14548]
    v = vpg.check(body, current_pr=99999,
                  prev_targets={"14548": {"kind": "pr", "merged": False}})
    assert v["guard_pass"] is False
