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
# Insert `scripts/` too: the mask under test lives in grain_tag since #14780.
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import grain_tag as gt  # noqa: E402
import variation_prev_guard as vpg  # noqa: E402


CLEAN_BODY = "Grain: MED/tooling -- lane myia-po-2025:CoursIA-2 -- prev: MED/infra #10067"


def test_clean_body_passes():
    v = vpg.check(CLEAN_BODY)
    assert v["guard_pass"] is True
    assert v["hits"] == {"body": [], "commits": [], "prev_invalid": []}


def test_green_verdict_names_accepted_prev_targets():
    """#15372 : le verdict vert cite les cibles prev: acceptees -- la
    levee de commentaire du garde les nomme pour que le remplacement du
    mur affiche ce qui fait tenir le vert."""
    v = vpg.check(CLEAN_BODY)
    assert v["guard_pass"] is True
    assert v["prev_targets_accepted"] == [10067]
    # Un body sans prev: reste vert avec une liste vide, pas une absence.
    v2 = vpg.check("Grain: LIGHT/docs -- lane myia-po-2023:CoursIA")
    assert v2["guard_pass"] is True
    assert v2["prev_targets_accepted"] == []


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
CLEAN_PREV_TARGETS = {"13826": {"kind": "pr", "state": "MERGED",
                                "merged": True}}


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


def test_prev_self_in_commit_message_does_not_block():
    # INVERSE depuis #15309 (4e axe, arbitrage ai-01 2026-09-12T03:36Z) : les
    # invariants `prev:` s'evaluent sur le BODY SEUL, la surface declarative
    # du §1 de variation-protocol.md. Le precedent #10093 (squash-merge
    # publie les messages de commit) reste valable pour les CLOSE-KEYWORDS --
    # la, la surface est le mecanisme -- mais pas pour `prev:` : corriger un
    # `prev:` de commit exige une reecriture d'historique, le geste que
    # git-workflow.md presente comme dernier recours. Un garde n'exige pas,
    # pour etre satisfait, un geste que la regle voisine decourage.
    # Ce test etait l'assertion inverse (commits[1] prev-self bloquant)
    # avant #15309 ; il epingle desormais la non-remontee de la surface
    # commits, et le maintien du blocage cote body.
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
    assert not any(loc.startswith("commits[") for loc, _ in kinds_by_loc)


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


# Invariant 2 is a THREE-way discrimination, and the three cases must be
# pinned together: a predicate tested only on its blocking case cannot be
# distinguished from one that blocks on everything. That is exactly how the
# original shipped -- `test_prev_not_merged_blocks` asserted the CLOSED
# verdict while feeding it an OPEN target, and nothing in the suite said
# the two were different.

_ABANDONED_BODY = ("Grain: MED/guard -- lane myia-ai-01:CoursIA "
                   "-- prev: MED/guard #13465")


def test_prev_abandoned_blocks():
    # CLOSED without merging: the declared lineage was given up. Nothing it
    # carries will ever reach `main`, so adjacency is measured against a
    # grain that does not exist there. This is the defect invariant 2 aims at.
    v = vpg.check(_ABANDONED_BODY, current_pr=13473,
                  prev_targets={"13465": {"kind": "pr", "state": "CLOSED",
                                          "merged": False}})
    assert v["guard_pass"] is False
    assert any(h["kind"] == "prev-abandoned" and h["prev_pr"] == 13465
               for h in v["hits"]["prev_invalid"])


def test_prev_open_abstains_the_predecessor_is_in_flight():
    # THE REPAIR. Same body, same current PR, ONE field different -- and the
    # verdict flips. A predecessor still open is not a broken lineage: it is
    # the state R1 of `proactive-coordination.md` mandates ("1 PR entre 2
    # wakeups = PLANCHER, jamais plafond -- re-pioche IMMEDIATEMENT").
    #
    # The witness the original invariant cited, #13473, was tagged
    # `prev: ... #13465` while #13465 was OPEN -- and it MERGED on
    # 2026-08-29 without anyone touching the tag. A "defect" that resolves
    # itself when its predecessor lands is a transient state, not a defect.
    v = vpg.check(_ABANDONED_BODY, current_pr=13473,
                  prev_targets={"13465": {"kind": "pr", "state": "OPEN",
                                          "merged": False}})
    assert v["guard_pass"] is True
    assert v["hits"]["prev_invalid"] == []


def test_prev_merged_passes():
    # The third state, kept explicit rather than left implicit in the
    # end-to-end tests: MERGED is clean, and it must be clean for a REASON
    # the suite states, not as a by-product of no other branch firing.
    v = vpg.check(_ABANDONED_BODY, current_pr=13473,
                  prev_targets={"13465": {"kind": "pr", "state": "MERGED",
                                          "merged": True}})
    assert v["guard_pass"] is True


def test_legacy_meta_without_state_abstains_it_cannot_tell_open_from_closed():
    # BACKWARD-COMPAT / FN-SAFETY. A hand-written or pre-#13475-repair
    # `--prev-targets-file` carries only `merged`. `merged: False` covers
    # BOTH open and closed, so the predicate has insufficient information
    # and must abstain rather than guess -- the same contract as an
    # unresolved target. `test_resolver_always_emits_state_for_a_pr` is
    # what keeps this an edge case instead of the silent norm.
    v = vpg.check(_ABANDONED_BODY, current_pr=13473,
                  prev_targets={"13465": {"kind": "pr", "merged": False}})
    assert v["guard_pass"] is True
    assert v["hits"]["prev_invalid"] == []


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
        prev_targets={"13465": {"kind": "pr", "state": "CLOSED",
                                "merged": False}},
    )
    assert v["guard_pass"] is False
    assert any(h["genre"] == "fix" for h in v["hits"]["body"])
    assert any(h["kind"] == "prev-self" for h in v["hits"]["prev_invalid"])
    assert any(h["kind"] == "prev-abandoned" for h in v["hits"]["prev_invalid"])
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
    # Helper: the full verdict table in one place. Two of the five rows are
    # CLEAN and two are ABSTENTIONS -- a table listing only the blocking
    # rows would pass under a predicate that blocks on everything.
    targets = [1, 2, 3, 4, 5]
    meta = {
        "1": {"kind": "pr", "state": "MERGED", "merged": True},   # clean
        "2": {"kind": "pr", "state": "CLOSED", "merged": False},  # ABANDONED
        "3": {"kind": "issue", "state": "OPEN"},                  # NOT-PR
        "4": {"kind": "pr", "state": "OPEN", "merged": False},    # in flight
        "5": {"kind": "pr", "merged": False},                     # legacy
        # "6" absent on purpose -> abstain (unresolved)
    }
    hits = vpg.validate_prev_targets(targets + [6], meta, location="body")
    assert sorted(h["kind"] for h in hits) == ["prev-abandoned", "prev-not-pr"]
    assert sorted(h["prev_pr"] for h in hits) == [2, 3]


def test_prev_invalid_check_unaffected_by_existing_close_keyword_tests():
    # Regression guard for the #10093 surface: the original invariants
    # still fire when only `prev_targets` is passed. This pins the fact
    # that the extension is ADDITIVE -- it doesn't break the existing
    # close-keyword detection.
    v = vpg.check(
        "Grain: MED/fix -- lane x:y -- prev: MED/fix #100",
        current_pr=200,
        prev_targets={"100": {"kind": "pr", "state": "MERGED",
                              "merged": True}},
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
         13922: ("pr", "OPEN"),        # open PR     -> in flight, clean
         13999: ("pr", "CLOSED"),      # closed PR   -> abandoned, blocking
         14513: ("issue", "OPEN")}     # issue


def test_resolve_prev_targets_merged_pr_is_a_merged_pr():
    gh = FakeGh(WORLD)
    assert vpg.resolve_prev_targets([14225], runner=gh) == {
        "14225": {"kind": "pr", "state": "MERGED", "merged": True}}
    # PR-first ordering: the issue endpoint is never consulted for a PR.
    assert [c[1] for c in gh.calls] == ["pr"]


def test_resolve_prev_targets_open_pr_is_a_pr_not_merged():
    assert vpg.resolve_prev_targets([13922], runner=FakeGh(WORLD)) == {
        "13922": {"kind": "pr", "state": "OPEN", "merged": False}}


def test_resolve_prev_targets_closed_pr_is_distinguishable_from_an_open_one():
    # The whole point of surfacing `state` (2026-09-08). Before it, both an
    # OPEN and a CLOSED PR came back as `merged: False` -- one dict, two
    # situations, and `validate_prev_targets` was structurally unable to
    # tell a predecessor still in flight from an abandoned one. The pair of
    # assertions below IS the repair: same `kind`, same `merged`, and the
    # only field that differs is the one the invariant now reads.
    closed = vpg.resolve_prev_targets([13999], runner=FakeGh(WORLD))
    opened = vpg.resolve_prev_targets([13922], runner=FakeGh(WORLD))
    assert closed == {"13999": {"kind": "pr", "state": "CLOSED",
                                "merged": False}}
    assert closed["13999"]["merged"] == opened["13922"]["merged"], \
        "`merged` alone cannot separate the two -- that is the defect"
    assert closed["13999"]["state"] != opened["13922"]["state"]


def test_resolve_prev_targets_issue_is_an_issue():
    gh = FakeGh(WORLD)
    assert vpg.resolve_prev_targets([14513], runner=gh) == {
        "14513": {"kind": "issue", "state": "OPEN"}}
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
        "14225": {"kind": "pr", "state": "MERGED",
                  "merged": True}}                                # the repair


def test_resolver_always_emits_state_for_every_pr_kind_it_returns():
    """Keeps the `state`-less abstention an EDGE case, never the norm.

    `validate_prev_targets` abstains on a PR-kind meta carrying no `state`,
    because it cannot tell OPEN from CLOSED and must not guess. That
    abstention is a courtesy to hand-written and legacy fixtures -- if the
    real resolver ever stopped emitting `state`, the same code path would
    silently turn invariant 2 off across the whole fleet, and every test
    above would still be green. This is the control that would go red.
    """
    resolved = vpg.resolve_prev_targets(sorted(WORLD), runner=FakeGh(WORLD))
    assert len(resolved) == len(WORLD), "fixture inerte: rien resolu"
    without = [n for n, meta in resolved.items() if not meta.get("state")]
    assert not without, "resolver emitted a PR meta with no state: %s" % without


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
# `finditer` swept the whole body, found #14548, and the guard rejected the
# PR on the cited grain's target -- accusing a lane of a defect it had taken
# care to avoid.
#
# NOTE (2026-09-08, invariant-2 repair): #14548 was OPEN in the real
# incident, and OPEN was what made the leak visible back then. Since an OPEN
# target no longer blocks, every fixture in this section holds it CLOSED
# instead: the teeth of these tests are "a mask leak turns into a block",
# and that only stays true if the leaked target is one the current predicate
# rejects. Left at OPEN, the assertions below would pass on a totally broken
# mask.
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
    # also QUOTES another lane's tag pointing at #14548 (abandoned -- see
    # the section NOTE: it was OPEN in the incident, and OPEN no longer
    # blocks, so the leak has to land on a state that does).
    targets = {"14501": {"kind": "pr", "state": "MERGED", "merged": True},
               "14548": {"kind": "pr", "state": "CLOSED", "merged": False}}
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


# --------------------------------------------------------------------------
# #15932 -- the fence ABOVE the tag line. `test_fenced_block_is_masked_too`
# above only holds when the real tag line comes FIRST; the first-line race is
# what leaked.
# --------------------------------------------------------------------------

# Shape of the real #15925 body (compressed): the reproduction block is a
# `python` fence whose first statement quotes a defective tag verbatim, and it
# sits ABOVE the author's own trailer. `_first_grain_line` took the first
# `Grain:` substring it met -- inside the fence -- so `_declared_prev_pr`
# returned the QUOTE's target (15832, CLOSED/unmerged) instead of the real
# trailer (15924, OPEN), and the guard red-lit the PR with
# `prev-abandoned -> [15832]` on a predecessor the author never pointed at.
#
# The real trailer is held OPEN on purpose (the section NOTE convention): a
# leaking mask must turn this red, and only the CLOSED quote can do that. The
# teeth therefore sit entirely on the mask, not on the predicate.
FENCED_CITATION_ABOVE_TAG = (
    "## Reproduction\n"
    "```python\n"
    'body = "Grain: MED/lean -- lane myia-x:CoursIA -- prev: MED/lean #15832"\n'
    "vpg.check(body, [], current_pr=15869, prev_targets=meta)\n"
    "```\n"
    "\n"
    "## Suite\n"
    "Grain: LIGHT/tooling -- lane myia-po-2023:CoursIA -- prev: MED/tooling #15924\n"
)

FENCED_CITATION_TARGETS = {
    "15832": {"kind": "pr", "state": "CLOSED", "merged": False},
    "15924": {"kind": "pr", "state": "OPEN", "merged": False},
}


def test_fenced_citation_above_the_tag_line_is_not_a_declaration():
    # The #15932 defect, first-hand.
    assert vpg._declared_prev_pr(FENCED_CITATION_ABOVE_TAG) == 15924
    assert 15832 not in vpg.find_prev_target_pr_numbers(FENCED_CITATION_ABOVE_TAG)
    v = vpg.check(FENCED_CITATION_ABOVE_TAG, current_pr=15925,
                  prev_targets=FENCED_CITATION_TARGETS)
    assert v["hits"]["prev_invalid"] == []
    assert v["guard_pass"] is True


def test_fenced_citation_does_not_trip_prev_self():
    # Symmetric half: the quote names the CURRENT PR (mine-po-2023's body
    # quotes it with `current_pr=15869`), which must not read as a
    # self-reference either -- `find_prev_self_references` falls back to
    # `_declared_prev_pr` (l.281), the same function that leaked.
    assert vpg.find_prev_self_references(FENCED_CITATION_ABOVE_TAG, 15832) == []


def test_plain_citation_above_the_tag_line_still_fails():
    # NEGATIVE CONTROL -- the mask is not a blanket amnesty on the ORDER. The
    # SAME clause, written in plain text above the tag line, is a real
    # declaration and must still be rejected. This is the pair that proves
    # the pass above was earned by the fence.
    body = ("## Reproduction\n"
            "Grain: MED/lean -- lane myia-x:CoursIA -- prev: MED/lean #15832\n"
            "\n"
            "Grain: LIGHT/tooling -- lane myia-po-2023:CoursIA -- prev: MED/tooling #15924\n")
    assert vpg._declared_prev_pr(body) == 15832
    v = vpg.check(body, current_pr=15925, prev_targets=FENCED_CITATION_TARGETS)
    assert v["hits"]["prev_invalid"] == [
        {"location": "body", "kind": "prev-abandoned", "prev_pr": 15832}]
    assert v["guard_pass"] is False


def test_mask_fenced_blocks_keeps_the_inline_span_surface():
    # The narrow mask is the whole point (#15932): a fully backticked tag line
    # must SURVIVE it, or `test_fully_backticked_tag_is_still_evaluated`'s
    # blind-spot control becomes a silent bypass -- a lane would wrap its tag
    # in backticks and every `prev:` invariant would go quiet.
    backticked = "`Grain: MED/guard -- lane a:b -- prev: MED/guard #14548`\n"
    assert gt.mask_fenced_blocks(backticked) == backticked
    # ... while the WIDE mask does blank it (that is why the two are split).
    assert "14548" not in gt.mask_code_spans(backticked)


def test_mask_fenced_blocks_shape_and_both_fence_characters():
    fenced = "avant\n```python\nGrain: MED/qc -- prev: MED/qc #14548\n```\napres\n"
    masked = gt.mask_fenced_blocks(fenced)
    assert "14548" not in masked
    assert len(masked) == len(fenced)
    lines = masked.splitlines()
    assert len(lines) == len(fenced.splitlines())
    assert lines[0] == "avant" and lines[-1] == "apres"
    # every line of the fence is blanked to the SAME length as its original
    assert all(l == " " * len(o) for l, o in zip(lines[1:-1], fenced.splitlines()[1:-1]))
    # `~~~` is a fence too, and an UNCLOSED fence masks to the end -- which is
    # exactly what GitHub renders, so what a reviewer sees.
    assert "14548" not in gt.mask_fenced_blocks("avant\n~~~\nGrain: a:b -- prev: a #14548\n")
    # A 4-space indented block is deliberately NOT masked (nested lists carry
    # legitimate markers there -- see check_lane_claim's scope note).
    assert gt.mask_fenced_blocks("    Grain: a:b -- prev: a #14548\n") == \
        "    Grain: a:b -- prev: a #14548\n"


def test_plain_prev_at_an_abandoned_pr_still_fails():
    # NEGATIVE CONTROL -- the mask is not a blanket amnesty. The SAME clause
    # as the citation above, written in plain text (the canonical tag), at
    # the SAME target, must still be rejected. This is the pair that proves
    # the pass above was earned by the backticks, and not by a target the
    # predicate waves through anyway.
    body = "Grain: MED/guard -- lane a:b -- prev: MED/guard #14548"
    v = vpg.check(body, current_pr=99999,
                  prev_targets={"14548": {"kind": "pr", "state": "CLOSED",
                                          "merged": False}})
    assert v["hits"]["prev_invalid"] == [
        {"location": "body", "kind": "prev-abandoned", "prev_pr": 14548}]
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
    #
    # The union is what this measures, so the target must be one the
    # predicate rejects (section NOTE): held CLOSED, a lost union turns the
    # red into a green and the test speaks. Held OPEN it would be silent.
    body = "`Grain: MED/guard -- lane a:b -- prev: MED/guard #14548`\nSuite."
    assert vpg.find_prev_target_pr_numbers(body) == [14548]
    v = vpg.check(body, current_pr=99999,
                  prev_targets={"14548": {"kind": "pr", "state": "CLOSED",
                                          "merged": False}})
    assert v["guard_pass"] is False


def test_prose_citation_without_grain_line_is_not_a_declaration():
    # c.966 -- the false positive that blocked PR #14592.
    #
    # Real shape: `b974f2721` (c.957 REPAIR P0) carries a body that
    # DOCUMENTS the bug in prose, citing ``prev: MED/training #14592``
    # in backticks inside a numbered list. The text carries NO `Grain:`
    # line at all (it's a normal commit message, not a worker-authored
    # grain). The previous `_declared_prev_pr` passed the WHOLE body to
    # `grain_tag.parse_prev`, which matched the prose citation and reported
    # `prev: #14592` -- then PREV-SELF / PREV-NOT-MERGED fired (that
    # second invariant is named PREV-ABANDONED since 2026-09-08; the old
    # name is kept here because it is what the incident report said).
    #
    # After the fix, the search is BOUNDED to the first `Grain:` line:
    # absent -> None -> no declaration -> no false positive.
    commit_body = (
        "fix(guards): REPAIR P0-4 M17 HAR-LJ-Asym BTC round-4\n"
        "\n"
        "## Concerns verbatim (round-4)\n"
        "\n"
        "5. `prev: MED/training #14592` was self-rouge. `prev:` now points "
        "at `MED/refactor #14456` (MERGED 2026-09-03T12:00:08Z).\n"
    )
    # The PREV-SELF that blocked the PR fired because parse_prev
    # returned 14592 = current_pr. With the bounded search, no `Grain:`
    # line exists, so the fallback never matches -> no hit.
    assert vpg._declared_prev_pr(commit_body) is None
    v = vpg.check(commit_body, current_pr=14592)
    assert v["hits"]["prev_invalid"] == []
    assert v["guard_pass"] is True


def test_prose_citation_after_tag_line_still_evaluates_tag():
    # c.966 -- the OTHER prose shape: a body that has BOTH a tag line AND
    # a prose citation of another grain's `prev:`. The bounded search
    # must return the TAG's `prev:`, not the prose citation's.
    body = (
        "Grain: MED/guard -- lane a:b -- prev: MED/guard #14501\n"
        "\n"
        "## Cause instrumentale\n"
        "Le meme defaut que `prev: MED/qc #14548` documentait sur #14548.\n"
    )
    assert vpg._declared_prev_pr(body) == 14501
    # #14548 held CLOSED for the same reason as the section NOTE: if the
    # bounded search ever regressed to the prose citation, the verdict must
    # go red rather than stay quietly green.
    targets = {"14501": {"kind": "pr", "state": "MERGED", "merged": True},
               "14548": {"kind": "pr", "state": "CLOSED", "merged": False}}
    v = vpg.check(body, current_pr=99999, prev_targets=targets)
    assert v["hits"]["prev_invalid"] == []
    assert v["guard_pass"] is True


def test_first_grain_line_helper_bounds_search():
    # c.966 -- unit-level coverage of the bounded search.
    assert vpg._first_grain_line(None) is None
    assert vpg._first_grain_line("") is None
    assert vpg._first_grain_line("no tag here\n") is None
    tag_line = "Grain: DEEP/training -- lane x:y -- prev: DEEP/training #7"
    assert vpg._first_grain_line(tag_line) == tag_line
    multiline = (
        "The `Grain:` field is mandatory on every worker PR.\n"
        "See the variation-protocol for the canonical form.\n"
    )
    # Returns the prose line (still has `Grain:` substring), but
    # `parse_prev` on it returns pr_number=None -> safe.
    assert vpg._first_grain_line(multiline) == multiline.split("\n")[0]
    assert vpg._declared_prev_pr(multiline) is None


# --------------------------------------------------------------------------
# #14700 -- a backtick span ACROSS a soft line break must still be one mask
# --------------------------------------------------------------------------
#
# The defect that blocked PR #14700 on its own `` commits[0] ``:
#
#     L4: ... citing `prev: MED/training
#     L5: #14592` in backticks inside a numbered list ...
#
# The previous regex `` `[^`\\n]*` `` forbade newlines, so the closing
# backtick at the start of L5 was orphaned and the L5 half escaped the
# mask. `` _PREV_PR_REF_RE `` then matched `` #14592 `` and fired
# `` prev-abandoned -> [14592] `` -- on the PR whose own commit message
# documented the bug. The control in ai-01's analysis was exact: the same
# citation on a SINGLE line was correctly masked; the soft break was the
# only discriminant. We extend the span to allow `` \\n `` and pin the
# change with three tests -- the multi-line shape, the single-line shape
# (no regression), and the masked-selector parity for `` find_prev_self ``.

def test_multiline_backtick_span_is_one_mask():
    # The exact commit shape of PR #14700's `` commits[0] ``. The whole
    # `` `prev: MED/training\\n#14592` `` is ONE code span -- verified by
    # checking that `` _PREV_PR_REF_RE `` finds NOTHING inside the
    # masked text. Before the fix, `` #14592 `` leaked through L5.
    multiline = (
        "defect. The commit body documents the bug in prose, "
        "citing `prev: MED/training\n"
        "#14592` in backticks inside a numbered list, with NO `Grain:` "
        "line of its own."
    )
    masked = gt.mask_code_spans(multiline)
    # The whole span (L4 backtick + newline + L5 leading `#14592` + L5
    # backtick) is replaced by spaces -- nothing for the regex to match.
    assert "14592" not in masked
    # And the masked length preserves the original: the caller relies on
    # offset preservation to keep verdict slices meaningful.
    assert len(masked) == len(multiline)
    # PREV-SELF stays silent: the span is a citation, not a declaration.
    assert vpg.find_prev_self_references(multiline, current_pr=14592) == []
    # `` find_prev_target_pr_numbers `` also stays silent -- the cited
    # `` #14592 `` was inside a backtick span, so it isn't a target.
    assert vpg.find_prev_target_pr_numbers(multiline) == []


def test_single_line_backtick_span_still_masked():
    # NON-REGRESSION CONTROL. Same citation, on a single line -- this was
    # the working case BEFORE the fix and must remain working AFTER. If it
    # ever breaks, the fix has widened the regex too far.
    single = ("citing `prev: MED/training #14592` in backticks")
    masked = gt.mask_code_spans(single)
    assert "14592" not in masked
    assert len(masked) == len(single)
    assert vpg.find_prev_self_references(single, current_pr=14592) == []
    assert vpg.find_prev_target_pr_numbers(single) == []


def test_adjacent_backticks_do_not_merge_into_one_span():
    # EDGE-CASE CONTROL. Two separate backtick spans separated by ONE
    # newline (`` `a`\\n`b` ``) must remain TWO spans. If the regex
    # becomes greedy across ``\\n``, the two would merge and the
    # intervening ``\\n`` would be eaten by a single mask -- breaking
    # offset preservation for any code that lies between them. The
    # current regex is non-greedy and bounded by the FIRST closing
    # backtick, so they stay distinct.
    text = "`a`\n`b`"
    masked = gt.mask_code_spans(text)
    # Two spans masked independently -- `` `a` `` (3) + newline (1) +
    # `` `b` `` (3) -- total 7 chars, all blanks except the newline.
    assert masked == "   \n   "
    # Length preserved.
    assert len(masked) == len(text)


def test_fenced_block_with_internal_backticks_still_masked():
    # EDGE-CASE CONTROL. A fenced block containing `` `prev: ... #N` ``
    # on multiple lines is masked as ONE block (re.DOTALL + ``.*?``),
    # independent of the new multi-line inline behaviour. Verifies that
    # the fenced-block branch and the inline branch don't regress when
    # the inline span is widened.
    body = (
        "Grain: MED/guard -- lane a:b -- prev: MED/guard #14501\n"
        "```\n"
        "`prev: MED/qc #14548` on one line, and\n"
        "`prev: MED/qc #14549` on another.\n"
        "```\n"
    )
    # Only the tag's #14501 is a target; the in-block citations are masked.
    assert vpg.find_prev_target_pr_numbers(body) == [14501]


def test_multiline_backticked_citation_in_commit_passes_full_guard():
    # #14703 -- the issue's isolated control replayed at FULL GUARD level.
    # ai-01 measured the defect through the complete verdict path (the
    # organ's `prev_invalid` named ``commits[0]`` / the cited target /
    # 14592); the mask-level tests above pin the mechanism, this one pins
    # the end-to-end verdict the CI actually computes. The cited #14592 is
    # held CLOSED in ``prev_targets`` so a mask leak would turn into a
    # block -- the pass is earned by the mask, not by a target the current
    # predicate would wave through anyway. (It was OPEN when this test was
    # written; OPEN stopped blocking on 2026-09-08, which would have turned
    # the three assertions below into tautologies.)
    targets = {
        # the body's own prev
        "13826": {"kind": "pr", "state": "MERGED", "merged": True},
        # the cited-in-prose PR
        "14592": {"kind": "pr", "state": "CLOSED", "merged": False},
    }
    commit_two_line = (
        "fix(guard): document citation defect\n"
        "\n"
        "1. defect. The commit body documents the bug in prose, citing "
        "`prev: MED/training\n"
        "#14592` in backticks inside a numbered list, with NO Grain: "
        "line of its own.\n"
    )
    v = vpg.check(CLEAN_PREV_BODY, [commit_two_line],
                  current_pr=14703, prev_targets=targets)
    assert v["guard_pass"] is True
    assert v["hits"]["prev_invalid"] == []

    # NON-REGRESSION CONTROL: the same citation on a single line -- the
    # pre-fix working case, unchanged by the multi-line extension.
    commit_one_line = (
        "fix(guard): document citation defect\n"
        "\n"
        "1. defect. Citing `prev: MED/training #14592` in backticks.\n"
    )
    v = vpg.check(CLEAN_PREV_BODY, [commit_one_line],
                  current_pr=14703, prev_targets=targets)
    assert v["guard_pass"] is True
    assert v["hits"]["prev_invalid"] == []

    # TEETH CONTROL, deplace sur la surface BODY par #15309 (4e axe,
    # arbitrage ai-01 2026-09-12T03:36Z) : la meme clause nue SANS
    # backticks, dans le BODY cette fois, doit toujours bloquer -- la
    # surface ou les invariants `prev:` s'evaluent desormais. Avant
    # #15309, ce controle etait joue sur ``commits[0]`` ; la prescription
    # a retire la surface commits des invariants prev: (corriger un
    # message de commit exige une reecriture d'historique), donc la
    # preuve que le vert est MERITE par le masque se joue maintenant
    # cote body : si le masque regressait (regex `` `[^`\\n]*` `` de
    # pre-#14700), le ``#14592`` fuiterait du code span et ce bloc
    # rougirait.
    body_with_bare_wrapped = (
        "Grain: LIGHT/refactor -- lane myia-po-2026:CoursIA "
        "-- prev: LIGHT/refactor #13826\n"
        "\n"
        "1. text with prev: MED/training\n"
        "#14592 outside any backticks.\n"
    )
    v = vpg.check(body_with_bare_wrapped, [],
                  current_pr=14703, prev_targets=targets)
    assert v["guard_pass"] is False
    assert any(h["kind"] == "prev-abandoned" and h["prev_pr"] == 14592
               and h["location"] == "body"
               for h in v["hits"]["prev_invalid"])


def test_stale_commit_prev_cannot_veto_a_valid_body_15303():
    # #15309 4e axe -- le controle positif d'ai-01, rejoue : au head
    # ``1c2f8b7af9`` de #15303, ``--body-file`` seul rend guard_pass=True
    # (prev: DEEP/lean #15082, PR MERGED) et l'ajout de ``--commits-file``
    # rendait guard_pass=False sur ``commits[0]``, qui porte une
    # declaration ANTERIEURE pointant #15288 (une ISSUE). La correction
    # dans la surface declarative (le body) doit SUFFIRE : un message de
    # commit n'est pas une surface declarative, et la lane ne peut pas
    # l'editer sans reecrire l'historique.
    targets = {
        "15082": {"kind": "pr", "state": "MERGED", "merged": True},
        "15288": {"kind": "issue"},
    }
    body = ("Grain: DEEP/lean -- lane myia-po-2024:CoursIA-2 "
            "-- prev: DEEP/lean #15082")
    stale_commit = (
        "feat(lean): premiere tranche\n"
        "\n"
        "Grain: CONTENU/lean -- lane myia-po-2024:CoursIA-2 "
        "-- prev: MED/lean #15288\n"
    )
    v = vpg.check(body, [stale_commit], current_pr=15303,
                  prev_targets=targets)
    assert v["guard_pass"] is True
    assert v["hits"]["prev_invalid"] == []
    # Controle negatif de la prescription : la meme declaration dans le
    # BODY rougit toujours -- c'est exactement ce que #13475 voulait
    # attraper, et le retrait de la surface commits ne l'atteint pas.
    v2 = vpg.check(body.replace("#15082", "#15288"), [],
                   current_pr=15303, prev_targets=targets)
    assert v2["guard_pass"] is False
    assert any(h["kind"] == "prev-not-pr" and h["prev_pr"] == 15288
               and h["location"] == "body"
               for h in v2["hits"]["prev_invalid"])


# --- #14550, second defect: a silent fail-open is an unearned attestation ----
# ai-01 measured it on #14515: CLEAN, PR gate green, mergeable -- with an
# unevaluated `prev:`, because the `gh` resolution happened to fail during
# THAT run. Same violation as four red PRs the same minute; only the
# abstention differed, and nothing in the verdict said so.
#
# The 2026-09-08 repair of invariant 2 does NOT touch this: an abstention on
# a lookup failure and an abstention on an in-flight predecessor are two
# different silences, and only the first one is a gap in the measurement.

def test_unresolved_prev_targets_pure_selector():
    # The selector names exactly what the gate could not measure: cited but
    # absent from the resolved dict -- whether the lookup raised (network,
    # gh absent) or the target itself did not resolve.
    assert vpg.unresolved_prev_targets({14483}, {}) == [14483]
    assert vpg.unresolved_prev_targets(
        {14483, 7}, {"14483": {"kind": "pr", "state": "MERGED"}}) == [7]
    assert vpg.unresolved_prev_targets(set(), {}) == []


def test_resolution_failure_stays_green_but_flags_abstention(
        tmp_path, capsys, monkeypatch):
    # ACCEPTANCE 4 (#14550): resolution fails -> guard_pass: True AND
    # resolution_failed non-empty. The FN-safety contract is unchanged
    # (never accuse on a lookup failure); what changes is that the green
    # stops being indistinguishable from a measured one.
    body = tmp_path / "body.txt"
    body.write_text(
        "Grain: MED/tooling -- lane myia-po-2025:CoursIA-2 -- prev: MED/guard #14459",
        encoding="utf-8")

    def _boom(missing, runner=None):
        raise RuntimeError("gh absent (simulated #14515 condition)")

    monkeypatch.setattr(vpg, "resolve_prev_targets", _boom)
    rc = vpg.main(["--body-file", str(body), "--current-pr", "14560",
                   "--resolve-targets"])
    captured = capsys.readouterr()
    verdict = json.loads(captured.out)
    assert rc == 0
    assert verdict["guard_pass"] is True
    assert verdict["resolution_failed"] == [14459]
    # The warning line is a GitHub Actions workflow command: the workflow
    # `cat`s verdict.err inside the step, so this becomes a run annotation.
    assert "::warning::" in captured.err
    assert "#14459" in captured.err


def test_resolved_bad_target_fails_the_abstention_flag_is_not_the_predicate():
    # ACCEPTANCE 5 (#14550) -- positive control of the fail-open: with the
    # resolution SUCCEEDING on a target the predicate rejects, the verdict
    # must go red. The abstention flag repairs VISIBILITY, never the
    # predicate; if this ever passes, the fail-open has become permanent.
    #
    # The real #14515 tag cited an OPEN #14483, which is no longer a defect
    # (see `test_prev_open_abstains_the_predecessor_is_in_flight`). What
    # this test needs is any target the predicate DOES reject, so the shape
    # is kept and the state moved to CLOSED -- otherwise the assertion would
    # be measuring the repair instead of the fail-open.
    body = ("Grain: MED/notebook-python -- lane myia-po-2023:CoursIA -- "
            "prev: MED/notebook-python #14483")
    v = vpg.check(body, prev_targets={"14483": {"kind": "pr",
                                                "state": "CLOSED",
                                                "merged": False}})
    assert v["guard_pass"] is False
    kinds = {h["kind"] for h in v["hits"]["prev_invalid"]}
    assert "prev-abandoned" in kinds
    assert "resolution_failed" not in v  # check() has nothing to abstain on
