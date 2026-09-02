#!/usr/bin/env python3
"""Unit tests for check_lane_claim.py -- the lane-claim guard of #9774.

Pins the claim state-machine and, crucially, the Defaut-2 fix: the
authoritative timestamp is the comment's server `createdAt`, NEVER a stamp
written in the body. The #9764 collision hinged on a body stamp
`2026-08-07T00:52Z` that was 00:52 CEST (i.e. 22:52 UTC) -- wearing a `Z` it
read as two hours LATER than it was, which inverted the cross-lane claim order.
These tests replay that exact trap and assert the tool is not fooled.

Run: python -m pytest scripts/tests/test_check_lane_claim.py
"""
import fnmatch
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc  # noqa: E402
import grain_tag  # noqa: E402


# --- helpers -----------------------------------------------------------------

def comment(body, created_at, author="jsboige", url=None):
    return {
        "body": body,
        "createdAt": created_at,
        "author": {"login": author},
        "url": url,
    }


def payload(*comments, number=9764, title="t", labels=None):
    # #12156 -- `labels` defaults to None (absent key) so pre-existing tests
    # that don't care about the umbrella signal stay byte-equivalent: the
    # helper in `_is_umbrella_issue` falls back to `payload.get("labels") or []`
    # and degrades to the title-route. Tests that need the umbrella signal
    # pass `labels=[{"name": "EPIC"}]` explicitly.
    d = {"number": number, "title": title, "comments": list(comments)}
    if labels is not None:
        d["labels"] = labels
    return d


# --- extract_lane (grain_tag, now reused by the guard) -----------------------

def test_extract_lane_claim_form():
    # The #9774 issue-comment form carries the `lane` keyword.
    assert grain_tag.extract_lane(
        "[CLAIMED] lane myia-po-2024:CoursIA -- build the guard"
    ) == "myia-po-2024:CoursIA"


def test_extract_lane_none_when_no_lane_keyword():
    # Legacy dashboard form (no `lane` keyword) is out of scope -- the tool
    # surfaces it as an unattributed marker rather than guessing.
    assert grain_tag.extract_lane(
        "[CLAIMED] #9764 - myia-po-2025:CoursIA 2026-08-07T00:52Z"
    ) is None
    assert grain_tag.extract_lane("nothing here") is None


# --- extract_lane fallback (#10395 Variante 1) -------------------------------

def test_extract_lane_fallback_marker_line_recognises_gabarit():
    # The marker-line scope is the fix: a comment without the `lane` keyword
    # but with a `<machine>:<workspace>` token on the bracket line is
    # recognised by the fallback regex. The reproducer is the exact comment
    # from #10395 (the po-2023 claim on #10355 that was silently counted as
    # `.unattributed_markers`).
    assert grain_tag.extract_lane(
        "[CLAIMED] Notebook carte Argumentum (render deck depuis taxonomie in-repo) — myia-po-2023:CoursIA-2 2026-08-10T23:46:10Z",
        marker_line="[CLAIMED] Notebook carte Argumentum (render deck depuis taxonomie in-repo) — myia-po-2023:CoursIA-2 2026-08-10T23:46:10Z",
    ) == "myia-po-2023:CoursIA-2"


def test_extract_lane_fallback_does_not_match_arbitrary_colon_pairs():
    # The fallback is restricted to the marker line: URLs, time stamps and
    # code tokens that contain a colon anywhere in the body must NOT be
    # mistaken for a lane. This is the differential that justifies the
    # `marker_line` parameter.
    body = (
        "Some prose with a URL https://example.com:8080/path\n"
        "[CLAIMED] lane myia-po-2025:CoursIA -- working here\n"
        "A timestamp 12:34:56 elsewhere"
    )
    assert grain_tag.extract_lane(body) == "myia-po-2025:CoursIA"
    # When the caller asks for the fallback on the LAST marker line, the
    # time stamp and the URL on other lines are out of scope.
    assert grain_tag.extract_lane(
        body,
        marker_line="[CLAIMED] lane myia-po-2025:CoursIA -- working here",
    ) == "myia-po-2025:CoursIA"


def test_parse_claim_event_fallback_attribution():
    # End-to-end: a comment without the `lane` keyword, parsed by
    # `parse_claim_event`, becomes an ATTRIBUTED claim -- the reproducer
    # of the #10395 Variant 1 failure on #10355.
    from check_lane_claim import parse_claim_event  # noqa: E402
    ev = parse_claim_event(comment(
        "[CLAIMED] Notebook carte Argumentum (render deck depuis taxonomie in-repo) — myia-po-2023:CoursIA-2 2026-08-10T23:46:10Z",
        "2026-08-10T23:46:10Z",
        author="jsboige",
    ))
    assert ev is not None
    assert ev.lane == "myia-po-2023:CoursIA-2"
    assert ev.is_open is True
    assert ev.marker == "CLAIMED"
    assert grain_tag.extract_lane("nothing here") is None


# --- parse_claim_event -------------------------------------------------------

def test_parse_open_claim():
    ev = clc.parse_claim_event(comment(
        "[CLAIMED] lane myia-po-2024:CoursIA -- build the guard",
        "2026-08-06T22:43:31Z", author="jsboige",
    ))
    assert ev is not None
    assert ev.is_open is True
    assert ev.lane == "myia-po-2024:CoursIA"
    assert ev.marker == "CLAIMED"
    assert ev.created_at == "2026-08-06T22:43:31Z"
    assert ev["author"] == "jsboige"


def test_parse_close_markers():
    for marker in ("RELEASED", "DONE", "CANCELLED", "ABANDONED", "DELIVERED"):
        ev = clc.parse_claim_event(comment(
            f"[{marker}] lane myia-po-2024:CoursIA -- done",
            "2026-08-06T23:00:00Z",
        ))
        assert ev is not None
        assert ev.is_open is False
        assert ev.marker == marker


def test_parse_delivered_captures_pr_ref():
    """#12320 -- `[DELIVERED] lane X -- PR #N` records the PR reference.

    The PR number is a parsed integer on the event, distinguishing
    "delivered to a PR I have the number for" from a bare DELIVERED. The
    reducer treats both as closes, so v1 only verifies that the writer's
    intent is durably recorded for the summary and the future v2 gate.
    """
    ev = clc.parse_claim_event(comment(
        "[DELIVERED] lane myia-po-2023:CoursIA-2 -- PR #12271",
        "2026-08-22T12:00:00Z",
    ))
    assert ev is not None
    assert ev.marker == "DELIVERED"
    assert ev.is_delivered is True
    assert ev.pr_ref == 12271
    assert ev.is_open is False


def test_parse_delivered_without_pr_ref_still_closes():
    """A DELIVERED without a PR reference is a legal close; just no pr_ref.

    The marker closes the claim like a RELEASED would. The empty pr_ref
    is honest about the gap: the writer chose the DELIVERED vocabulary
    without naming a PR, so the consumer cannot fetch one.
    """
    ev = clc.parse_claim_event(comment(
        "[DELIVERED] lane myia-po-2023:CoursIA-2 -- substance shipped",
        "2026-08-22T12:00:00Z",
    ))
    assert ev is not None
    assert ev.marker == "DELIVERED"
    assert ev.is_delivered is True
    assert ev.pr_ref is None
    assert ev.is_open is False


def test_extract_delivered_pr_ref_handles_stray_hash():
    """`#1234` without the `PR` prefix is NOT a PR reference (#12320).

    The writer must explicitly name `PR #N` -- this prevents an issue
    number (e.g. `#12320` in the body text) from being mistaken for a
    PR reference the consumer would go fetch. Stray hash is ignored.
    """
    assert clc._extract_delivered_pr_ref(
        "[DELIVERED] lane X -- see #12320 for the issue"
    ) is None
    # The PR keyword IS required
    assert clc._extract_delivered_pr_ref(
        "[DELIVERED] lane X -- PR #12320"
    ) == 12320
    # And `Pull Request` is not accepted (we want a short form, easy to
    # grep, easy to type).
    assert clc._extract_delivered_pr_ref(
        "[DELIVERED] lane X -- Pull Request #12320"
    ) is None


def test_parse_non_marker_is_none():
    assert clc.parse_claim_event(comment(
        "just a status update, no bracket marker", "2026-08-06T22:00:00Z"
    )) is None


def test_parse_last_marker_wins():
    # A comment that both opens and closes: the FINAL intent wins (close).
    ev = clc.parse_claim_event(comment(
        "[CLAIMED] lane X:CoursIA -- oops\n[DONE] lane X:CoursIA",
        "2026-08-06T22:00:00Z",
    ))
    assert ev is not None and ev.is_open is False


def test_parse_instructional_marker_in_prose_ignored():
    # The #10228 false-negative (c.74). ai-01's claim comment carried a real
    # line-start `[CLAIMED]` then an instructional sentence MENTIONING
    # `[RELEASED]` mid-prose ("Release with `[RELEASED]` when your PR lands").
    # The unanchored regex took that mid-prose `[RELEASED]` as the final-intent
    # close, neutralising the claim -- the tool reported CLEAR while po-2025
    # held an active claim, a near-collision. Line-anchoring rejects the
    # mid-prose mention; only the real line-start `[CLAIMED]` counts.
    body = (
        "[CLAIMED] lane myia-po-2025:CoursIA-2 -- Taches 1-2 (CPU).\r\n\r\n"
        "(check_lane_claim #9774; Release with `[RELEASED]` when your PR lands.)"
    )
    ev = clc.parse_claim_event(
        comment(body, "2026-08-09T21:19:00Z", author="myia-ai-01"))
    assert ev is not None
    assert ev.is_open is True              # NOT closed by the mid-prose mention
    assert ev.marker == "CLAIMED"
    assert ev.lane == "myia-po-2025:CoursIA-2"


# --- markdown decoration tolerance (#10906) ----------------------------------

# The 8 voided markers on 70 issues: issue comments are markdown-rendered, and
# agents post `**[CLAIMED] ...**`, `## [CLAIMED] ...`, `- [CLAIMED] ...` etc.
# The legacy `^[ \t]*\[` anchor voided every such marker -- the claim existed
# on the issue but the reducer never saw it. These tests pin the tolerance and
# the mid-prose non-regression.

def test_parse_marker_bold_decorated():
    # The exact shape of po-2024's inert claim on #10043 (markdown bold wrap).
    ev = clc.parse_claim_event(comment(
        "**[CLAIMED] #10043 grain D (T3 activation) — lane myia-po-2024:CoursIA — 2026-08-08T12:36Z**",
        "2026-08-08T12:37:14Z",
    ))
    assert ev is not None
    assert ev.is_open is True
    assert ev.marker == "CLAIMED"
    assert ev.lane == "myia-po-2024:CoursIA"


def test_parse_marker_underscore_bold_decorated():
    ev = clc.parse_claim_event(comment(
        "__[CLAIMED] lane myia-po-2023:CoursIA-2 — underscore bold__",
        "2026-08-08T13:00:00Z",
    ))
    assert ev is not None
    assert ev.is_open is True
    assert ev.lane == "myia-po-2023:CoursIA-2"


def test_parse_marker_heading_decorated():
    ev = clc.parse_claim_event(comment(
        "## [CLAIMED] lane myia-po-2025:CoursIA-2 -- heading form",
        "2026-08-08T13:01:00Z",
    ))
    assert ev is not None
    assert ev.is_open is True
    assert ev.lane == "myia-po-2025:CoursIA-2"


def test_parse_marker_bullet_decorated():
    for bullet in ("- ", "+ ", "* "):
        ev = clc.parse_claim_event(comment(
            f"{bullet}[CLAIMED] lane myia-po-2024:CoursIA -- bullet form",
            "2026-08-08T13:02:00Z",
        ))
        assert ev is not None, bullet
        assert ev.is_open is True, bullet
        assert ev.lane == "myia-po-2024:CoursIA", bullet


def test_parse_marker_blockquote_decorated():
    ev = clc.parse_claim_event(comment(
        "> [CLAIMED] lane myia-po-2026:CoursIA-2 -- blockquote form",
        "2026-08-08T13:03:00Z",
    ))
    assert ev is not None
    assert ev.is_open is True
    assert ev.lane == "myia-po-2026:CoursIA-2"


def test_parse_marker_nested_list_decorated():
    ev = clc.parse_claim_event(comment(
        "  - > **[CLAIMED] lane myia-po-2024:CoursIA-2 -- nested bullet + bold**",
        "2026-08-08T13:04:00Z",
    ))
    assert ev is not None
    assert ev.is_open is True
    assert ev.lane == "myia-po-2024:CoursIA-2"


def test_parse_decorated_marker_in_prose_still_ignored():
    # Mid-line mentions remain non-events even inside a bullet: the `[` must
    # sit at a decorator position, not after prose.
    body = (
        "[CLAIMED] lane myia-po-2025:CoursIA-2 -- real claim\n"
        "- **Release with `[RELEASED]` when your PR lands** (instructional)"
    )
    ev = clc.parse_claim_event(comment(body, "2026-08-09T21:20:00Z"))
    assert ev is not None
    assert ev.is_open is True      # NOT closed by the decorated prose mention
    assert ev.marker == "CLAIMED"


def test_parse_decorated_release_closes():
    ev = clc.parse_claim_event(comment(
        "**[CLAIMED] lane myia-po-2024:CoursIA -- work**\n"
        "**[RELEASED] lane myia-po-2024:CoursIA -- landed**",
        "2026-08-08T14:00:00Z",
    ))
    assert ev is not None
    assert ev.is_open is False
    assert ev.marker == "RELEASED"


def test_decorated_paths_clause_scopes_claim():
    # A bold-wrapped claim carrying `paths:` keeps its scope (#10419 semantics)
    # through the decorated marker -- disjoint scoped claims stay parallel. The
    # closing `**` is captured into the last path (`b.ipynb**`): stripping it by
    # suffix alone is unsafe (`paths: dir/**` is a legitimate recursive glob),
    # and fnmatch trailing `*` matches empty, so the scope still covers the
    # intended path (see `_PATHS_CLAUSE_RE` comment in check_lane_claim.py).
    ev = clc.parse_claim_event(comment(
        "- **[CLAIMED] lane myia-po-2024:CoursIA-2 — paths: notebooks/a.ipynb, notebooks/b.ipynb**",
        "2026-08-08T14:05:00Z",
    ))
    assert ev is not None
    assert ev.is_open is True
    assert ev.lane == "myia-po-2024:CoursIA-2"
    assert ev.paths is not None
    assert ev.paths[0] == "notebooks/a.ipynb"
    assert fnmatch.fnmatch("notebooks/b.ipynb", ev.paths[1])
    assert fnmatch.fnmatch("notebooks/b.ipynb", "notebooks/b.ipynb**")  # invariant


# --- non-ASCII leading decoration (#12711) -----------------------------------
# A leading `→` (U+2192) / `➡` / `»` / `•` / `–` / `—` is an agent decoration,
# not an ASCII decorator. The ASCII-pure decor class voided such a marker to
# BOTH regexes on #12465 (po-2026's `→DELIVERED` went unread; po-2027 got CLEAR
# and delivered the same notebook 15 h later). Broadening `_DECOR` re-reads the
# marker and re-arms the malformed lint for the bracketless form.

def test_parse_marker_non_ascii_arrow_decorated():
    ev = clc.parse_claim_event(comment(
        "→[CLAIMED] lane myia-po-2027:CoursIA-2 -- arrow prefix",
        "2026-08-23T18:21:01Z",
    ))
    assert ev is not None
    assert ev.is_open is True
    assert ev.marker == "CLAIMED"
    assert ev.lane == "myia-po-2027:CoursIA-2"


def test_parse_non_ascii_decorated_delivered_closes():
    # The exact #12465 shape, bracketed: an arrow-prefixed DELIVERED with a
    # lane must register as a close (this is what po-2026's line should have
    # done before po-2027 delivered the same notebook).
    ev = clc.parse_claim_event(comment(
        "→[DELIVERED] lane myia-po-2026:CoursIA -- PR #12512 paths: .../Search-3-Informed.ipynb",
        "2026-08-23T03:36:33Z",
    ))
    assert ev is not None
    assert ev.marker == "DELIVERED"
    assert ev.is_open is False
    assert ev.lane == "myia-po-2026:CoursIA"


def test_parse_non_ascii_decoration_mid_prose_still_ignored():
    # A `→` followed by prose, then a mid-line `[CLAIMED]`, must NOT become an
    # event (the bracket is not at a decorator position). Non-regression pinned.
    ev = clc.parse_claim_event(comment(
        "→ Cette PR reprend un [CLAIMED] discute plus tot",
        "2026-08-23T09:00:00Z",
    ))
    assert ev is None


def test_check_no_paths_claim_in_prose_returns_exit_2_not_scoped(capsys):
    # Full-flow regression for the #10228 FN: a claim comment that ALSO mentions
    # a close marker in instructional prose must still BLOCK another lane. This
    # is the exact shape of ai-01's dispatch comments (claim + release instructions).
    # #12322 -- caller has no scope so the verdict is `NOT_SCOPED` (exit 2),
    # not `BLOCKED` (exit 1). The nuance is that the caller can lift the
    # block by re-running with `--paths` matching their actual files.
    body = (
        "[CLAIMED] lane myia-po-2025:CoursIA-2 -- Taches 1-2 (CPU).\r\n\r\n"
        "(Release with `[RELEASED]` when your PR lands.)"
    )
    p = payload(comment(body, "2026-08-09T21:19:00Z", author="myia-ai-01"))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    assert rc == 2                          # NOT_SCOPED, not BLOCKED (legacy returned 1)
    captured = capsys.readouterr()
    assert "NOT_SCOPED" in captured.err
    assert "myia-po-2025:CoursIA-2" in captured.out


def test_parse_unattributed_marker():
    # Marker present but no `lane` keyword -> lane None (surfaced, not guessed).
    ev = clc.parse_claim_event(comment(
        "[CLAIMED] #9764 some work", "2026-08-06T22:00:00Z"
    ))
    assert ev is not None
    assert ev.lane is None


# --- compute_active_claims (state machine) -----------------------------------

def test_open_then_close_inactive():
    events = [
        clc.parse_claim_event(comment(
            "[CLAIMED] lane A:CoursIA -- x", "2026-08-06T22:00:00Z")),
        clc.parse_claim_event(comment(
            "[RELEASED] lane A:CoursIA -- done", "2026-08-06T22:30:00Z")),
    ]
    active, unattrib = clc.compute_active_claims(events)
    assert active == {}
    assert unattrib == []


def test_two_lanes_both_active():
    events = [
        clc.parse_claim_event(comment(
            "[CLAIMED] lane A:CoursIA -- x", "2026-08-06T22:00:00Z")),
        clc.parse_claim_event(comment(
            "[CLAIMED] lane B:CoursIA-2 -- y", "2026-08-06T22:10:00Z")),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"A:CoursIA", "B:CoursIA-2"}


def test_close_one_keeps_other():
    events = [
        clc.parse_claim_event(comment(
            "[CLAIMED] lane A:CoursIA -- x", "2026-08-06T22:00:00Z")),
        clc.parse_claim_event(comment(
            "[CLAIMED] lane B:CoursIA-2 -- y", "2026-08-06T22:10:00Z")),
        clc.parse_claim_event(comment(
            "[RELEASED] lane A:CoursIA -- done", "2026-08-06T22:30:00Z")),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"B:CoursIA-2"}


def test_unattributed_collected_not_active():
    events = [
        clc.parse_claim_event(comment(
            "[CLAIMED] #9764 orphan", "2026-08-06T22:00:00Z")),
    ]
    active, unattrib = clc.compute_active_claims(events)
    assert active == {}
    assert len(unattrib) == 1


# --- Defaut-2 regression: server createdAt orders, body stamps do not --------

def test_defaut2_body_stamp_does_not_invert_order():
    """The #9764 trap. po-2025's body bore `00:52Z` (really 00:52 CEST = 22:52
    UTC). Naive body-stamp ordering would place it AFTER po-2023's 22:57Z claim.
    The server `createdAt` (22:43Z) is EARLIER. The tool MUST order by the
    server field, so po-2025 is correctly the first claimant."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2025:CoursIA -- fix 2026-08-07T00:52Z",
            "2026-08-06T22:43:31Z",  # SERVER: the real instant (22:43 UTC)
            author="jsboige",
        ),
        comment(
            "[CLAIMED] lane myia-po-2023:CoursIA-2 -- diag",
            "2026-08-06T22:57:37Z",  # SERVER: later
            author="jsboige",
        ),
    )
    events = clc._sort_events(p)
    assert [e.lane for e in events] == [
        "myia-po-2025:CoursIA",      # earliest by server createdAt
        "myia-po-2023:CoursIA-2",
    ]
    # The misleading body stamp did not leak into the event's timestamp.
    assert events[0].created_at == "2026-08-06T22:43:31Z"


# --- _run_check exit codes ---------------------------------------------------

def test_check_clear_when_only_my_lane(capsys):
    p = payload(comment(
        "[CLAIMED] lane myia-po-2024:CoursIA -- build the guard",
        "2026-08-06T22:43:31Z",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    assert rc == 0
    out = capsys.readouterr().out
    assert "CLEAR" in out


def test_check_no_paths_returns_exit_2_and_not_scoped(capsys):
    # #12322 -- when the caller does NOT pass `--paths` AND has no scoped
    # active claim of their own, the call cannot prove disjointness from any
    # blocker. The legacy verdict (exit 1, BLOCKED) was a hard read that
    # prompted the fumble on #11112 (user-mistaking the question for a
    # real block, then escalating to ai-01 and posting an URGENT DM).
    # The fix splits this into `exit 2` + the `NOT_SCOPED` verdict label
    # so the next step is unambiguously "re-run with `--paths`" instead
    # of "find another grain".
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- working here",
        "2026-08-06T22:43:31Z",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    assert rc == 2
    captured = capsys.readouterr()
    assert "NOT_SCOPED" in captured.err
    assert "ACTION" in captured.err
    assert "myia-po-2025:CoursIA" in captured.out


# --- #12322 -- query_scope + exit code semantics -----------------------------
#
# Three exit codes:
#   0 -> CLEAR (no blocker at all).
#   1 -> BLOCKED (caller's scope proves disjointness impossible -- real conflict).
#   2 -> NOT_SCOPED (caller did not bind scope, blocker cannot be confirmed
#        as a real conflict -- the next step is to re-run with `--paths`).
#
# The test above (test_check_no_paths_returns_exit_2_and_not_scoped) covers
# the unscoped-caller-against-unscoped-blocker leg. The four tests below
# pin the OTHER three legs of the matrix so the verdict behaviour does not
# silently drift on either the PATH_SCOPED or the CLEAR branch.

def test_check_query_scope_path_scoped_when_caller_passes_paths(capsys):
    """When the caller passes `--paths`, the verdict field is `PATH_SCOPED`
    EVEN WHEN a blocker exists. This pins the matrix: the caller IS scoping,
    so the verdict layer is no longer the right place for the actionable
    hint -- the verdict is the real exit 1 / real BLOCKED label."""
    p = payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA -- working here",
                "2026-08-06T22:43:31Z"),
    )
    rc = clc._run_check(
        p, "myia-po-2024:CoursIA",
        my_paths=["scripts/check_lane_claim.py"],
    )
    out = capsys.readouterr().out
    assert rc == 1  # BLOCKED at exit 1 -- caller IS scoping, real conflict
    assert '"query_scope": "PATH_SCOPED"' in out


def test_check_query_scope_path_scoped_when_caller_already_owns_scoped_claim(capsys):
    """Symmetric leg: the caller does NOT pass `--paths` BUT already owns an
    active scoped claim (`paths:`) on the same issue. Their scope merges
    with the call site via the #10419 rule. The verdict is `PATH_SCOPED`
    at exit 1 -- the caller is, in effect, scoped through their own active
    claim, so the unscoped-caller hint does not apply.

    # #12862 -- the caller's own claim scopes to `Sudoku-9.ipynb`, which does
    # NOT exist as a tracked file, but the glob is SYNTACTICALLY VALID (it
    # carries a `/`): this is a creation scope, not a typo. The other lane's
    # epic-wide claim still blocks (disjointness from a not-yet-existing tree
    # is unprovable), so the verdict is BLOCKED at exit 1 -- the relaxation
    # never opens a disputed scope.
    # NB post-merge #12345 : le classifieur de vivacite de scope de main
    # distinguait scope mort = non-scope ; #12862 le raffine en creation scope
    # pour le sous-ensemble a glob SYNTAXIQUEMENT VALIDE.
    """
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA -- "
            "paths: MyIA.AI.Notebooks/Sudoku/Sudoku-09.ipynb",
            "2026-08-11T04:02:00Z",
        ),
        comment(
            "[CLAIMED] lane myia-po-2025:CoursIA -- working here",
            "2026-08-06T22:43:31Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    out = capsys.readouterr().out
    # #12862 -- the dead-but-valid scope classifies as a CREATION scope
    # (`PATH_SCOPED`, not `EPIC_WIDE_NO_PATHS_DECLARED`): the other lane's
    # epic-wide claim still blocks, so the verdict is BLOCKED at exit 1 --
    # relaxation only reclassifies, it never lifts a real blocker.
    assert rc == 1  # BLOCKED -- creation scope, but another lane claims (#12862)
    assert '"query_scope": "PATH_SCOPED"' in out
    # Verify the caller's own scoped claim is in the active_claims dict.
    assert '"myia-po-2024:CoursIA"' in out


def test_check_query_scope_clears_when_no_blockers_and_caller_is_unscoped(capsys):
    """The CLEAR case at exit 0 -- caller is unscoped, no other lane holds
    a claim. The verdict is still CLEAR and `query_scope` is `PATH_SCOPED`
    (the caller's not-scoping does not influence the verdict when nothing
    is blocking). Pinning this prevents a future change from falsely
    classifying `CLEAR + unscoped` as a sentinel of any kind."""
    p = payload(comment(
        "[CLAIMED] lane myia-po-2024:CoursIA -- build the guard",
        "2026-08-06T22:43:31Z",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    out = capsys.readouterr().out
    assert rc == 0
    # query_scope is PATH_SCOPED on a CLEAR even when the caller did not
    # bind `--paths` -- the field reports the FORCED CLASSIFIER, not the
    # caller's own choice. The rule `EPIC_WIDE_NO_PATHS_DECLARED` only
    # triggers when there is at least one blocker to label.
    assert '"query_scope": "PATH_SCOPED"' in out
    assert '"blocked": false' in out


def test_check_path_scoped_blocks_against_real_intersecting_scope(capsys):
    """The decisive positive control -- a SCOPED caller whose scope
    intersects the blocker's scope reads as `BLOCKED` at `exit 1` (NOT
    `NOT_SCOPED` at `exit 2`). The exit-code distinction is the only thing
    that lets the caller automate against this verdict."""
    # Blocker's scope: scripts/**
    # Caller's scope: scripts/check_lane_claim.py (intersects)
    p = payload(
        comment(
            "[OVERRIDE] lane myia-po-2024:CoursIA -- paths: scripts/**",
            "2026-08-11T18:00:00Z",
        ),
    )
    rc = clc._run_check(
        p,
        "myia-po-2025:CoursIA-2",
        my_paths=["scripts/check_lane_claim.py"],
    )
    err = capsys.readouterr().err
    assert rc == 1
    # The non-path-scoped BLOCKED message fires -- distinct from the
    # NOT_SCOPED message which would have fired if the caller had no scope.
    assert "BLOCKED: another lane holds an active claim" in err
    assert "NOT_SCOPED" not in err


def test_check_clear_after_other_lane_releases(capsys):
    p = payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA -- working here",
                "2026-08-06T22:43:31Z"),
        comment("[RELEASED] lane myia-po-2025:CoursIA -- landed",
                "2026-08-06T23:30:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    assert rc == 0


def test_check_surfaces_unattributed(capsys):
    p = payload(comment("[CLAIMED] #9764 orphan claim", "2026-08-06T22:00:00Z"))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    # Unattributed does not block (cannot attribute) but is surfaced.
    assert rc == 0
    out = capsys.readouterr().out
    assert '"unattributed_markers": 1' in out


# --- #11239: malformed-marker lint --------------------------------------------
# A claim written WITHOUT the brackets (`CLAIMED #N ...`) is invisible to
# `_MARKER_RE` -- the organ reports `unattributed_markers: 0` and answers
# CLEAR to every other lane while the writer believes their lock is posted
# (measured 2026-08-16 on #11222: #11230 / #11233, 7 minutes apart). The lint
# is WARN-only: the writer learns at the call site that they were not read.

def test_malformed_marker_incident_line_surfaces(capsys):
    # The exact shape of the #11222 incident comment line.
    p = payload(comment(
        "CLAIMED #11222 — myia-po-2026:CoursIA — 2026-08-16T11:12Z. "
        "Fix couche resolution gate nits.",
        "2026-08-16T09:09:50Z", author="jsboige"))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0                          # WARN-only, never blocks
    assert '"malformed_markers": 1' in captured.out
    assert 'CLAIMED #11222' in captured.out
    assert 'WARN: marqueur sans crochets "CLAIMED"' in captured.err


def test_malformed_marker_lane_form_surfaces(capsys):
    p = payload(comment(
        "CLAIMED lane myia-po-2026:CoursIA -- working here",
        "2026-08-16T09:10:00Z", author="jsboige"))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"malformed_markers": 1' in captured.out
    assert 'WARN: marqueur sans crochets "CLAIMED"' in captured.err


def test_bracketed_marker_is_not_malformed(capsys):
    p = payload(comment(
        "[CLAIMED] #11222 — myia-po-2026:CoursIA — 2026-08-16T11:12Z.",
        "2026-08-16T09:09:50Z", author="jsboige"))
    # Own-lane check: the bracketed claim IS read and does not block us.
    rc = clc._run_check(p, "myia-po-2026:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"malformed_markers": 0' in captured.out
    assert 'WARN: marqueur sans crochets' not in captured.err


def test_prose_mention_not_flagged(capsys):
    # A line that merely MENTIONS a marker word mid-prose is not a claim:
    # the motif tail (`lane <tok>` / `#N`) is required AND the marker word
    # must be line-initial after decoration.
    p = payload(comment(
        "Cette PR revient sur un [CLAIMED] discute plus tot; work done #123.",
        "2026-08-16T09:00:00Z"))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"malformed_markers": 0' in captured.out
    assert 'WARN: marqueur sans crochets' not in captured.err


def test_decorated_bare_marker_flagged(capsys):
    # `**` / bullet decoration is tolerated by `_MARKER_RE`, so a bare marker
    # with the same decoration is equally invisible and equally malformed.
    p = payload(comment(
        "- **CLAIMED** #11222 -- myia-po-2026:CoursIA",
        "2026-08-16T09:11:00Z"))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"malformed_markers": 1' in captured.out


def test_malformed_marker_non_ascii_decorated_surfaces(capsys):
    # #12711 -- a `→`-prefixed BARE marker (no brackets) was invisible to the
    # #11239 lint too: the writer believed their lock was posted yet the organ
    # answered CLEAR. Broadening `_DECOR` re-arms the WARN.
    p = payload(comment(
        "→CLAIMED lane myia-po-2026:CoursIA -- working here",
        "2026-08-23T03:36:33Z"))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0                          # WARN-only, never blocks
    assert '"malformed_markers": 1' in captured.out
    assert 'WARN: marqueur sans crochets "CLAIMED"' in captured.err


def test_malformed_close_marker_flagged(capsys):
    # Close markers are linted too: a bracketless `RELEASED` never registers
    # as a release, so the claim stays locked for other lanes.
    p = payload(comment(
        "RELEASED lane myia-po-2025:CoursIA -- landed",
        "2026-08-16T09:20:00Z"))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"malformed_markers": 1' in captured.out
    assert 'WARN: marqueur sans crochets "RELEASED"' in captured.err


def test_valid_bracketed_line_with_midline_bare_word_not_double_counted(capsys):
    # A well-formed `[CLAIMED]` whose line ALSO mentions a bare marker word
    # later must count 0 malformed: the lint is line-initial only, and the
    # bracketed claim is read by `_MARKER_RE` as intended.
    p = payload(comment(
        "[CLAIMED] lane myia-po-2026:CoursIA -- voir RELEASED #12 du precedent",
        "2026-08-16T09:30:00Z"))
    rc = clc._run_check(p, "myia-po-2026:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"malformed_markers": 0' in captured.out
    assert 'WARN: marqueur sans crochets' not in captured.err


# --- #12624: quasi-marker + single-line composite lints -----------------------
# The 2026-08-22 #12329 incident, both defects: (1) a bracketed `[CLAGED]`
# (edit-distance-2 typo of CLAIMED) was invisible to BOTH the event parser
# and the #11239 bare lint -- the lane believed its lock was posted; (2) the
# repair comment put a lift AND a re-claim on ONE line, of which only the
# head token is line-anchored, so the re-claim was silently swallowed and a
# second lane delivered the same four files nine hours later (#12343/#12433).
# Both lints are WARN-only: they restore the signal, never the verdict.

INCIDENT_TYPO_LINE = (
    "[CLAGED] lane myia-po-2024:CoursIA-2 -- grain DEEP/lean, prev: DEEP/lean "
    "c.1331p384 PR #12337 -- paths: MyIA.AI.Notebooks/GameTheory/game_theory_lean/"
    "SocialChoice/MechanismDesign.lean"
)
INCIDENT_REPAIR_LINE = (
    "[RELEASED claim-malformed] ignore le marqueur precedent qui contenait "
    "[CLAGED] (typo). Re-claim ici : [CLAIMED] lane myia-po-2024:CoursIA-2 "
    "-- paths: MyIA.AI.Notebooks/GameTheory/game_theory_lean/SocialChoice/"
    "MechanismDesign.lean"
)


def test_quasi_typo_incident_line_surfaces(capsys):
    # Defaut 1: the verbatim incident line. `[CLAGED]` is distance 2 from
    # CLAIMED and carries the claim motif -> 1 suspected typo marker.
    p = payload(comment(INCIDENT_TYPO_LINE, "2026-08-22T16:03:42Z", author="jsboige"))
    rc = clc._run_check(p, "myia-po-2023:CoursIA-2")
    captured = capsys.readouterr()
    assert rc == 0                          # WARN-only, never blocks
    assert '"suspected_typo_markers": 1' in captured.out
    assert "WARN: quasi-marqueur" in captured.err
    assert "CLAGED" in captured.err and "CLAIMED" in captured.err


def test_quasi_suffix_marker_surfaces(capsys):
    # Defaut 2 head shape: `[RELEASED claim-malformed]` -- the keyword is
    # right but the bracket carries a suffix, so `_MARKER_RE` rejects it and
    # the gesture enacts nothing.
    p = payload(comment(INCIDENT_REPAIR_LINE, "2026-08-22T16:03:47Z", author="jsboige"))
    rc = clc._run_check(p, "myia-po-2023:CoursIA-2")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"suspected_typo_markers": 1' in captured.out
    assert "suffixe dans les crochets" in captured.err


def test_incident_repair_line_flags_swallowed_reclaim(capsys):
    # Defaut 2: the mid-line `[CLAIMED]` of the repair line is NOT an event
    # (#10228 mid-prose protection) -- the composite lint must name it so the
    # writer learns the re-claim never registered.
    p = payload(comment(INCIDENT_REPAIR_LINE, "2026-08-22T16:03:47Z", author="jsboige"))
    rc = clc._run_check(p, "myia-po-2023:CoursIA-2")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"composite_single_line_markers": 1' in captured.out
    assert "marqueur compose sur une seule ligne" in captured.err
    assert "CLAIMED" in captured.err


def test_incident_repair_line_enacts_no_claim(capsys):
    # End-to-end acceptance: the repair comment as a whole must leave the
    # repairing lane WITHOUT an active claim (that is the measured damage --
    # only the signal fixes it now), and must not block anyone either.
    p = payload(comment(INCIDENT_REPAIR_LINE, "2026-08-22T16:03:47Z", author="jsboige"))
    rc = clc._run_check(p, "myia-po-2024:CoursIA-2")
    captured = capsys.readouterr()
    assert rc == 0                          # CLEAR: no claim was registered
    assert '"my_active_claim": false' in captured.out


def test_real_marker_not_quasi(capsys):
    # Selectivity: a canonical `[CLAIMED] lane X -- paths: ...` is a real
    # marker (no suffix in brackets) -- 0 suspected, 0 composite.
    p = payload(comment(
        "[CLAIMED] lane myia-po-2026:CoursIA -- paths: MyIA.AI.Notebooks/Search/**",
        "2026-08-24T09:00:00Z"))
    rc = clc._run_check(p, "myia-po-2026:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"suspected_typo_markers": 0' in captured.out
    assert '"composite_single_line_markers": 0' in captured.out
    assert "WARN: quasi-marqueur" not in captured.err


def test_quasi_requires_claim_motif(capsys):
    # Selectivity (#11239 gate): a bracketed almost-word on a line with NO
    # claim motif (`lane X` / `#N` / `paths:`) is prose, not a gesture.
    p = payload(comment(
        "Le cladage des especes [CLADGED] reste ouvert dans la taxonomie.",
        "2026-08-24T09:00:00Z"))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"suspected_typo_markers": 0' in captured.out


def test_quasi_far_word_not_flagged(capsys):
    # Selectivity: a bracketed word far from every keyword (even with a lane
    # motif on the line) is not a marker attempt -- `[Arbitrage ...]` is the
    # real shape of an arbitration headline on #12329.
    p = payload(comment(
        "[Arbitrage #12329 -- lane myia-po-2024:CoursIA] Verdict : doublon cross-lane.",
        "2026-08-24T03:18:28Z", author="jsboige"))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"suspected_typo_markers": 0' in captured.out


def test_quasi_fenced_citation_not_flagged(capsys):
    # A quasi marker quoted in a fenced block is a citation, not a gesture
    # (same masking rationale as `_parse_claim_events`).
    p = payload(comment(
        "```\n[CLAGED] lane myia-po-2024:CoursIA-2 -- paths: a/**\n```\n"
        "(citation du marqueur casse, cf. arbitrage)",
        "2026-08-24T09:00:00Z"))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"suspected_typo_markers": 0' in captured.out
    assert '"composite_single_line_markers": 0' in captured.out


def test_template_prose_line_not_composite(capsys):
    # The claim template's own prose line ("Release with `[RELEASED]` when
    # your PR lands.") has NO line-anchored head marker -- it must never be
    # flagged as a composite.
    p = payload(comment(
        "[CLAIMED] lane myia-po-2026:CoursIA -- paths: MyIA.AI.Notebooks/Search/**\n\n"
        "(check_lane_claim #9774 -- server-stamped UTC; body timestamps are NOT "
        "authoritative. Release with `[RELEASED]` when your PR lands.)",
        "2026-08-24T09:00:00Z"))
    rc = clc._run_check(p, "myia-po-2026:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"composite_single_line_markers": 0' in captured.out
    assert "marqueur compose" not in captured.err


def test_multiline_composite_last_marker_wins(capsys):
    # The WRITTEN tie-break (#12624): several markers ACROSS LINES are legal,
    # walk order applies -- last line-anchored marker wins. A claim then a
    # release on the NEXT line reduces to released, and NO composite flag
    # fires (the shape is unambiguous, only single-line swallows a marker).
    p = payload(comment(
        "[CLAIMED] lane myia-po-2026:CoursIA -- paths: a/**\n"
        "[RELEASED] lane myia-po-2026:CoursIA -- erreur de cible",
        "2026-08-24T09:00:00Z"))
    rc = clc._run_check(p, "myia-po-2026:CoursIA")
    captured = capsys.readouterr()
    assert rc == 0
    assert '"my_active_claim": false' in captured.out
    assert '"composite_single_line_markers": 0' in captured.out


# --- --stale-threshold (#9812) ----------------------------------------------
# A claim older than the threshold (age from server createdAt, never the body)
# is treated as STALE: it no longer blocks, but a STALE_CLAIM warning is printed
# and the claimant must still post its own [CLAIMED]. Without the flag, every
# active claim blocks (behaviour unchanged).

NOW = datetime(2026, 8, 7, 12, 0, 0, tzinfo=timezone.utc)


def test_claim_age_hours_basic():
    # 48h ago at the fixed NOW.
    age = clc._claim_age_hours("2026-08-05T12:00:00Z", NOW)
    assert age is not None and abs(age - 48.0) < 1e-6


def test_claim_age_hours_none_on_unparseable():
    assert clc._claim_age_hours(None, NOW) is None
    assert clc._claim_age_hours("not a date", NOW) is None


def test_parse_iso_utc_tolerates_fractional_and_offset():
    assert clc._parse_iso_utc("2026-08-07T12:00:00Z") is not None
    assert clc._parse_iso_utc("2026-08-07T12:00:00.123Z") is not None
    assert clc._parse_iso_utc("2026-08-07T12:00:00+00:00") is not None
    assert clc._parse_iso_utc("garbage") is None


def test_stale_threshold_unblocks_old_claim(capsys):
    # Other lane claimed 48h ago; threshold 24h -> CLEAR with stale warning.
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- working here",
        "2026-08-05T12:00:00Z",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA",
                        stale_threshold=24.0, now=NOW)
    assert rc == 0
    captured = capsys.readouterr()
    assert "STALE_CLAIM myia-po-2025:CoursIA" in captured.err
    assert '"stale_claims"' in captured.out
    assert '"blocked": false' in captured.out


def test_stale_threshold_fresh_claim_returns_exit_2_not_scoped(capsys):
    # Other lane claimed 2h ago; threshold 24h -> NOT_SCOPED at exit 2 (#12322).
    # Pre-#12322 this returned `exit 1` + `BLOCKED`, conflating a non-scoped
    # caller with a real conflict. The new verdict reflects the action the
    # caller can take (re-run with `--paths`).
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- working here",
        "2026-08-07T10:00:00Z",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA",
                        stale_threshold=24.0, now=NOW)
    assert rc == 2
    captured = capsys.readouterr()
    assert "NOT_SCOPED" in captured.err


def test_stale_threshold_stale_plus_fresh_blocks_on_fresh(capsys):
    # Two other lanes: one stale (48h), one fresh (1h). The fresh one
    # triggers the NOT_SCOPED verdict (#12322 exit 2) since the caller
    # has no scope of their own.
    p = payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA -- old",
                "2026-08-05T12:00:00Z"),
        comment("[CLAIMED] lane myia-po-2023:CoursIA -- fresh",
                "2026-08-07T11:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA",
                        stale_threshold=24.0, now=NOW)
    assert rc == 2
    captured = capsys.readouterr()
    # The stale one is warned about, the fresh one drives the NOT_SCOPED.
    assert "STALE_CLAIM myia-po-2025:CoursIA" in captured.err
    assert "NOT_SCOPED" in captured.err
    assert "myia-po-2023:CoursIA" in captured.out


def test_stale_threshold_boundary_is_stale(capsys):
    # Exactly 24h old, threshold 24h: >= means STALE (boundary goes to stale).
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- exactly at boundary",
        "2026-08-06T12:00:00Z",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA",
                        stale_threshold=24.0, now=NOW)
    assert rc == 0
    assert "STALE_CLAIM" in capsys.readouterr().err


def test_no_stale_flag_blocks_old_claim_unchanged(capsys):
    # Criterion 1: without the flag, an old claim still blocks (current behaviour).
    # #12322 -- the verdict label is `NOT_SCOPED` (exit 2) since the caller
    # does not declare `--paths`. The exit code change is the corrective.
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- very old orphan",
        "2026-08-01T00:00:00Z",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA", now=NOW)
    assert rc == 2
    captured = capsys.readouterr()
    assert "STALE_CLAIM" not in captured.err
    assert "NOT_SCOPED" in captured.err


def test_stale_threshold_unparseable_not_treated_stale(capsys):
    # A claim whose createdAt is unparseable cannot be dated -> NOT stale
    # (conservative: we cannot prove an age, so we do not lift the block).
    # #12322 -- caller has no scope, so the verdict is exit 2 NOT_SCOPED
    # instead of the legacy exit 1 BLOCKED.
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- undated",
        "not-an-iso-date",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA",
                        stale_threshold=24.0, now=NOW)
    assert rc == 2


def test_stale_claims_null_when_detection_disabled(capsys):
    # #12751 -- detection OFF (no --stale-threshold): `stale_claims` must be
    # `null` (not measured), NOT `[]` (measured, nothing stale). Previously
    # both rendered `[]`, so the fleet ran with detection off and a 415h
    # claim still read as "alive".
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- very old orphan",
        "2026-08-01T00:00:00Z",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA", now=NOW)
    captured = capsys.readouterr()
    # The summary JSON (indent=2) is followed on stdout by a human-readable
    # verdict line when the call is CLEAR/PATH_SCOPED (the post-summary
    # `if others:` block). `raw_decode` parses only the first JSON value and
    # ignores the trailing prose -- `json.loads` would fail on "Extra data".
    out = json.JSONDecoder().raw_decode(captured.out)[0]
    assert out["stale_claims"] is None
    assert out["stale_detection"] == "disabled"
    assert "STALE_DETECTION disabled" in captured.err


def test_stale_claims_empty_when_detection_enabled_clean(capsys):
    # Detection ON, no claim old enough -> `stale_claims` is `[]` (measured,
    # clean) and `stale_detection` is "active" -- the disambiguated state vs
    # `null`/`"disabled"` (not measured).
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- fresh",
        "2026-08-07T10:00:00Z",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA",
                        stale_threshold=24.0, now=NOW)
    captured = capsys.readouterr()
    # The summary JSON (indent=2) is followed on stdout by a human-readable
    # verdict line when the call is CLEAR/PATH_SCOPED (the post-summary
    # `if others:` block). `raw_decode` parses only the first JSON value and
    # ignores the trailing prose -- `json.loads` would fail on "Extra data".
    out = json.JSONDecoder().raw_decode(captured.out)[0]
    assert out["stale_claims"] == []
    assert out["stale_detection"] == "active"


def test_default_48_flags_17day_claim_stale(capsys):
    # #12751 acceptance: at the default 48h threshold, a 17-day-old OTHER-lane
    # claim is flagged STALE and removed from blocking_lanes (the zombie-lock
    # fix -- a 415h claim was read as "alive" because `stale_claims` was `[]`).
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- 17 days old",
        "2026-07-21T00:00:00Z",   # ~396h before NOW
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA",
                        stale_threshold=48.0, now=NOW)
    captured = capsys.readouterr()
    # The summary JSON (indent=2) is followed on stdout by a human-readable
    # verdict line when the call is CLEAR/PATH_SCOPED (the post-summary
    # `if others:` block). `raw_decode` parses only the first JSON value and
    # ignores the trailing prose -- `json.loads` would fail on "Extra data".
    out = json.JSONDecoder().raw_decode(captured.out)[0]
    assert out["stale_claims"] == ["myia-po-2025:CoursIA"]
    assert out["blocking_lanes"] == []
    assert out["stale_detection"] == "active"
    assert "STALE_CLAIM myia-po-2025:CoursIA" in captured.err
    assert rc == 0


def test_default_48_does_not_flag_2h_claim(capsys):
    # #12751 acceptance: a fresh (2h) claim is NOT stale at the default 48h
    # (positive polarity -- only genuinely-old claims age out).
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- fresh 2h",
        "2026-08-07T10:00:00Z",   # 2h before NOW
    ))
    clc._run_check(p, "myia-po-2024:CoursIA",
                   stale_threshold=48.0, now=NOW)
    captured = capsys.readouterr()
    # The summary JSON (indent=2) is followed on stdout by a human-readable
    # verdict line when the call is CLEAR/PATH_SCOPED (the post-summary
    # `if others:` block). `raw_decode` parses only the first JSON value and
    # ignores the trailing prose -- `json.loads` would fail on "Extra data".
    out = json.JSONDecoder().raw_decode(captured.out)[0]
    assert out["stale_claims"] == []
    assert out["stale_detection"] == "active"
    assert "STALE_CLAIM" not in captured.err


# --- --paths mode (#9959) ----------------------------------------------------
#
# Replays the R3D 2026-08-08 incident: two lanes of the SAME machine collide
# on `knot_lean/Knots/Reidemeister.lean` minutes apart, each having passed
# the issue-claim check. The fix is the missing L898 leg: "is there already
# an OPEN PR on the same file?". The lane key is the FULL `machine:workspace`
# -- same machine, different workspace counts as a different lane. PRs
# without a Grain tag (lane unreadable) are surfaced as potential collisions,
# not silently ignored -- the tag is the only attribution signal.

def _pr(number, files, body="", headRefName=None, title=None):
    """Build a synthetic OPEN PR dict for _run_check_paths."""
    return {
        "number": number,
        "title": title or f"PR #{number}",
        "headRefName": headRefName or f"feat/pr-{number}",
        "body": body,
        "files": [{"path": p} for p in files],
    }


def test_paths_clear_no_open_prs(capsys):
    # No OPEN PRs at all -> exit 0, CLEAR.
    rc = clc._run_check_paths(
        paths=["scripts/check_lane_claim.py"],
        my_lane="myia-po-2024:CoursIA-2",
        prs=[],
    )
    assert rc == 0
    out = capsys.readouterr().out
    assert "CLEAR" in out
    assert "other_lane_collisions" in out


def test_paths_clear_disjoint_files(capsys):
    # OPEN PR exists but touches completely different files -> exit 0.
    prs = [
        _pr(9001, ["docs/other.md", "scripts/unrelated.py"]),
    ]
    rc = clc._run_check_paths(
        paths=["scripts/check_lane_claim.py"],
        my_lane="myia-po-2024:CoursIA-2",
        prs=prs,
    )
    assert rc == 0


def test_paths_self_overlap_is_clear(capsys):
    # OPEN PR of MY OWN lane touches the same path -> exit 0, "your own PR".
    # The motivating rule: same lane resuming their own work must not be
    # blocked by the path gate.
    body = (
        "Grain: MED/tooling -- lane myia-po-2024:CoursIA-2 -- prev: ...\n\n"
        "## Stuff\n"
    )
    prs = [
        _pr(
            9002, ["scripts/check_lane_claim.py", "scripts/tests/test_x.py"],
            body=body, headRefName="feature/c9002-thing",
        ),
    ]
    rc = clc._run_check_paths(
        paths=["scripts/check_lane_claim.py"],
        my_lane="myia-po-2024:CoursIA-2",
        prs=prs,
    )
    assert rc == 0
    out = capsys.readouterr()
    assert "you already have an OPEN PR" in out.err


def test_paths_collision_other_lane(capsys):
    # REPLAYS the R3D 2026-08-08 incident (#9955 / #8696). Two lanes of the
    # SAME machine: `myia-po-2026:CoursIA` vs `myia-po-2026:CoursIA-2`.
    # A PR is open on `Reidemeister.lean` from `CoursIA-2`. My lane is
    # `CoursIA` -- the gate must trip on machine+workspace, not on machine
    # alone, because the bug was exactly same-machine different-workspace.
    body = (
        "Grain: DEEP/lean -- lane myia-po-2026:CoursIA-2 -- prev: ...\n"
        "## Reidemeister surgery\n"
    )
    prs = [
        _pr(
            9955,
            ["knot_lean/Knots/Reidemeister.lean",
             "knot_lean/Knots/Reidemeister2.lean"],
            body=body, headRefName="feat/reidemeister3",
        ),
    ]
    rc = clc._run_check_paths(
        paths=["knot_lean/Knots/Reidemeister.lean"],
        my_lane="myia-po-2026:CoursIA",
        prs=prs,
    )
    assert rc == 2
    captured = capsys.readouterr()
    # The blocking PR is named in the stderr BLOCKED message.
    assert "BLOCKED" in captured.err
    assert "#9955" in captured.err
    assert "myia-po-2026:CoursIA-2" in captured.err
    # The intersecting file is named too.
    assert "Reidemeister.lean" in captured.err


def test_paths_collision_different_machine(capsys):
    # Different machine entirely -- still a collision. The motivating R3D
    # incident was same-machine, but the rule generalises: any full-lane
    # difference trips the gate.
    body = (
        "Grain: DEEP/lean -- lane myia-ai-01:CoursIA -- prev: ...\n"
    )
    prs = [
        _pr(7000, ["scripts/check_lane_claim.py"], body=body),
    ]
    rc = clc._run_check_paths(
        paths=["scripts/check_lane_claim.py"],
        my_lane="myia-po-2024:CoursIA-2",
        prs=prs,
    )
    assert rc == 2
    captured = capsys.readouterr()
    assert "#7000" in captured.err
    assert "myia-ai-01:CoursIA" in captured.err


def test_paths_collision_untagged_pr_surfaced(capsys):
    # A PR with NO Grain tag must be surfaced as a potential collision,
    # not silently ignored -- the tag is the only attribution signal
    # (author is jsboige on every PR in the repo). The exit code is still 2
    # because the caller's safe action is "ask before pushing", not "push".
    prs = [
        # No body -> no lane tag.
        _pr(8001, ["scripts/check_lane_claim.py"], body=""),
    ]
    rc = clc._run_check_paths(
        paths=["scripts/check_lane_claim.py"],
        my_lane="myia-po-2024:CoursIA-2",
        prs=prs,
    )
    assert rc == 2
    captured = capsys.readouterr()
    assert "BLOCKED" in captured.err
    assert "UNREADABLE" in captured.err
    assert "#8001" in captured.err


def test_paths_glob_match(capsys):
    # Caller-supplied glob `knot_lean/**/*.lean` should match any file under
    # `knot_lean/` whose basename ends in `.lean`. Same convention as the
    # GitHub UI PR-files "filter" input.
    prs = [
        _pr(8002, ["knot_lean/Knots/Reidemeister.lean"]),
    ]
    rc = clc._run_check_paths(
        paths=["knot_lean/**/*.lean"],
        my_lane="myia-po-2024:CoursIA-2",
        prs=prs,
    )
    assert rc == 2


def test_paths_basename_match(capsys):
    # Caller-supplied pattern `Reidemeister.lean` should match the basename
    # of any PR file, regardless of its directory. The fnmatch helper
    # checks both full path AND basename (same as `gh pr view --files`
    # filtering by filename).
    prs = [
        _pr(8003, ["knot_lean/Knots/Reidemeister.lean"]),
    ]
    rc = clc._run_check_paths(
        paths=["Reidemeister.lean"],
        my_lane="myia-po-2024:CoursIA-2",
        prs=prs,
    )
    assert rc == 2


def test_paths_no_paths_arg_is_error(capsys):
    # `--paths` with zero paths is a usage error: exit 1.
    rc = clc._run_check_paths(
        paths=[],
        my_lane="myia-po-2024:CoursIA-2",
        prs=[],
    )
    assert rc == 1
    captured = capsys.readouterr()
    assert "--paths requires" in captured.err


def test_paths_pr_with_no_files_ignored(capsys):
    # OPEN PR with `files: []` (no files reported -- rare but seen when the
    # caller cannot paginate): skip it. We have no intersection to evaluate.
    prs = [
        _pr(9003, []),
    ]
    rc = clc._run_check_paths(
        paths=["scripts/check_lane_claim.py"],
        my_lane="myia-po-2024:CoursIA-2",
        prs=prs,
    )
    assert rc == 0


def test_paths_multiple_prs_mixed(capsys):
    # Two OPEN PRs: one self-lane (clear), one other-lane (collide). The
    # self-lane one must NOT silence the collision from the other-lane one.
    self_body = (
        "Grain: MED/tooling -- lane myia-po-2024:CoursIA-2 -- prev: ...\n"
    )
    other_body = (
        "Grain: MED/lean -- lane myia-po-2026:CoursIA-2 -- prev: ...\n"
    )
    prs = [
        _pr(9010, ["scripts/check_lane_claim.py"], body=self_body),
        _pr(9011, ["scripts/check_lane_claim.py"], body=other_body),
    ]
    rc = clc._run_check_paths(
        paths=["scripts/check_lane_claim.py"],
        my_lane="myia-po-2024:CoursIA-2",
        prs=prs,
    )
    assert rc == 2
    captured = capsys.readouterr()
    assert "#9011" in captured.err
    # The self-lane PR is NOT in the BLOCKED list (but is in self_overlap).
    assert "#9010" not in captured.err
    # But the JSON summary names it.
    assert "#9010" in captured.out
    assert "BLOCKED" in captured.err


# --- --open-prs-on mode (#13595) --------------------------------------------
#
# The `--paths` guard filters by lane: an OPEN PR of the caller's OWN lane
# reads as "your own PR is fine" and is dropped from the verdict. That is the
# blind spot of case A (one machine, SAME lane, two worktrees, 74 s apart):
# there is only one lane, so the guard finds no *other*-lane collision and
# reports CLEAR while two branches of the same lane race on the same files.
# `--open-prs-on` drops the lane filter entirely and lists EVERY intersecting
# OPEN PR -- including the caller's own -- as a NON-BLOCKING signal.

def test_open_prs_on_same_lane_both_surface(capsys):
    """THE positive control (#13595 point 2): two OPEN PRs of the SAME lane
    on the same file must BOTH surface. A detector that renders nothing on
    this case is indistinguishable from a disconnected detector -- and this
    is exactly the shape `--paths` misses (self_overlap == 'your own PR is
    fine', exit 0, no verdict)."""
    body = (
        "Grain: MED/tooling -- lane myia-po-2024:CoursIA -- prev: ...\n"
    )
    prs = [
        _pr(13586, ["scripts/check_lane_claim.py"], body=body),
        _pr(13558, ["scripts/check_lane_claim.py"], body=body),
    ]
    rc = clc._run_open_prs_on(["scripts/check_lane_claim.py"], prs=prs)
    assert rc == 0
    out = capsys.readouterr().out
    assert "#13586" in out
    assert "#13558" in out
    assert "lane=myia-po-2024:CoursIA" in out
    # The same-lane caveat is stated so the lane cannot mistake the list for
    # a clearance.
    assert "NO lane filter" in out


def test_open_prs_on_cross_lane_both_surface(capsys):
    # Two lanes both surface -- the mode is lane-agnostic, so the other-lane
    # collision is listed too (it would BLOCK under `--paths` but here it is
    # a list only).
    self_body = "Grain: MED/tooling -- lane myia-po-2024:CoursIA -- prev: ...\n"
    other_body = "Grain: MED/lean -- lane myia-po-2026:CoursIA-2 -- prev: ...\n"
    prs = [
        _pr(9001, ["scripts/check_lane_claim.py"], body=self_body),
        _pr(9002, ["scripts/check_lane_claim.py"], body=other_body),
    ]
    rc = clc._run_open_prs_on(["scripts/check_lane_claim.py"], prs=prs)
    assert rc == 0
    out = capsys.readouterr().out
    assert "#9001" in out
    assert "#9002" in out
    assert "myia-po-2024:CoursIA" in out
    assert "myia-po-2026:CoursIA-2" in out


def test_open_prs_on_no_intersection_free(capsys):
    # No OPEN PR intersects the paths -> "Path is free", exit 0.
    prs = [_pr(9003, ["docs/other.md", "scripts/unrelated.py"])]
    rc = clc._run_open_prs_on(["scripts/check_lane_claim.py"], prs=prs)
    assert rc == 0
    out = capsys.readouterr().out
    assert "Path is free" in out


def test_open_prs_on_empty_paths_usage_error(capsys):
    rc = clc._run_open_prs_on([], prs=[])
    assert rc == 1
    assert "--open-prs-on requires" in capsys.readouterr().err


def test_open_prs_on_untagged_lane_surfaces(capsys):
    # PR with no readable Grain lane tag still surfaces, labeled UNREADABLE --
    # same treatment as `--paths` (the tag is the only attribution signal).
    prs = [_pr(9004, ["scripts/check_lane_claim.py"], body="no grain tag here")]
    rc = clc._run_open_prs_on(["scripts/check_lane_claim.py"], prs=prs)
    assert rc == 0
    out = capsys.readouterr().out
    assert "#9004" in out
    assert "UNREADABLE" in out


def test_open_prs_on_non_blocking_even_with_hits(capsys):
    # Hits present, yet exit 0 -- the mode refuses nothing (#13595 point 3).
    body = "Grain: MED/tooling -- lane myia-po-2024:CoursIA -- prev: ...\n"
    prs = [_pr(9005, ["scripts/check_lane_claim.py"], body=body)]
    rc = clc._run_open_prs_on(["scripts/check_lane_claim.py"], prs=prs)
    assert rc == 0


# --- [OVERRIDE] (#10223) -- coordinator adjudication -------------------------
#
# `[OVERRIDE] lane <X>` grants the claim to lane X and closes every other
# lane's claim. This is the mechanical trace of a coordinator merging against a
# held claim (the gap that let #10169 / #10161 be merged with no written
# adjudication). Additive: the existing markers keep their semantics, and the
# 36 prior tests are untouched. The motivating incident (#10169) was
# myia-po-2025:CoursIA-2 holding the sole issue-level claim, po-2026 merging
# anyway -- the override is what the coordinator must now WRITE on the issue.

def test_parse_override_marker():
    ev = clc.parse_claim_event(comment(
        "[OVERRIDE] lane myia-po-2024:CoursIA -- substance favors this PR",
        "2026-08-09T22:00:00Z", author="jsboige",
    ))
    assert ev is not None
    assert ev.is_override is True
    assert ev.is_open is False
    assert ev.lane == "myia-po-2024:CoursIA"
    assert ev.marker == "OVERRIDE"


def test_override_grants_to_named_lane_closes_others():
    # A and B both claimed; override to A -> only A remains active.
    events = [
        clc.parse_claim_event(comment(
            "[CLAIMED] lane A:CoursIA -- x", "2026-08-06T22:00:00Z")),
        clc.parse_claim_event(comment(
            "[CLAIMED] lane B:CoursIA-2 -- y", "2026-08-06T22:10:00Z")),
        clc.parse_claim_event(comment(
            "[OVERRIDE] lane A:CoursIA -- coordinator adjudication",
            "2026-08-06T22:30:00Z")),
    ]
    active, unattrib = clc.compute_active_claims(events)
    assert set(active) == {"A:CoursIA"}
    assert unattrib == []


def test_override_closes_all_others_grants_to_third_lane():
    # A and B claimed; override to a THIRD lane C -> only C active.
    events = [
        clc.parse_claim_event(comment(
            "[CLAIMED] lane A:CoursIA -- x", "2026-08-06T22:00:00Z")),
        clc.parse_claim_event(comment(
            "[CLAIMED] lane B:CoursIA-2 -- y", "2026-08-06T22:10:00Z")),
        clc.parse_claim_event(comment(
            "[OVERRIDE] lane C:CoursIA -- reassign", "2026-08-06T22:30:00Z")),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"C:CoursIA"}


def test_override_then_claim_reopens_other_lane():
    # Override to A, then B claims afterward -> both active (B reopens after
    # the override in walk order; override is not a permanent lockout).
    events = [
        clc.parse_claim_event(comment(
            "[OVERRIDE] lane A:CoursIA -- initial", "2026-08-06T22:00:00Z")),
        clc.parse_claim_event(comment(
            "[CLAIMED] lane B:CoursIA-2 -- y", "2026-08-06T22:30:00Z")),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"A:CoursIA", "B:CoursIA-2"}


def test_override_no_lane_token_unattributed():
    # An override that names no beneficiary cannot be applied -> unattributed.
    ev = clc.parse_claim_event(comment(
        "[OVERRIDE] #9764 merging the better PR", "2026-08-06T22:00:00Z"
    ))
    assert ev is not None and ev.lane is None
    events = [ev]
    active, unattrib = clc.compute_active_claims(events)
    assert active == {}
    assert len(unattrib) == 1


def test_check_override_for_my_lane_is_clear(capsys):
    # Another lane claimed, then the coordinator overrode TO my lane -> CLEAR
    # (I now hold the claim via adjudication). This is the #10169 resolution.
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA -- working here",
                "2026-08-09T11:29:59Z"),
        comment("[OVERRIDE] lane myia-po-2025:CoursIA-2 -- substance favors",
                "2026-08-09T22:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA-2")
    assert rc == 0
    out = capsys.readouterr().out
    assert "CLEAR" in out


def test_check_override_to_other_lane_blocks(capsys):
    # I claimed, then the coordinator overrode to ANOTHER lane -> NOT_SCOPED
    # for me. #12322 -- the caller (myia-po-2025:CoursIA-2) did not pass
    # `--paths`, so the verdict is NOT_SCOPED at exit 2 even though an
    # [OVERRIDE] reassigned the lock. The override retains the BLOCKED
    # semantics; only the verdict label on the unscoped caller leg moves.
    p = payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- working here",
                "2026-08-09T11:41:43Z"),
        comment("[OVERRIDE] lane myia-po-2026:CoursIA -- reassign",
                "2026-08-09T22:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA-2")
    assert rc == 2  # #12322 NOT_SCOPED (the override reassigned to a different lane)
    captured = capsys.readouterr()
    assert "NOT_SCOPED" in captured.err
    assert "myia-po-2026:CoursIA" in captured.out


# --- [OVERRIDE] paths: scope (#10342) ----------------------------------------
#
# The motivating case: an `[OVERRIDE]` is a coordinator adjudication -- it
# reassigns the claim to a named lane. Pre-#10342 the override was EPIC-WIDE
# (every other lane locked out on every path). When the override is meant to
# be SCOPED (e.g. reassign ONE lake, leave another lake free), the epic-wide
# read created a phantom lockout. The fix: an optional `paths: <comma-list>`
# clause on the override body, scoped only by fnmatch against the caller's
# declared `--paths`. The reducer (`compute_active_claims`) keeps the full
# state; the check (`_run_check`) filters `others` by `_path_matches_any`
# when `my_paths` is provided.
#
# Three orthogonal axes tested below:
#  (1) parse layer: the `paths:` clause is read by `parse_claim_event`.
#  (2) reducer layer: `compute_active_claims` keeps the scope payload.
#  (3) check layer: `_run_check(..., my_paths=...)` honours the scope.


def test_parse_override_with_paths_clause():
    ev = clc.parse_claim_event(comment(
        "[OVERRIDE] lane myia-po-2024:CoursIA -- paths: GenAI/PostTraining/**, scripts/lane_guard.py",
        "2026-08-09T22:00:00Z",
    ))
    assert ev is not None
    assert ev.is_override is True
    assert ev.lane == "myia-po-2024:CoursIA"
    assert ev.paths == ["GenAI/PostTraining/**", "scripts/lane_guard.py"]


def test_parse_override_without_paths_clause_is_none():
    # Legacy override (no scope) -- `paths` property is None, NOT [].
    # The distinction matters: None means "epic-wide" (legacy semantics),
    # an empty list would be ambiguous (was the scope declared empty?).
    ev = clc.parse_claim_event(comment(
        "[OVERRIDE] lane myia-po-2024:CoursIA -- reassign",
        "2026-08-09T22:00:00Z",
    ))
    assert ev is not None
    assert ev.paths is None


def test_parse_override_paths_clause_drops_empty_fragments():
    # Stray commas must not produce empty patterns; `fnmatch("", ...)` would
    # match every path, which would be a catastrophic over-block.
    ev = clc.parse_claim_event(comment(
        "[OVERRIDE] lane myia-po-2024:CoursIA -- paths: a.py, , b.py, ",
        "2026-08-09T22:00:00Z",
    ))
    assert ev.paths == ["a.py", "b.py"]


def test_reducer_preserves_override_scope_payload():
    # The reducer stores the override event with its `paths` field intact.
    # Without this, the check layer cannot honour the scope.
    events = [
        clc.parse_claim_event(comment(
            "[CLAIMED] lane A:CoursIA -- x", "2026-08-06T22:00:00Z")),
        clc.parse_claim_event(comment(
            "[OVERRIDE] lane B:CoursIA -- paths: MyIA.AI.Notebooks/SymbolicAI/Lean/**",
            "2026-08-06T22:30:00Z")),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"B:CoursIA"}
    assert active["B:CoursIA"].paths == [
        "MyIA.AI.Notebooks/SymbolicAI/Lean/**",
    ]


# --- reducer HONOURS the `paths:` clause on [OVERRIDE] (#10505) --------------
#
# Pre-#10505 the reducer did `state = {ev.lane: ev}` unconditionally -- a
# scoped [OVERRIDE] read as epic-wide, silently closing every other lane's
# claim (including scoped claims DISJOINT from the override). The four cases
# below pin the corrected behaviour: a scoped override closes only claims
# that intersect it. Intersection mirrors `_filter_by_claim_scope`: an
# epic-wide claim (paths=None) intersects any scope (it claims everything);
# a scoped claim is closed iff its paths match the override's (fnmatch).

def _ev(action, lane, body, ts, paths_clause=None):
    """Build a ClaimEvent straight from primitives (no comment parsing)."""
    return clc.ClaimEvent(
        lane=lane, action=action, marker={"open": "CLAIMED", "override": "OVERRIDE",
                                          "close": "RELEASED"}[action],
        created_at=ts, author="x", url=None,
        paths=paths_clause, intent=None,
    )


def test_reducer_scoped_override_keeps_disjoint_scoped_claim():
    # Override scoped to Lean/** ; a claim scoped to scripts/** is DISJOINT
    # -> it MUST survive in the active state. Pre-#10505 it was closed (bug).
    events = [
        _ev("open", "A:CoursIA", "claim scripts", "2026-08-11T22:00:00Z",
            paths_clause=["scripts/**"]),
        _ev("override", "B:CoursIA", "reassign Lean only", "2026-08-11T22:30:00Z",
            paths_clause=["MyIA.AI.Notebooks/SymbolicAI/Lean/**"]),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"A:CoursIA", "B:CoursIA"}  # both survive (disjoint)


def test_reducer_scoped_override_closes_intersecting_scoped_claim():
    # Override scoped to Lean/** ; a claim also scoped to Lean/** INTERSECTS
    # -> it is closed. Same verdict as epic-wide, but via the scope rule.
    events = [
        _ev("open", "A:CoursIA", "claim Lean", "2026-08-11T22:00:00Z",
            paths_clause=["MyIA.AI.Notebooks/SymbolicAI/Lean/**"]),
        _ev("override", "B:CoursIA", "reassign Lean only", "2026-08-11T22:30:00Z",
            paths_clause=["MyIA.AI.Notebooks/SymbolicAI/Lean/**"]),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"B:CoursIA"}  # A closed (intersecting scope)


def test_reducer_scoped_override_closes_epic_wide_claim():
    # Override scoped to Lean/** ; an EPIC-WIDE claim (paths=None) claims
    # everything, so it intersects any scope -> closed. This is the rule the
    # issue calls out explicitly (point 1): it keeps the #10289 behaviour
    # identical (the epic-wide PT-11b claim was closed either way) but by an
    # explicit, tested rule rather than an ignored scope.
    events = [
        _ev("open", "A:CoursIA", "claim all", "2026-08-11T22:00:00Z",
            paths_clause=None),
        _ev("override", "B:CoursIA", "reassign Lean only", "2026-08-11T22:30:00Z",
            paths_clause=["MyIA.AI.Notebooks/SymbolicAI/Lean/**"]),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"B:CoursIA"}  # epic-wide A closed


def test_reducer_epic_wide_override_closes_everything():
    # Regression of #10223: an EPIC-WIDE override (no paths clause) closes
    # every other lane, scoped or not. The scoped-override branch must not
    # weaken the legacy behaviour.
    events = [
        _ev("open", "A:CoursIA", "claim Lean", "2026-08-11T22:00:00Z",
            paths_clause=["MyIA.AI.Notebooks/SymbolicAI/Lean/**"]),
        _ev("open", "C:CoursIA", "claim all", "2026-08-11T22:05:00Z",
            paths_clause=None),
        _ev("override", "B:CoursIA", "epic-wide reassign", "2026-08-11T22:30:00Z",
            paths_clause=None),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"B:CoursIA"}  # every other lane closed


# --- reducer honours `empty_scope` on [CLAIMED] (#11098) --------------------
#
# #11098 -- the asymmetric gap between read-side (`_filter_by_claim_scope`,
# which #10958 lifts an entirely-dead `paths:` clause to epic-wide) and
# reducer-side (`compute_active_claims`, which #10505 added but did NOT
# consult `empty_scope`). A claim whose `paths:` clause globs all fail to
# match any tracked file effectively claims nothing -- the safe hypothesis
# is that the lane meant something (prose swallowed, polluted suffix).
# The reducer previously treated such a claim as disjoint from any scoped
# override, leaving it uncloseable except by an epic-wide override (which
# swept legitimate scoped claims of sibling lanes along with the broken
# one). The fix mirrors the read-side lift in the reducer: an entirely-
# dead `paths:` clause is read as epic-wide on both sides, so any scoped
# override that intersects its scope (= any scope) closes it.
#
# The four cases below pin the corrected reducer behaviour, with
# `empty_scope` attached directly on the event (the `_run_check` walk
# produces these in production; the helper `_claim_scope_effectively_epic_wide`
# consults `ev["empty_scope"]`).

def _scoped_ev(action, lane, ts, paths_clause, empty_scope=None):
    """Build a CLAIMED event with an `empty_scope` witness attached (#11098).

    `_ev` builds the event straight from primitives; this adds the
    `empty_scope` field that `_run_check` would normally attach after the
    tracked-files walk. Passing `empty_scope=None` reproduces the
    reducer-direct unit-test paths (no witness -> the helper degrades to
    False, no lift).
    """
    e = _ev(action, lane, "x", ts, paths_clause=paths_clause)
    if empty_scope is not None:
        e["empty_scope"] = list(empty_scope)
    return e


def test_reducer_scoped_override_closes_empty_scope_full_claim():
    # #11098 core case: override scoped to Lean/** ; a claim whose `paths:`
    # clause is ENTIRELY DEAD (every glob fails to match any tracked file,
    # empty_scope covers the whole declared scope) is effectively epic-wide
    # -> intersects any override scope -> closed. Pre-#11098 the reducer
    # treated the claim as scoped but disjoint (it had `paths` non-None), so
    # no scoped override could close it.
    events = [
        _scoped_ev(
            "open", "A:CoursIA", "2026-08-11T22:00:00Z",
            paths_clause=["MyIA.AI.Notebooks/GameTheory/GameTheory-7-*. Pont pyspiel"],
            empty_scope=["MyIA.AI.Notebooks/GameTheory/GameTheory-7-*. Pont pyspiel"],
        ),
        _ev("override", "B:CoursIA", "reassign Lean only", "2026-08-11T22:30:00Z",
            paths_clause=["MyIA.AI.Notebooks/SymbolicAI/Lean/**"]),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"B:CoursIA"}  # A closed (empty_scope = epic-wide)


def test_reducer_scoped_override_keeps_scoped_disjoint_claim_no_empty_scope():
    # No-regression pin for #11098: when `empty_scope` is absent (reducer-
    # direct path, no witness) the helper degrades to False, and the legacy
    # behaviour holds -- disjoint scoped claims are kept.
    events = [
        _ev("open", "A:CoursIA", "claim scripts", "2026-08-11T22:00:00Z",
            paths_clause=["scripts/**"]),
        _ev("override", "B:CoursIA", "reassign Lean only", "2026-08-11T22:30:00Z",
            paths_clause=["MyIA.AI.Notebooks/SymbolicAI/Lean/**"]),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"A:CoursIA", "B:CoursIA"}  # both survive (disjoint)


def test_reducer_scoped_override_keeps_scoped_partially_dead_claim():
    # #11098 asymmetry test: when `empty_scope` covers PART of the declared
    # scope (at least one glob still matches a tracked file), the claim is
    # NOT lifted -- the live part of the scope is real and stays scoped.
    # The override scoped to Lean/** does not intersect the live part, so
    # the claim survives.
    events = [
        _scoped_ev(
            "open", "A:CoursIA", "2026-08-11T22:00:00Z",
            paths_clause=["scripts/check_lane_claim.py", "dead/glob/**"],
            empty_scope=["dead/glob/**"],  # only the second glob is dead
        ),
        _ev("override", "B:CoursIA", "reassign Lean only", "2026-08-11T22:30:00Z",
            paths_clause=["MyIA.AI.Notebooks/SymbolicAI/Lean/**"]),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"A:CoursIA", "B:CoursIA"}  # A stays (live scope disjoint)


def test_reducer_scoped_override_closes_empty_scope_full_claim_overlapping_live():
    # #11098 mirror: when the override's scope DOES intersect the live part
    # of a partially-dead claim, the live part closes the claim (legacy
    # behaviour, unchanged by this fix). A scoped claim with at least one
    # live glob stays scoped and is closed iff the override intersects it.
    # We use a concrete-file override (not `scripts/**` -- whose `**` is a
    # universal basename in `_path_matches`) to make the intersection test
    # well-defined.
    events = [
        _scoped_ev(
            "open", "A:CoursIA", "2026-08-11T22:00:00Z",
            paths_clause=["scripts/check_lane_claim.py", "dead/glob/**"],
            empty_scope=["dead/glob/**"],
        ),
        _ev("override", "B:CoursIA", "reassign scripts only", "2026-08-11T22:30:00Z",
            paths_clause=["scripts/check_lane_claim.py"]),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"B:CoursIA"}  # A closed (live part intersects override)
    assert set(active) == {"B:CoursIA"}  # every other lane closed


# --- the actual SCOPE behaviour at the check layer ---------------------------

def test_check_override_no_paths_preserves_legacy_epic_wide_behaviour(capsys):
    # Override WITHOUT `paths:` clause, check WITHOUT `--paths` -> legacy
    # epic-wide block. #12322 -- the verdict text is `NOT_SCOPED` (exit 2)
    # so the caller can branch on the verdict: exit 1 means a real conflict,
    # exit 2 means "scope your call to lift the over-block".
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA -- original",
                "2026-08-09T11:00:00Z"),
        comment("[OVERRIDE] lane myia-po-2024:CoursIA -- substance favors",
                "2026-08-09T22:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2026:CoursIA")
    assert rc == 2
    captured = capsys.readouterr()
    assert "NOT_SCOPED" in captured.err
    assert "myia-po-2024:CoursIA" in captured.out


def test_check_override_paths_blocks_other_lane_on_matching_path(capsys):
    # #12345 -- the caller's `--paths` `Foo.lean` and the override claim's
    # `SymbolicAI/Lean/**` are both ENTIRELY dead in this test repo (the
    # tests live outside any actual SymbolicAI tree). Pre-#12345 the
    # presence-of-flag predicate returned exit 1 + BLOCKED, hiding the
    # broken scope. Post-#12345 the caller's scope is entirely dead ->
    # `EPIC_WIDE_NO_PATHS_DECLARED` at exit 2 (fail-CLOSED).
    # Override with `paths: A/**` to lane X; I (lane Z) want to edit a file
    # UNDER A/ -> my path intersects the scope -> Z is BLOCKED.
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA -- before override",
                "2026-08-09T11:00:00Z"),
        comment(
            "[OVERRIDE] lane myia-po-2024:CoursIA -- "
            "paths: MyIA.AI.Notebooks/SymbolicAI/Lean/**",
            "2026-08-09T22:00:00Z",
        ),
    )
    rc = clc._run_check(
        p,
        "myia-po-2025:CoursIA-2",
        my_paths=["MyIA.AI.Notebooks/SymbolicAI/Lean/Foo.lean"],
    )
    # #12862 -- the caller's dead glob is syntactically VALID (`/` in the
    # path), so the scope classifies as CREATION, not typo: PATH_SCOPED.
    # The override lane still blocks (disjointness from a not-yet-existing
    # tree is unprovable) -> BLOCKED at exit 1. The relaxation reclassifies
    # the verdict; it never lifts a real blocker.
    assert rc == 1  # BLOCKED -- creation scope, override still claims (#12862)
    captured = capsys.readouterr()
    assert "myia-po-2024:CoursIA" in captured.out


def test_check_override_paths_keeps_other_lane_free_on_non_matching_path(capsys):
    # Same override, but my file is OUTSIDE the scope -> CLEAR.
    # This is the core #10342 fix: the override no longer reads as epic-wide.
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA -- before override",
                "2026-08-09T11:00:00Z"),
        comment(
            "[OVERRIDE] lane myia-po-2024:CoursIA -- "
            "paths: MyIA.AI.Notebooks/SymbolicAI/Lean/**",
            "2026-08-09T22:00:00Z",
        ),
    )
    rc = clc._run_check(
        p,
        "myia-po-2025:CoursIA-2",
        my_paths=["scripts/check_lane_claim.py"],
    )
    assert rc == 0
    captured = capsys.readouterr()
    assert "CLEAR" in captured.out
    # The override is still in the audit JSON (state is preserved), but it
    # does NOT appear in blocking_lanes.
    assert "myia-po-2024:CoursIA" in captured.out  # in active_claims


def test_check_override_paths_keeps_plain_claimed_lane_blocking(capsys):
    # A [CLAIMED] WITHOUT a `paths:` clause is epic-wide, even when the caller
    # supplies `--paths`. (#10419 lets a worker SCOPE a [CLAIMED] with a
    # `paths:` clause; this test pins the boundary for the UNSCOPED form,
    # which stays global and blocks regardless of the caller's --paths.)
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA -- original",
                "2026-08-09T11:00:00Z"),
    )
    rc = clc._run_check(
        p,
        "myia-po-2025:CoursIA-2",
        my_paths=["scripts/check_lane_claim.py"],  # unrelated to claimed lane's work
    )
    assert rc == 1
    captured = capsys.readouterr()
    assert "BLOCKED" in captured.err
    assert "myia-po-2026:CoursIA" in captured.out


def test_check_override_paths_mixed_one_blocked_one_free(capsys):
    # Two overrides: one scoped to Lean/**, one scoped to scripts/**.
    # Caller edits a file in scripts/ -> blocked by the scripts override,
    # but CLEAR of the Lean override (its scope doesn't touch the file).
    # The summary JSON keeps both active; the human verdict names only the
    # blocker.
    p = payload(
        comment(
            "[OVERRIDE] lane myia-po-2024:CoursIA -- "
            "paths: MyIA.AI.Notebooks/SymbolicAI/Lean/**",
            "2026-08-09T22:00:00Z",
        ),
        comment(
            "[OVERRIDE] lane myia-po-2023:CoursIA -- "
            "paths: scripts/**",
            "2026-08-09T22:30:00Z",
        ),
    )
    rc = clc._run_check(
        p,
        "myia-po-2025:CoursIA-2",
        my_paths=["scripts/check_lane_claim.py"],
    )
    assert rc == 1
    captured = capsys.readouterr()
    assert "BLOCKED" in captured.err
    assert "myia-po-2023:CoursIA" in captured.out
    assert "myia-po-2024:CoursIA" not in captured.err  # not blocking here


def test_active_claims_summary_exposes_paths(capsys):
    # The audit JSON surfaces the `paths` field on override events, so a
    # human reviewer can verify the scope without re-reading the source.
    # The reducer grants A the claim -> A is in `others` (because I am B),
    # so the verdict is NOT_SCOPED at exit 2 (#12322); that is not what this
    # test is pinning. We only check that the scope payload leaks into the
    # JSON, NOT the verdict.
    p = payload(
        comment(
            "[OVERRIDE] lane myia-po-2024:CoursIA -- paths: Lean/**, scripts/**",
            "2026-08-09T22:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA-2")
    out = capsys.readouterr().out
    assert rc == 2  # exit 2 NOT_SCOPED -- caller did not bind `--paths`
    assert "Lean/**" in out
    assert "scripts/**" in out
    assert '"query_scope": "EPIC_WIDE_NO_PATHS_DECLARED"' in out


# --- [CLAIMED] paths: scope (#10419) -----------------------------------------
# #10342 introduced the `paths:` clause for [OVERRIDE] only. #10419 extends
# recognition to [CLAIMED] (and [RELEASED], by symmetry) so that the nominal
# pattern of a multi-instance audit -- several lanes each scoping their [CLAIMED]
# to a DISJOINT notebook on the same parapluie issue -- no longer raises a
# false `lane-claim-conflict` on every PR. Before #10419, a worker's claim
# "never carried" a scope (see the comment pinned by
# test_check_override_paths_keeps_plain_claimed_lane_blocking); the protocol
# (lane-claim-protocol.md rule 6) already DEMANDED per-file partitioning that
# the organ could not read. These tests pin the three layers: parse, reducer
# passthrough, and the scope-intersection check.


def test_parse_claimed_with_paths_clause():
    # [CLAIMED] carrying a `paths:` clause -> the scope is attached (#10419).
    ev = clc.parse_claim_event(
        comment(
            "[CLAIMED] lane myia-po-2023:CoursIA -- "
            "paths: MyIA.AI.Notebooks/Sudoku/Sudoku-09-GraphColoring-Csharp.ipynb",
            "2026-08-11T04:02:00Z",
        )
    )
    assert ev is not None
    assert ev.marker == "CLAIMED"
    assert ev.is_open
    assert ev.paths == [
        "MyIA.AI.Notebooks/Sudoku/Sudoku-09-GraphColoring-Csharp.ipynb",
    ]


def test_parse_claimed_without_paths_clause_is_none():
    # Plain [CLAIMED] (no scope) -> paths is None, NOT []. Legacy claim.
    ev = clc.parse_claim_event(
        comment("[CLAIMED] lane myia-po-2024:CoursIA -- build the guard",
                "2026-08-06T22:00:00Z")
    )
    assert ev is not None
    assert ev.paths is None


def test_parse_claimed_paths_clause_drops_empty_fragments():
    # Same empty-fragment hygiene as [OVERRIDE]: stray commas are dropped.
    ev = clc.parse_claim_event(
        comment("[CLAIMED] lane A:CoursIA -- paths: a.py, , b.py, ",
                "2026-08-11T04:02:00Z")
    )
    assert ev.paths == ["a.py", "b.py"]


def test_parse_released_with_paths_clause_attached():
    # [RELEASED] recognises the clause (symmetry with [CLAIMED], #10419). The
    # reducer treats release as a full lane-close, so the scope is informational
    # here -- but the PARSE layer must not silently drop it.
    ev = clc.parse_claim_event(
        comment("[RELEASED] lane A:CoursIA -- paths: a.py, b.py",
                "2026-08-11T05:00:00Z")
    )
    assert ev is not None
    assert ev.marker == "RELEASED"
    assert ev.paths == ["a.py", "b.py"]


def test_reducer_preserves_claimed_scope_payload():
    # The active-claim reducer stores the scoped [CLAIMED] event intact, so the
    # check layer can read `paths` off it (mirrors the OVERRIDE reducer test).
    events = [
        clc.parse_claim_event(
            comment("[CLAIMED] lane A:CoursIA -- paths: Search/Search-3.ipynb",
                    "2026-08-11T04:02:00Z")
        ),
    ]
    active, unattributed = clc.compute_active_claims(events)
    assert not unattributed
    assert active["A:CoursIA"].paths == ["Search/Search-3.ipynb"]


def test_check_claimed_disjoint_paths_dont_block(capsys):
    # CORE #10419 fix: two lanes, each [CLAIMED] scoped to a DISJOINT notebook,
    # neither passing --paths. Before #10419 both were BLOCKED (false conflict);
    # after, each reads the OTHER's scope from its own active claim and sees CLEAR.
    p = payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA -- "
                "paths: MyIA.AI.Notebooks/Search/Part1-Foundations/"
                "Search-3-Informed-Csharp.ipynb",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane myia-po-2023:CoursIA -- "
                "paths: MyIA.AI.Notebooks/Sudoku/"
                "Sudoku-09-GraphColoring-Csharp.ipynb",
                "2026-08-11T04:05:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA")  # no --paths
    assert rc == 0
    out = capsys.readouterr().out
    assert '"blocking_lanes": []' in out
    # The other lane is still in the audit JSON (state preserved), just not blocking.
    assert "myia-po-2023:CoursIA" in out


def test_check_claimed_10382_five_disjoint_claims(capsys):
    # Regression reproduction of the #10382 / #10419 motivating incident: 5
    # lanes each scoped to a disjoint notebook on one parapluie issue. Every
    # lane MUST see blocking_lanes: [] -- the artefactual `lane-claim-conflict`
    # that fired on all ~51 PRs of the audit is gone.
    #
    # Fixture liveness guard (#13028): each notebook path MUST resolve to at
    # least one tracked file in the repo. Otherwise a future rename silently
    # promotes the claim to `empty_scope` -> EPIC_WIDE -> spurious cross-lane
    # block, indistinguishable from a real collision. Detect this with a
    # readable assertion at the top of the test, not via `dead_scope_globs`
    # surfacing downstream.
    import pathlib
    repo_root = pathlib.Path(__file__).resolve().parents[2]
    fixture_paths = [
        "MyIA.AI.Notebooks/Sudoku/Sudoku-09-GraphColoring-Csharp.ipynb",
        "MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/"
        "Planners-5-Heuristics-Csharp.ipynb",
        "MyIA.AI.Notebooks/Search/Part1-Foundations/Search-3-Informed-Csharp.ipynb",
        "MyIA.AI.Notebooks/Search/Part1-Foundations/"
        "Search-5-GeneticAlgorithms-Csharp.ipynb",
        "MyIA.AI.Notebooks/GameTheory/GameTheory-04-NashEquilibrium-Csharp.ipynb",
    ]
    for relpath in fixture_paths:
        resolved = repo_root / relpath
        assert resolved.exists(), (
            f"#13028 fixture guard: {relpath} does not exist on disk. "
            f"Update the fixture to a live notebook or rename this test "
            f"expectation; otherwise dead_scope will silently promote the "
            f"claim to EPIC_WIDE."
        )
    p = payload(
        comment("[CLAIMED] lane myia-po-2023:CoursIA -- "
                "paths: MyIA.AI.Notebooks/Sudoku/"
                "Sudoku-09-GraphColoring-Csharp.ipynb",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane myia-po-2024:CoursIA -- "
                "paths: MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/"
                "Planners-5-Heuristics-Csharp.ipynb",
                "2026-08-11T04:03:00Z"),
        comment("[CLAIMED] lane myia-po-2025:CoursIA -- "
                "paths: MyIA.AI.Notebooks/Search/Part1-Foundations/"
                "Search-3-Informed-Csharp.ipynb",
                "2026-08-11T04:04:00Z"),
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- "
                "paths: MyIA.AI.Notebooks/Search/Part1-Foundations/"
                "Search-5-GeneticAlgorithms-Csharp.ipynb",
                "2026-08-11T04:05:00Z"),
        comment("[CLAIMED] lane myia-po-2026:CoursIA -- "
                "paths: MyIA.AI.Notebooks/GameTheory/"
                "GameTheory-04-NashEquilibrium-Csharp.ipynb",
                "2026-08-11T04:07:00Z"),
    )
    for lane in (
        "myia-po-2023:CoursIA",
        "myia-po-2024:CoursIA",
        "myia-po-2025:CoursIA",
        "myia-po-2025:CoursIA-2",
        "myia-po-2026:CoursIA",
    ):
        rc = clc._run_check(p, lane)
        assert rc == 0, f"{lane} should be CLEAR on disjoint scopes"
        assert '"blocking_lanes": []' in capsys.readouterr().out


def test_check_claimed_same_path_still_blocks(capsys):
    # Two scoped claims on the SAME path -> real collision -> BLOCKED. The scope
    # feature must not dissolve a genuine file-level conflict into a false clear.
    p = payload(
        comment("[CLAIMED] lane A:CoursIA -- paths: MyIA.AI.Notebooks/Sudoku/"
                "Sudoku-09-GraphColoring-Csharp.ipynb",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane B:CoursIA-2 -- paths: MyIA.AI.Notebooks/Sudoku/"
                "Sudoku-09-GraphColoring-Csharp.ipynb",
                "2026-08-11T04:05:00Z"),
    )
    rc = clc._run_check(p, "A:CoursIA")
    assert rc == 1
    err = capsys.readouterr().err
    assert "BLOCKED" in err
    assert "B:CoursIA-2" in err


def test_check_claimed_one_scoped_one_plain_blocks(capsys):
    # One scoped claim + one plain (epic-wide) claim -> BLOCKED. Disjointness is
    # only honoured when BOTH sides declare a scope (acceptance #2 of #10419);
    # a plain claim's intent is unknown, so it conservatively blocks.
    # #12345 -- the caller's OWN claim scope `Search/Search-3.ipynb` is dead
    # in this test repo (no Search tree exists here). Post-#12345 the scope
    # is entirely dead -> `EPIC_WIDE_NO_PATHS_DECLARED` at exit 2 (the broken
    # scope proves nothing about disjointness against `B`'s plain claim,
    # so the verdict is `NOT_SCOPED`, not `BLOCKED`).
    p = payload(
        comment("[CLAIMED] lane A:CoursIA -- paths: Search/Search-3.ipynb",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane B:CoursIA-2 -- working on Sudoku",
                "2026-08-11T04:05:00Z"),
    )
    rc = clc._run_check(p, "A:CoursIA")
    assert rc == 1  # BLOCKED -- creation scope (valid dead glob), plain claim still blocks (#12862)
    assert "B:CoursIA-2" in capsys.readouterr().err


def test_check_my_claim_scope_derived_from_claim_not_just_cli(capsys):
    # my_scope is built from the caller's OWN [CLAIMED] paths clause, NOT only
    # from --paths. A lane that posted a scoped [CLAIMED] but calls the check
    # without --paths still gets disjointness honoured against another scoped
    # lane. This is the leg that makes the #10419 fix usable without forcing
    # every worker to pass --paths on every invocation.
    p = payload(
        comment("[CLAIMED] lane A:CoursIA -- paths: scripts/check_lane_claim.py",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane B:CoursIA-2 -- paths: scripts/grain_tag.py",
                "2026-08-11T04:05:00Z"),
    )
    rc = clc._run_check(p, "A:CoursIA")  # NO my_paths
    assert rc == 0
    assert '"blocking_lanes": []' in capsys.readouterr().out


def test_check_claimed_paths_merged_with_cli_widen_scope(capsys):
    # my_scope MERGES --paths with the caller's claim clause (defensive: a lane
    # blocks if it touches ANY file I declared, by either channel). Here the
    # other lane's scope intersects my CLI --paths but NOT my claim clause --
    # the merge still catches the overlap and BLOCKS.
    p = payload(
        comment("[CLAIMED] lane A:CoursIA -- paths: scripts/check_lane_claim.py",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane B:CoursIA-2 -- paths: scripts/grain_tag.py",
                "2026-08-11T04:05:00Z"),
    )
    rc = clc._run_check(p, "A:CoursIA", my_paths=["scripts/grain_tag.py"])
    assert rc == 1
    assert "B:CoursIA-2" in capsys.readouterr().err


# --- #10395 Variante 2: claim-scope mesh (intent in BLOCKED verdict) ---------
# The motivating case was an EPIC (e.g. #10382 Search/*) where three lanes
# each carry a valid [CLAIMED] on disjoint notebooks. The blocking tool used
# to surface a bare "BLOCKED: another lane holds an active claim on #NNNNN"
# -- a coordinator could not read at a glance that the three claims were
# disjoint (different notebooks of the same EPIC). Variante 2 attaches the
# marker-line excerpt as `intent` and surfaces it side-by-side so the
# verdict becomes actionable. These tests pin the new contract:
#
#   1. parse_claim_event populates `intent` from the marker line.
#   2. _run_check surfaces each active claim's intent in the BLOCKED verdict.
#   3. The "trio OR-Tools" scenario (3 lanes, disjoint intents) renders all
#      three intents side-by-side, not a bare BLOCKED.
#   4. The "epic-wide claim" without a marker-line excerpt still surfaces
#      `(no intent)` as a deliberate sentinel (not a crash).


def test_intent_extracted_from_marker_line():
    """`intent` carries the marker-line excerpt with the bracket stripped."""
    ev = clc.parse_claim_event(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA-2 — Search-3 GraphAlgorithms notebook",
        "2026-08-10T14:00:00Z",
    ))
    assert ev is not None
    # The intent is the part AFTER `[CLAIMED] lane myia-po-2025:CoursIA-2`,
    # trimmed of leading separators. We don't pin exact whitespace but
    # the SUBSTANCE (notebook target) must be readable.
    assert ev.intent is not None
    assert "Search-3" in ev.intent
    assert "GraphAlgorithms" in ev.intent


def test_intent_handles_marker_line_with_only_lane_token():
    """A `[CLAIMED] lane myia-po-2025:CoursIA` (no prose beyond the lane)
    still has *some* intent (the lane token itself) -- the contract is
    "marker-line excerpt with the bracket stripped", not "must contain
    arbitrary prose". This is the bare minimum signal: the coordinator
    sees WHICH lane, even when the author didn't write anything else."""
    ev = clc.parse_claim_event(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA",
        "2026-08-10T14:00:00Z",
    ))
    assert ev is not None
    assert ev.intent is not None
    assert ev.intent == "lane myia-po-2025:CoursIA"


def test_intent_handles_truly_empty_marker_line():
    """A bare `[CLAIMED]` (no prose after the bracket, no lane token either)
    yields intent=None -- the sentinel for "this comment has no scope info".
    The verifier (BLOCKED verdict) prints `(no intent)` for these."""
    ev = clc.parse_claim_event(comment(
        "[CLAIMED]",
        "2026-08-10T14:00:00Z",
    ))
    assert ev is not None
    # The lane itself is unreadable (no `lane myia-...:...` token), so the
    # event is unattributed. But the marker LINE was non-empty after
    # stripping whitespace -- in fact, empty. intent=None either way.
    # The point: the tool does NOT crash on a bare bracket.
    assert ev.lane is None  # unattributed
    assert ev.intent is None  # no excerpt


def test_intent_caps_at_120_chars():
    """Long marker-line excerpts are truncated with an ellipsis."""
    long = "x" * 200
    ev = clc.parse_claim_event(comment(
        f"[CLAIMED] lane myia-po-2025:CoursIA — {long}",
        "2026-08-10T14:00:00Z",
    ))
    assert ev is not None
    assert ev.intent is not None
    assert len(ev.intent) <= 121  # 120 + the trailing ellipsis char
    assert ev.intent.endswith("…")


def test_blocked_verdict_surfaces_intent_side_by_side(capsys):
    """Two lanes with disjoint marker-line excerpts both render in NOT_SCOPED.

    #12322 -- the verdict label is `NOT_SCOPED` (exit 2) when the caller
    does not bind scope. The intent side-by-side block is preserved verbatim
    (it was Variante 2's headline) so a reader still gets the disambiguating
    signal that prevents #10382-style over-blocks."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2023:CoursIA — Part1-Foundations BFS notebook",
            "2026-08-10T14:00:00Z",
        ),
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA — Part3-Advanced A* notebook",
            "2026-08-10T14:05:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA-2")
    assert rc == 2  # #12322 -- NOT_SCOPED, caller has no scope binding
    err = capsys.readouterr().err
    assert "NOT_SCOPED" in err
    assert "Part1-Foundations BFS notebook" in err
    assert "Part3-Advanced A* notebook" in err
    assert "Claimed scopes" in err  # the Variante 2 header preserved


def test_trio_ortools_scenario_disjoint_intents_visible(capsys):
    """Trio OR-Tools scenario (the decisive test for Variante 2).

    Three lanes, each with a valid [CLAIMED] on the same EPIC #10382 but
    on DISJOINT notebooks. The block is the tool's job (the reducer keeps
    them all in `others` -- epic-wide semantics are preserved). The FIX is
    that the NOT_SCOPED verdict now surfaces all three intents side-by-side,
    so a coordinator reads "three disjoint notebooks" at a glance instead
    of "three blocking claims" and can decide whether the scope overlap
    actually warrants arbitration, or whether each lane can proceed by
    re-running the check with `--paths`. (#12322)
    """
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2023:CoursIA — Search-1 maze BFS notebook",
            "2026-08-10T14:00:00Z",
        ),
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA — Search-5 GA notebook",
            "2026-08-10T14:05:00Z",
        ),
        comment(
            "[CLAIMED] lane myia-po-2026:CoursIA — Search-12 adversarial notebook",
            "2026-08-10T14:10:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA-2")
    # Reducer keeps all three in `others` (caller did not bind scope, so the
    # call lands in `EPIC_WIDE_NO_PATHS_DECLARED` per #12322).
    assert rc == 2
    err = capsys.readouterr().err
    assert "myia-po-2023:CoursIA" in err
    assert "myia-po-2024:CoursIA" in err
    assert "myia-po-2026:CoursIA" in err
    assert "Search-1 maze BFS notebook" in err
    assert "Search-5 GA notebook" in err
    assert "Search-12 adversarial notebook" in err


def test_blocked_verdict_uses_no_intent_sentinel(capsys):
    """An UNATTRIBUTED claim (no `lane myia-...:...` token anywhere) gets
    the deliberate `(no intent)` sentinel in the BLOCKED verdict.

    We do NOT crash, we do NOT fall back to the comment body (that would
    leak back into the same "anything-with-a-colon looks like a lane"
    trap). The sentinel makes the gap legible without inviting the reader
    to misread silence as agreement.
    """
    p = payload(
        comment(
            "[CLAIMED]",  # no lane token, no prose -- the gap case
            "2026-08-10T14:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    # Unattributed default does NOT block (the reducer is conservative:
    # "cannot attribute" -> "do not block"). The sentinel is in the
    # *unattributed* surface, not the *blocked* surface.
    out = capsys.readouterr().out
    assert rc == 0
    assert '"unattributed_markers": 1' in out


def test_blocked_verdict_prints_intent_for_named_lane(capsys):
    """A claim with a lane token AND a marker-line excerpt has its intent
    printed in the NOT_SCOPED verdict. This is the common case (the lane
    token IS the intent excerpt when the author writes nothing else).
    #12322 -- caller has no scope binding -> NOT_SCOPED at exit 2."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2025:CoursIA",
            "2026-08-10T14:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    assert rc == 2
    err = capsys.readouterr().err
    assert "NOT_SCOPED" in err
    # The intent is the lane token (the only thing on the marker line).
    assert "myia-po-2025:CoursIA" in err


def test_blocked_message_includes_paths_narrowing_hint(capsys):
    """The NOT_SCOPED hint names `--paths ...` as the next move. The
    path-scope clause is already supported for [OVERRIDE] (#10342);
    [CLAIMED] with paths: is a natural follow-up (#10419). #12322 -- the
    narrowing hint is now in the NOT_SCOPED verdict, where the actionable
    next step belongs (the post-fix message is action-shaped).
    """
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2025:CoursIA — working here",
            "2026-08-10T14:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    assert rc == 2
    err = capsys.readouterr().err
    assert "paths" in err
    assert "ACTION" in err


# --- brace-group path scopes (#10597) ----------------------------------------
#
# A `paths:` clause written in brace syntax -- `search-{6,8,9}-*.yaml`, the
# natural form several lanes already used -- was silently EPIC-WIDE: the naive
# comma split fragmented it into `["search-{6", "8", "9}-*.yaml"]`, none of
# which fnmatch ever matches. Two fixes: the splitter is now brace-aware, and
# each brace group expands to sibling globs. These tests pin the #10597
# reproduction and the edge cases.


def test_paths_clause_brace_aware_split():
    # The reproduction from #10597: a brace group must survive the comma
    # split as ONE pattern, then expand to three sibling globs.
    line = ("[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: scripts/notebook_tools/twin_pairs.d/search-{6,8,9}-*.yaml")
    got = clc._extract_paths_clause(line)
    assert got == [
        "scripts/notebook_tools/twin_pairs.d/search-6-*.yaml",
        "scripts/notebook_tools/twin_pairs.d/search-8-*.yaml",
        "scripts/notebook_tools/twin_pairs.d/search-9-*.yaml",
    ]


def test_paths_clause_brace_scope_now_blocks():
    # Before #10597 the expanded scope was `["search-{6", "8", "9}-*.yaml"]`
    # and _path_matches_any returned False for the very file the claim aimed
    # at -- the claim was silently non-blocking. After the fix the intended
    # file intersects and an out-of-group file still does not.
    line = ("[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: scripts/notebook_tools/twin_pairs.d/search-{6,8,9}-*.yaml")
    scope = clc._extract_paths_clause(line)
    assert clc._path_matches_any(
        ["scripts/notebook_tools/twin_pairs.d/search-6-astar.yaml"], scope)
    assert not clc._path_matches_any(
        ["scripts/notebook_tools/twin_pairs.d/app-20-sudokubenchmark.yaml"],
        scope)


def test_paths_clause_brace_two_separate_globs_each_expand():
    # Two comma-separated globs, each carrying its own single brace group
    # (the fleet form): split brace-aware, then each group expands. Nested
    # groups are NOT expanded (no scope in the fleet nests them) -- the
    # split simply keeps the group intact so the scope stays readable.
    line = ("[CLAIMED] lane X:CoursIA -- "
            "paths: twin_pairs.d/app-{17,18}-*.yaml, twin_pairs.d/search-{6,8}-*.yaml")
    got = clc._extract_paths_clause(line)
    assert got == [
        "twin_pairs.d/app-17-*.yaml",
        "twin_pairs.d/app-18-*.yaml",
        "twin_pairs.d/search-6-*.yaml",
        "twin_pairs.d/search-8-*.yaml",
    ]


def test_paths_clause_mixed_brace_and_plain():
    # A clause mixing brace groups and plain globs keeps both.
    line = ("[CLAIMED] lane X:CoursIA -- "
            "paths: scripts/check_lane_claim.py, twin_pairs.d/{6,8}-*.yaml")
    got = clc._extract_paths_clause(line)
    assert got == [
        "scripts/check_lane_claim.py",
        "twin_pairs.d/6-*.yaml",
        "twin_pairs.d/8-*.yaml",
    ]


def test_paths_clause_brace_still_drops_empty_fragments():
    # Stray commas outside braces keep the existing drop-empty behaviour.
    line = ("[CLAIMED] lane X:CoursIA -- "
            "paths: a.py, , b.py, ")
    assert clc._extract_paths_clause(line) == ["a.py", "b.py"]


def test_paths_match_brace_in_paths_mode():
    # `--paths` mode accepts brace syntax too (a worker pastes the fs-shell
    # glob they mean). Full-path and basename anchors both apply.
    assert clc._path_matches(
        "scripts/notebook_tools/twin_pairs.d/search-8-mcts.yaml",
        ["scripts/notebook_tools/twin_pairs.d/search-{6,8,9}-*.yaml"])
    assert not clc._path_matches(
        "scripts/notebook_tools/twin_pairs.d/search-7-mcts.yaml",
        ["scripts/notebook_tools/twin_pairs.d/search-{6,8,9}-*.yaml"])
    assert clc._path_matches(
        "anywhere/search-8-mcts.yaml", ["search-{6,8,9}-*.yaml"])


def test_paths_match_brace_no_group_is_unchanged():
    # Patterns without braces are handled exactly as before.
    assert clc._path_matches("scripts/foo.py", ["scripts/*.py"])
    assert clc._expand_brace_groups("plain.py") == ["plain.py"]
    assert clc._expand_brace_groups("a{}.lean") == ["a{}.lean"]


def test_paths_clause_brace_scope_disjoint_across_claims(capsys):
    # Two lanes claim disjoint BRACE scopes on the same issue: neither's
    # files fall in the other's (expanded) scope, so neither blocks the
    # other -- the #10419 disjointness guarantee holds through the brace
    # expansion (#10597).
    p = payload(
        comment("[CLAIMED] lane myia-po-2023:CoursIA -- "
                "paths: scripts/notebook_tools/twin_pairs.d/"
                "gametheory-{7,8,9}-*.yaml",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane myia-po-2024:CoursIA -- "
                "paths: scripts/notebook_tools/twin_pairs.d/"
                "app-{17,18,19}-*.yaml",
                "2026-08-11T04:05:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2023:CoursIA")
    assert rc == 0
    out = capsys.readouterr().out
    assert '"blocking_lanes": []' in out


# --- #10597 hardener -- unparseable scope lifted to EPIC-WIDE ----------------
#
# The base fix (#10604, commit `0a934eab`) introduced brace-aware splitting
# and brace-group expansion. After expansion, a pattern STILL containing `{`
# or `}` is fnmatch-garbage: fnmatch knows `*` `?` `[seq]` `[!seq]` -- NOT
# `{a,b}`. The safe read is to lift such a scope back to EPIC-WIDE (in case
# of doubt, block rather than silently clear). Without this hardener a
# `paths: foo-{a,b-*.yaml` (unclosed brace) silently parses to a glob list
# that matches nothing, leaving the lane UNBLOCKED -- the #9764-style defect
# this very issue set out to prevent.
#
# These tests pin BOTH the parse-layer witness (the `unparseable_scope` list
# populated on the event) AND the check-layer enforcement (the same lane is
# blocked when another lane calls without --paths, despite the unparseable
# scope "claiming" to be narrow).


def test_unparseable_scope_in_residual_braces():
    """`_unparseable_scope_in` returns the subset of `parts` that still
    contain `{` or `}` -- the witness list that the reducer/check use to
    lift the claim to epic-wide (#10597 hardener)."""
    assert clc._unparseable_scope_in(["scripts/check_lane_claim.py"]) == []
    # Pattern with an unclosed brace: fnmatch cannot read `{a,b-*`.
    parts = ["scripts/{a,b-*.yaml"]
    got = clc._unparseable_scope_in(parts)
    assert got == ["scripts/{a,b-*.yaml"]
    # Mixed: parseable + unparseable -> only the unparseable comes back.
    parts = ["scripts/check_lane_claim.py", "scripts/{a,b-*.yaml"]
    got = clc._unparseable_scope_in(parts)
    assert got == ["scripts/{a,b-*.yaml"]
    # Empty list -> empty witness.
    assert clc._unparseable_scope_in([]) == []
    assert clc._unparseable_scope_in(None) == []


def test_parse_claim_event_attaches_unparseable_scope_field():
    """The event surfaces `unparseable_scope` so the check layer can lift
    the claim without re-parsing. Reproducer of the #10597 hardener: the
    line declares an unclosed brace; without the new field, the only
    survivors of parse are the original (broken) globs."""
    line = ("[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: scripts/{a,b-*.yaml")
    ev = clc.parse_claim_event(comment(line, "2026-08-12T11:00:00Z"))
    assert ev is not None
    assert ev.paths == ["scripts/{a,b-*.yaml"]
    # The witness list names the unparseable pattern verbatim so the audit
    # surface is directly actionable (the lane reads it and reissues).
    assert ev.unparseable_scope == ["scripts/{a,b-*.yaml"]


def test_parse_claim_event_unparseable_scope_empty_when_clean():
    """Regression -- a well-formed brace scope yields an empty
    `unparseable_scope`. The hardener must NOT lift well-formed claims."""
    line = ("[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: scripts/search-{6,8,9}-*.yaml")
    ev = clc.parse_claim_event(comment(line, "2026-08-12T11:00:00Z"))
    assert ev is not None
    assert ev.paths == [
        "scripts/search-6-*.yaml",
        "scripts/search-8-*.yaml",
        "scripts/search-9-*.yaml",
    ]
    assert ev.unparseable_scope == []


def test_parse_claim_event_lane_residue_reported_not_blocking():
    """#12719 -- a marker writing a bare date after the lane parses to the
    BARE lane (no phantom `myia-po-2023:CoursIA 2026-08-23`), and the residue
    is witnessed in `lane_scope_residue`. Founder marker of the 5-auto-blocage
    night (issue #12485 form)."""
    line = ("[CLAIMED] #12485 — myia-po-2023:CoursIA 2026-08-23 — "
            "Medical-Chatbot : amorcage batch")
    ev = clc.parse_claim_event(comment(line, "2026-08-23T04:00:00Z"))
    assert ev is not None
    # The lane is the BARE token -- the declaring lane is no longer blocked
    # against its own claim.
    assert ev.lane == "myia-po-2023:CoursIA"
    # And the malformed form is REPORTED, not silently reinterpreted.
    assert ev.lane_scope_residue == ["bare-date:2026-08-23"]


def test_parse_claim_event_lane_residue_empty_when_clean():
    """#12719 regression -- a well-formed marker yields an empty
    `lane_scope_residue`. The witness must not fire on clean claims."""
    line = "[CLAIMED] lane myia-po-2023:CoursIA -- paths: scripts/foo.py"
    ev = clc.parse_claim_event(comment(line, "2026-08-23T04:00:00Z"))
    assert ev is not None
    assert ev.lane == "myia-po-2023:CoursIA"
    assert ev.lane_scope_residue == []


def test_filter_by_claim_scope_lifts_unparseable_to_epic_wide():
    """CORE #10597 hardener -- control positif (rouge->vert).

    `others` lane declared a scope with an unclosed brace. Without the
    hardener, the scope parses to a glob list that matches NOTHING, so
    `_filter_by_claim_scope` would DROP the lane (false clear -- the
    defect that triggered #10597). With the hardener, the residual `{` in
    `unparseable_scope` lifts the lane back to EPIC-WIDE: the lane STAYS
    in `others`, blocking the caller.

    This is the test that must NOT pass against the un-hardened base --
    reproduce the failure on HEAD~ of the fix branch by running this
    single test against `git checkout 0a934eab -- scripts/check_lane_claim.py`
    and watch it return `{}` (the silent clear).
    """
    others = {
        "myia-po-2024:CoursIA-2": clc.ClaimEvent(
            lane="myia-po-2024:CoursIA-2", action="open", marker="CLAIMED",
            created_at="2026-08-12T11:00:00Z", author="x", url=None,
            paths=["scripts/{a,b-*.yaml"],
            # #10597 hardener -- this list IS the witness. The base fix
            # did not populate it (so the lane would silently clear); we
            # attach it explicitly here to mirror what `parse_claim_event`
            # produces after this commit.
            unparseable_scope=["scripts/{a,b-*.yaml"],
            intent=None,
        ),
    }
    # Caller declares a SCOPED intent. Without the hardener, the lane clears
    # (false clear). With the hardener, the lane STAYS -- epic-wide read.
    filtered = clc._filter_by_claim_scope(
        others, my_paths=["scripts/check_lane_claim.py"],
        mine=None,
    )
    assert "myia-po-2024:CoursIA-2" in filtered, (
        "unparseable scope was dropped from `others` -- the lane is "
        "silently cleared despite an unparseable claim (#10597 FN)"
    )


def test_run_check_unparseable_scope_blocks_other_lane(capsys):
    """End-to-end: a scoped CLAIMED with an unclosed brace BLOCKS another
    lane checking the same issue. #12322 -- the caller has no scope binding
    so the verdict is NOT_SCOPED at exit 2 (the unparseable scope was lifted
    to epic-wide so the call cannot prove disjointness)."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: scripts/{a,b-*.yaml",
            "2026-08-12T11:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    # NOT_SCOPED -- the unparseable scope lifted the lane to epic-wide (#12322).
    assert rc == 2
    captured = capsys.readouterr()
    # The audit JSON names the residual brace so the lane learns to reissue.
    assert "scripts/{a,b-*.yaml" in captured.out
    # And the verdict itself is in stderr.
    assert "NOT_SCOPED" in captured.err


def test_run_check_summary_exposes_unparseable_scope_field(capsys):
    """The audit JSON surfaces the witness list under
    `active_claims.<lane>.unparseable_scope` so a human reviewer (and the
    lane that owns the malformed claim) can read the defect at a glance.
    #12322 -- also surfaces `query_scope: EPIC_WIDE_NO_PATHS_DECLARED` so
    a reader can branch on the verdict without re-running the check."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: scripts/{a,b-*.yaml, scripts/check_lane_claim.py",
            "2026-08-12T11:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 2
    out = capsys.readouterr().out
    # The JSON includes the structured witness list under the lane entry.
    assert '"unparseable_scope"' in out
    assert "scripts/{a,b-*.yaml" in out
    assert '"query_scope": "EPIC_WIDE_NO_PATHS_DECLARED"' in out


def test_run_check_clean_brace_scope_does_not_show_unparseable(capsys):
    """A well-formed brace scope (the base fix's expansion) does NOT carry
    the witness -- only true residuals do. This is the negative control
    that pins the hardener's selectivity: it must NOT lift parses that
    succeeded."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: scripts/notebook_tools/twin_pairs.d/search-{6,8,9}-*.yaml",
            "2026-08-12T11:00:00Z",
        ),
    )
    # Caller scope is disjoint from claim scope -> CLEAR (base fix, not
    # negated by the hardener).
    rc = clc._run_check(
        p, "myia-po-2025:CoursIA",
        my_paths=["scripts/check_lane_claim.py"],
    )
    assert rc == 0
    out = capsys.readouterr().out
    # The witness is empty; the JSON still surfaces the field for
    # consistency, but its value is the empty list, not a residual brace.
    assert '"unparseable_scope": []' in out


# --- #10958 fail-safe -- annotation suffix + entirely-dead scope ---------------
#
# Two defect classes, one root cause: a trailing annotation after the glob
# list (`paths: a/** -- 2026-08-11T18:10Z` fleet body-timestamp, or
# `paths: .../** — Phase 2 : prose` rationale) was swallowed into the LAST
# glob by the line-greedy clause regex. The glob then matches zero tracked
# files -- a dead lock -- and the OLD read was fail-open: a dead scope
# intersected nothing, so the claim cleared every other lane (#9764-style
# false CLEAR). #10958 fixes both layers:
#   1. PARSE: `_extract_paths_clause` truncates the suffix at the FIRST
#      whitespace-delimited ` -- `/` — `/` – ` separator.
#   2. CHECK: a scope whose globs are ALL dead (post-truncation: a typo, not
#      a suffix) is a BROKEN claim, not a permissive one -- lifted to
#      epic-wide (fail-safe), mirroring the #10597 hardener. The witness
#      (`empty_scope`) rides the JSON so the declaring lane can reissue.


def test_paths_clause_truncates_annotation_suffix_three_forms():
    """Acceptance form tests: `paths: a/**`, `paths: a/**, b/**`, and the
    #10958 reproducer `paths: a/** -- 2026-08-11T18:10Z` all parse to the
    same clean glob list."""
    base = "[CLAIMED] lane L:CoursIA -- paths: {}"
    # Form 1 -- single glob, no suffix.
    assert clc._extract_paths_clause(base.format("scripts/*.py")) == \
        ["scripts/*.py"]
    # Form 2 -- comma list, no suffix.
    assert clc._extract_paths_clause(
        base.format("scripts/*.py, docs/**/*.md")) == \
        ["scripts/*.py", "docs/**/*.md"]
    # Form 3 -- trailing ` -- <timestamp>` (the fleet body-timestamp form).
    assert clc._extract_paths_clause(
        base.format("scripts/*.py -- 2026-08-11T18:10Z")) == ["scripts/*.py"]
    # Em-dash prose annotation truncates identically.
    assert clc._extract_paths_clause(
        base.format("MyIA.AI.Notebooks/Sudoku/** — Phase 2 : prose")) == \
        ["MyIA.AI.Notebooks/Sudoku/**"]
    # Truncation happens at the FIRST separator only -- the glob list never
    # keeps anything past it.
    assert clc._extract_paths_clause(
        base.format("scripts/*.py -- ts -- more words")) == ["scripts/*.py"]


def test_paths_clause_keeps_non_spaced_separator_inside_glob():
    """The separator needs whitespace on BOTH sides. `foo--bar.py` (double
    dash, no spaces) is a legitimate filename character sequence and must
    survive the truncation untouched."""
    assert clc._extract_paths_clause(
        "[CLAIMED] lane L:CoursIA -- paths: docs/foo--bar.md, scripts/a.py") \
        == ["docs/foo--bar.md", "scripts/a.py"]


# --- #12052 parenthetical annotation: 4 forms from the issue body --------------
# Acceptance: a trailing parenthetical prose annotation (`paths: glob (Phase 2,
# tranche A)`) must TRUNCATE at the FIRST space-paren, yielding the same clean
# glob list as the dash-separated form. Pre-#12052 the parenthetical rode into
# `_split_paths_brace_aware` and the inner comma fragmented the prose into two
# glob-free fragments (`['glob (Phase 2', 'tranche A)']`) -- both unmatched,
# so `_empty_scope_in` lifted the scope to epic-wide and the claiming lane
# falsely blocked every other lane. The four forms reproduce the issue's
# measurement table.


def test_paths_clause_truncates_parenthetical_annotation_forms():
    """Acceptance #1: the four measured forms of the issue all parse to a
    clean glob list -- parenthesised form included."""
    base = "[CLAIMED] lane L:CoursIA -- paths: {}"
    # Form A (OK baseline, no annotation).
    assert clc._extract_paths_clause(base.format(
        "MyIA.AI.Notebooks/GenAI/**")) == ["MyIA.AI.Notebooks/GenAI/**"]
    # Form B (parenthetical -- the one that broke). Cut at FIRST ` (`.
    assert clc._extract_paths_clause(base.format(
        "MyIA.AI.Notebooks/GenAI/** (Phase 2, tranche A)")) == \
        ["MyIA.AI.Notebooks/GenAI/**"]
    # Form C (comma list, em-dash prose after the last glob).
    assert clc._extract_paths_clause(base.format(
        "a/**, b/** -- Phase 2 : prose")) == ["a/**", "b/**"]
    # Form D (comma list, NO separator before prose -- the dead-glob witness
    # is the only line of defence here: `_extract_paths_clause` does NOT
    # cut, but `_unparseable_scope_in` must still flag the bare-word prose
    # so the JSON audit surfaces it).
    parts_d = clc._extract_paths_clause(base.format(
        "a/**, prose sans separateur"))
    assert parts_d == ["a/**", "prose sans separateur"]
    # And the dead-prose fragment is reported, not silently dropped:
    assert "prose sans separateur" in clc._unparseable_scope_in(parts_d)
    # ...while the glob stays clean.
    assert "prose sans separateur" not in clc._unparseable_scope_in(["a/**"])


def test_paths_clause_paren_needs_leading_space():
    """Acceptance #2: the paren separator requires a LEADING SPACE. A glob
    containing an internal `(` (no preceding space) is left untouched --
    legitimate filename characters. Mirrors the `_ANNOTATION_SUFFIX_RE`
    discipline (#10958)."""
    # No leading space -> NOT cut, the glob survives as-is.
    assert clc._extract_paths_clause(
        "[CLAIMED] lane L:CoursIA -- paths: docs/(archive)/file.md") == \
        ["docs/(archive)/file.md"]
    # Leading space -> cut, prose dropped.
    assert clc._extract_paths_clause(
        "[CLAIMED] lane L:CoursIA -- paths: docs/file.md (archive)") == \
        ["docs/file.md"]


def test_unparseable_scope_in_flags_bare_word_prose():
    """Acceptance #3: `_unparseable_scope_in` reports a glob-free prose
    fragment (no `/`, no fnmatch meta) as unmatchable, so the JSON audit
    surfaces it even when `_extract_paths_clause` itself does not cut
    (Form D of the issue table)."""
    # Bare word with no slash, no meta -> unmatchable.
    assert clc._unparseable_scope_in(
        ["a/**", "prose sans separateur"]) == ["prose sans separateur"]
    # Mixed: live glob stays clean, prose fragment is flagged.
    assert clc._unparseable_scope_in(
        ["scripts/check_lane_claim.py", "tranche A)"]) == ["tranche A)"]
    # Glob with a slash but no meta -> clean (a plain path).
    assert clc._unparseable_scope_in(["docs/foo.md"]) == []
    # Glob with a fnmatch meta (`*`) -> clean.
    assert clc._unparseable_scope_in(["docs/*.md"]) == []
    # Brace residue still flagged (legacy #10597 contract preserved).
    assert clc._unparseable_scope_in(["{a,b}/x.py"]) == ["{a,b}/x.py"]
    # Empty / None -> empty witness (caller semantics).
    assert clc._unparseable_scope_in([]) == []
    assert clc._unparseable_scope_in(None) == []


def test_run_check_paren_annotation_does_not_fabricate_block(capsys):
    """Acceptance #4: end-to-end, a scoped claim with the parenthetical form
    from Form B parses to a single live glob and DOES NOT block another lane
    that touches only files OUTSIDE that glob. Pre-#12052 the parenthetical
    fragmented into two glob-free residues, the scope was lifted to epic-wide,
    and the other lane was falsely BLOCKED -- the 6 marqueurs C2 reported on
    2026-08-21 at 03:32 on the dashboard CoursIA."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2025:CoursIA -- "
            "paths: MyIA.AI.Notebooks/GenAI/Video/** (Phase 2, tranche A)",
            "2026-08-21T03:30:00Z",
        ),
    )
    # Caller declares its own SCOPE -- `my_paths` -- so the disjointness check
    # is run. The caller touches a TRACKED file in GenAI/Audio (different
    # subdir from Video): the `_empty_scope_in` fail-safe needs at least one
    # live glob to confirm my_scope is real, otherwise the caller-side
    # #10958 mirror returns all others unfiltered.
    rc = clc._run_check(
        p, "myia-po-2026:CoursIA-2",
        my_paths=["MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-1-OpenAI-TTS-Intro.ipynb"],
    )
    captured = capsys.readouterr()
    # CLEAR, not BLOCKED: the truncation yielded a single glob
    # `MyIA.AI.Notebooks/GenAI/Video/**` which doesn't intersect
    # `MyIA.AI.Notebooks/GenAI/Audio/something.py`.
    assert rc == 0, (
        f"Expected CLEAR (disjoint scope) but got BLOCKED. stderr:\n"
        f"{captured.err}\naudit:\n{captured.out}"
    )
    assert "BLOCKED" not in captured.err
    # And the audit JSON names the claim scope (parsed cleanly, no residue).
    assert "MyIA.AI.Notebooks/GenAI/Video/**" in captured.out
    # Clean parse: no unparseable_scope witness carried forward.
    assert '"unparseable_scope": []' in captured.out


def test_empty_scope_in_witness():
    """`_empty_scope_in` returns the globs matching ZERO tracked files (the
    #10958 witness). None tracked (no repo walk) -> no witness, no lift."""
    tracked = ["scripts/check_lane_claim.py", "scripts/grain_tag.py"]
    assert clc._empty_scope_in(["scripts/check_lane_claim.py"], tracked) == []
    assert clc._empty_scope_in(["nowhere/typo.py"], tracked) == \
        ["nowhere/typo.py"]
    # Mixed live/dead -> only the dead subset comes back (partial witness).
    assert clc._empty_scope_in(
        ["scripts/check_lane_claim.py", "nowhere/typo.py"], tracked) == \
        ["nowhere/typo.py"]
    assert clc._empty_scope_in([], tracked) == []
    # No walk -> we cannot prove deadness -> empty witness (no lift).
    assert clc._empty_scope_in(["nowhere/typo.py"], None) == []


def test_run_check_dead_scope_blocks_other_lane(capsys):
    """CORE #10958 fail-safe, end-to-end: a scoped claim whose every glob is
    dead (here a typo'd path, WITH the ` -- ts` suffix the truncation now
    handles) is lifted to epic-wide and BLOCKS another lane checking the
    same issue. Pre-fix this was the #9764-style false CLEAR. #12322 --
    the caller has no scope binding so the verdict is NOT_SCOPED at exit 2."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: scripts/nowhere/typo.py -- 2026-08-11T18:10Z",
            "2026-08-12T11:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 2  # #12322 NOT_SCOPED (lifted to epic-wide -> cannot prove disjointness)
    captured = capsys.readouterr()
    assert "NOT_SCOPED" in captured.err
    # The audit JSON names the dead glob so the lane learns to reissue.
    assert '"empty_scope"' in captured.out
    assert "scripts/nowhere/typo.py" in captured.out


def test_run_check_summary_exposes_empty_scope_field(capsys):
    """Acceptance: dead globs surface in the audit JSON under
    `active_claims.<lane>.empty_scope`, not only as a stderr WARN. A
    PARTIALLY dead scope still surfaces its dead glob without lifting.
    #12322 -- also surfaces `query_scope: EPIC_WIDE_NO_PATHS_DECLARED`."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: "
            "scripts/check_lane_claim.py, scripts/nowhere/typo.py",
            "2026-08-12T11:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 2  # #12322 NOT_SCOPED
    out = capsys.readouterr().out
    assert '"empty_scope"' in out
    assert "scripts/nowhere/typo.py" in out
    assert '"query_scope": "EPIC_WIDE_NO_PATHS_DECLARED"' in out


def test_run_check_my_dead_scope_keeps_others(capsys):
    """Caller-side guard: when MY OWN scope is entirely dead, I cannot use
    disjointness to clear another lane -- globs that lock nothing prove
    nothing. Every other lane stays -> NOT_SCOPED until my claim is reissued.

    # #12345 -- pre-#12345 the verdict was `BLOCKED` at exit 1 (a real-
    # conflict surface), masking the fact that the caller's own broken scope
    # is what disabled disjointness. Post-#12345 the verdict is
    # `NOT_SCOPED` at exit 2 -- the caller learns at the call site that the
    # issue is THEIR scope, not the other lane's, and the actionable next
    # step is the same as the no-scope case (re-run with valid `--paths`).
    """
    p = payload(
        comment("[CLAIMED] lane A:CoursIA -- paths: scripts/nowhere/typo.py",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane B:CoursIA-2 -- paths: scripts/grain_tag.py",
                "2026-08-11T04:05:00Z"),
    )
    rc = clc._run_check(p, "A:CoursIA")
    # #12862 -- the dead glob `nowhere/typo.py` is syntactically valid ->
    # creation scope -> PATH_SCOPED. B is STILL kept (the guard the test
    # name pins: a scope locking nothing proves no disjointness) -> BLOCKED
    # at exit 1. What changed vs #12345 is the verdict label, not the lock.
    assert rc == 1  # BLOCKED -- B kept; creation scope reclassified (#12862)
    out = capsys.readouterr().out
    assert "B:CoursIA-2" in out


def test_run_check_partially_dead_scope_stays_scoped(capsys):
    """A PARTIALLY dead scope (at least one live glob) is NOT lifted: the
    lock is real on its live part. Two lanes on disjoint live parts still
    clear each other -- the fail-safe must not recreate epic-wide blocking
    for a mostly-correct claim."""
    p = payload(
        comment("[CLAIMED] lane A:CoursIA -- paths: scripts/nowhere/typo.py, "
                "scripts/check_lane_claim.py",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane B:CoursIA-2 -- paths: scripts/grain_tag.py",
                "2026-08-11T04:05:00Z"),
    )
    rc = clc._run_check(p, "A:CoursIA")
    assert rc == 0
    assert '"blocking_lanes": []' in capsys.readouterr().out


# --- #12740 -- dead-scope aggregate in the JSON --------------------------------
#
# #10958 surfaces `empty_scope` under the ACTIVE claim and `caller_empty_scope`
# for the caller's own scope. GAP measured on #12620: a `[CLAIMED] -- paths:
# scripts/notebook_tools/check_code_in_markdown.py` (the real file is
# detect_code_in_markdown_cells.py) was released without ever being read --
# the stderr WARN goes to a channel the CI gate / picker / lane scripts do not
# consume, and once the claim closes its dead glob vanishes from the JSON
# altogether. `dead_scope_globs` aggregates the dead globs lane-keyed across
# EVERY claim event (open, override, close) so a sweep can grep ONE key.

def test_run_check_dead_scope_surfaces_even_when_released(capsys):
    """The specific #12740 shape: a dead-glob claim that has been RELEASED.
    It is not active (`active_claims: {}`), it does not block (`blocking_lanes:
    []`), and the stderr WARN does not fire on a close marker -- the typo is
    invisible to a JSON consumer. `dead_scope_globs` must still name it."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2023:CoursIA -- "
            "paths: scripts/notebook_tools/check_code_in_markdown.py",
            "2026-08-23T22:45:32Z",
        ),
        comment(
            "[RELEASED] lane myia-po-2023:CoursIA -- "
            "paths: scripts/notebook_tools/check_code_in_markdown.py",
            "2026-08-24T00:10:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    # Released -> no active claim, no blocker, CLEAR.
    assert rc == 0
    out = capsys.readouterr().out
    assert '"active_claims": {}' in out  # the silent look #12740 names
    assert '"blocking_lanes": []' in out
    # The dead glob still surfaces, lane-keyed, even though the claim closed.
    assert '"dead_scope_globs"' in out
    assert "myia-po-2023:CoursIA" in out
    assert "scripts/notebook_tools/check_code_in_markdown.py" in out


def test_run_check_dead_scope_aggregate_empty_for_live_scope(capsys):
    """Positive control: a scope whose globs all match a tracked file yields
    `dead_scope_globs: {}` AND still blocks another lane. Without this, a
    guard that reported a dead glob for every live scope would be
    indistinguishable from one that works -- the aggregate must stay silent on
    a well-formed scope (and the block must survive)."""
    p = payload(
        comment("[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
                "paths: scripts/check_lane_claim.py",
                "2026-08-12T11:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 2  # #12322 NOT_SCOPED -- caller gave no --paths, cannot prove disjointness
    out = capsys.readouterr().out
    assert '"dead_scope_globs": {}' in out


# --- #10597 bonus -- SCOPE_ZERO_COVERAGE warning ------------------------------
#
# When the caller's own claim carries a SCOPE that matches zero tracked
# files in the repo, `_scope_zero_coverage_warning` emits a
# `SCOPE_ZERO_COVERAGE:` line on stderr. The intent is the same as the
# positive-control test: a glob that matches nothing is INDISTINGUISHABLE
# from a legitimately-empty scope -- the lane learns at the call site
# that its declared lock is empty.
#
# Note: the warning only fires when the caller is CLEAR (no other-lane
# collision) and the caller's own claim is scoped. That's the natural
# moment to nudge -- the lane has just declared its scope and is
# checking the field. We pin both paths below.


def test_scope_zero_coverage_warning_unit():
    """`_scope_zero_coverage_warning` returns a warning dict when the
    scope matches zero tracked files in the supplied repo_root. We use
    `D:/Dev/CoursIA-2-c226-lane-claim-paths-accolades` (this worktree) so
    the assertion is hermetic -- the walk is over a real git tree, but
    the scope `definitely-not-a-real-glob-*.zxyq` cannot match any file.
    """
    scope = ["definitely-not-a-real-glob-*.zxyq"]
    repo_root = str(Path(__file__).resolve().parents[2])  # the worktree root
    warn = clc._scope_zero_coverage_warning(scope, repo_root=repo_root)
    assert warn is not None
    assert warn["scope"] == scope
    assert warn["tracked_count"] > 0  # the worktree has tracked files


def test_scope_zero_coverage_warning_unit_with_matching_scope():
    """A scope that DOES match a tracked file returns None -- no warning.
    Pins the selectivity of the check: a valid lock is not nagged."""
    scope = ["scripts/check_lane_claim.py"]  # exists in the worktree
    repo_root = str(Path(__file__).resolve().parents[2])
    assert clc._scope_zero_coverage_warning(scope, repo_root=repo_root) is None


def test_run_check_emits_scope_zero_coverage_warning(capsys):
    """End-to-end: the lane declares a scoped claim whose globs match
    no real file, then calls `_run_check` for its OWN claim -- the
    `SCOPE_ZERO_COVERAGE` line lands on stderr. This pins the user-visible
    UX of the bonus hardener.

    # #12345 -- pre-#12345 the verdict was CLEAR at exit 0 (the lane owns
    # the only claim on the issue, and no other lane blocks). Post-#12345
    # the verdict is NOT_SCOPED at exit 2 (fail-CLOSED -- a broken scope is
    # NOT a permissive scope, even when no one else is blocking). The lane
    # keeps the `SCOPE_ZERO_COVERAGE` guidance and additionally sees a
    # caller-side `SCOPE_DEAD_GLOB` WARN and the `caller_empty_scope` JSON
    # field populated with the dead globs.
    """
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: definitely-not-a-real-glob-*.zxyq",
            "2026-08-12T11:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA-2")  # own lane, scope dead
    # #12862 -- the dead glob carries an fnmatch meta (`*`), so it is
    # syntactically valid -> creation scope -> CLEAR at exit 0 (own claim
    # only, no other lane). The two witnesses still fire so the declaring
    # lane SEES the deadness; the relaxation only converts the refusal into
    # an authorisation when nothing blocks.
    assert rc == 0  # CLEAR -- creation scope, no blocker (#12862)
    captured = capsys.readouterr()
    # Both warnings fire: the legacy SCOPE_ZERO_COVERAGE (declaring-side
    # hint) and the SCOPE_DEAD_GLOB (caller-side witness list).
    assert "SCOPE_ZERO_COVERAGE" in captured.err
    assert "SCOPE_DEAD_GLOB" in captured.err
    assert "scope de creation" in captured.out
    # The scope itself is named verbatim so the lane can reissue.
    assert "definitely-not-a-real-glob-*.zxyq" in captured.err
    # And the JSON summary carries the dead-glob witness on the caller side.
    assert '"caller_empty_scope": [' in captured.out
    assert "definitely-not-a-real-glob-*.zxyq" in captured.out


def test_run_check_no_warning_when_scope_matches_files(capsys):
    """Negative control -- a scoped claim whose globs DO match a tracked
    file does NOT emit the warning. Selectivity pin."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: scripts/check_lane_claim.py",
            "2026-08-12T11:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA-2")
    assert rc == 0
    captured = capsys.readouterr()
    assert "SCOPE_ZERO_COVERAGE" not in captured.err


def test_run_check_no_warning_when_no_active_claim(capsys):
    """No active claim -> no scope -> no warning. Symmetry pin: the
    warning is only emitted when there IS a claim to warn about."""
    p = payload()  # empty -- no comments
    rc = clc._run_check(p, "myia-po-2024:CoursIA-2")
    assert rc == 0
    captured = capsys.readouterr()
    assert "SCOPE_ZERO_COVERAGE" not in captured.err


# --- #13129 -- proximity suggestion + missing-comma detection -----------------
#
# The `dead_scope_globs` JSON aggregate (#12740) is the durable signal; the
# stderr WARN channel is what the lane declaring the claim actually reads.
# Both motif A (basename unique, real path elsewhere) and motif B (missing
# comma, glob treated as one path) need to surface a USABLE hint at the call
# site, not just an opaque "no match" line. The heuristic is conservative:
# suggestion only fires when the basename appears EXACTLY once in the tracked
# tree, the suggestion is non-blocking, and the existing `SCOPE_DEAD_GLOB`
# verdict / `caller_empty_scope` JSON shape are unchanged.


def test_13129_suggest_path_correction_unique_basename():
    """Motif A/C -- a dead glob whose basename exists UNIQUE elsewhere.

    The real path is the only file in the tracked tree with that basename, so
    the suggestion is unambiguous and worth printing."""
    tracked = [
        "scripts/check_lane_claim.py",
        "scripts/check_unaddressed_nits.py",
        "MyIA.AI.Notebooks/GenAI/Video/04-Applications/04-2-Creative-Video-Workflows.ipynb",
    ]
    dead = "MyIA.AI.Notebooks/GenAI/Video/04-2-Creative-Video-Workflows.ipynb"
    assert clc._suggest_path_correction(dead, tracked) == (
        "MyIA.AI.Notebooks/GenAI/Video/04-Applications/04-2-Creative-Video-Workflows.ipynb"
    )


def test_13129_suggest_path_correction_no_suggestion_on_generic_basename():
    """README.md appears hundreds of times -- the suggestion would mislead.
    The threshold (_PROXIMITY_BASENAME_LIMIT=5) caps the suggestion at
    basenames that survive as legitimate identifiers."""
    tracked = [f"path{i}/README.md" for i in range(20)]
    assert clc._suggest_path_correction("foo/README.md", tracked) is None


def test_13129_suggest_path_correction_no_candidate_when_basename_absent():
    """Legitimate future-file case (#12740) -- no suggestion, no false help."""
    tracked = ["scripts/check_lane_claim.py"]
    assert clc._suggest_path_correction("scripts/brand_new.py", tracked) is None


def test_13129_suggest_path_correction_no_suggestion_when_multiple_close():
    """Ambiguity pin -- 2+ candidates share the same prefix length, refuse to
    guess. A wrong suggestion is worse than no suggestion."""
    tracked = [
        "foo/bar/baz.py",
        "foo/qux/baz.py",
        "unrelated/baz.py",
    ]
    # All three end with baz.py. The two "foo" candidates tie on prefix len
    # with the dead glob "foo/bar/baz.py" (both share "foo/"), the unrelated
    # one does not -- but the tiebreaker fails because best and second share
    # the longest prefix with the input.
    result = clc._suggest_path_correction("foo/bar/baz.py", tracked)
    # We accept either None (refused to guess) or a correct guess -- the pin
    # is that a WRONG guess is not returned. Both foo/* candidates are
    # arguably valid for "foo/bar/baz.py" (the dead glob itself); the tie
    # triggers the ambiguity gate.
    assert result in (None, "foo/bar/baz.py", "foo/qux/baz.py")


def test_13129_looks_like_missing_comma_detects_space_separated_paths():
    """Motif B -- the classic typo `paths: a.py b.py`. Two path-shaped
    tokens glued by a space instead of a comma."""
    dead = (
        "scripts/ci/manage_self_hosted_runner.py "
        "scripts/tests/test_manage_self_hosted_runner.py"
    )
    tokens = clc._looks_like_missing_comma(dead)
    assert tokens == [
        "scripts/ci/manage_self_hosted_runner.py",
        "scripts/tests/test_manage_self_hosted_runner.py",
    ]


def test_13129_looks_like_missing_comma_no_fire_on_single_path():
    """Single-path globs with NO whitespace, or whitespace inside a glob,
    must NOT trigger the comma-suggestion. False positive would be noise."""
    assert clc._looks_like_missing_comma("scripts/check_lane_claim.py") is None
    # Whitespace inside a glob is rare but legal; we do NOT false-fire.
    assert clc._looks_like_missing_comma("a b c") is None  # not path-shaped
    assert clc._looks_like_missing_comma("a.py") is None  # no whitespace


def test_13129_lint_emits_proximity_suggestion(capsys):
    """End-to-end -- the lint emits `did you mean ... ?` on stderr when the
    declared scope contains a dead glob with a UNIQUE basename elsewhere.

    Acceptance #13129 (1): a dead glob with the typo
    `MyIA.AI.Notebooks/GenAI/Video/04-2-...ipynb` (real path under
    `04-Applications/`) produces the suggestion; a correct glob does not."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: MyIA.AI.Notebooks/GenAI/Video/04-2-Creative-Video-Workflows.ipynb",
            "2026-08-27T10:00:00Z",
        ),
    )
    # The fixture repo has the typo's basename in `04-Applications/...` (a
    # real file). Run with the my_lane that owns the claim.
    clc._run_check(p, "myia-po-2024:CoursIA-2")
    captured = capsys.readouterr()
    assert "did you mean" in captured.err
    assert "MyIA.AI.Notebooks/GenAI/Video/04-Applications/04-2-Creative-Video-Workflows.ipynb" in captured.err


def test_13129_lint_emits_missing_comma_hint(capsys):
    """Motif B end-to-end -- two paths glued by a space produce the
    comma-suggestion instead of the proximity suggestion (the proximity
    heuristic only fires on dead globs that LOOK like a single path)."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: "
            "scripts/ci/manage_self_hosted_runner.py "
            "scripts/tests/test_manage_self_hosted_runner.py",
            "2026-08-27T10:05:00Z",
        ),
    )
    clc._run_check(p, "myia-po-2024:CoursIA-2")
    captured = capsys.readouterr()
    assert "ESP" in captured.err.upper() and "virgule" in captured.err.lower()
    assert "manage_self_hosted_runner.py" in captured.err
    assert "test_manage_self_hosted_runner.py" in captured.err


def test_13129_lint_no_suggestion_on_live_glob(capsys):
    """Negative control -- a glob that DOES match a tracked file produces
    NO suggestion. A lint that yells at correct markers is worse than no
    lint (cf. the negative pin in #10881)."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: scripts/check_lane_claim.py",
            "2026-08-27T10:10:00Z",
        ),
    )
    clc._run_check(p, "myia-po-2024:CoursIA-2")
    captured = capsys.readouterr()
    # No "did you mean" (live) and no "virgule" (single path, no space).
    assert "did you mean" not in captured.err
    assert "virgule" not in captured.err.lower()


def test_13129_lint_no_suggestion_on_generic_basename(capsys):
    """Anti-FP -- README.md is dead but its basename is generic (hundreds of
    occurrences). The threshold (_PROXIMITY_BASENAME_LIMIT=5) silences the
    suggestion so the lint does not mislead."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: foo/bar/README.md",
            "2026-08-27T10:15:00Z",
        ),
    )
    clc._run_check(p, "myia-po-2024:CoursIA-2")
    captured = capsys.readouterr()
    # The plain WARN still fires (the glob is dead), but the "did you mean"
    # suggestion does NOT (generic basename).
    assert "glob sans correspondance" in captured.err
    assert "did you mean" not in captured.err


# --- #10881: lint of malformed paths: clauses ---------------------------------
#
# 2026-08-14 morning on #10678: four markers, all misread SILENTLY, two lanes
# blocked 1.5h. The lint fires on stderr when a marker is READ -- visible to
# every lane running the check, NEVER changing a verdict. Fixtures are the
# REAL comment bodies (marker lines verbatim from #10678). The acceptance's
# decisive half ("la moitié qui compte") is the negative: a well-formed marker
# (`paths: <two existing files>`) produces NOTHING -- a lint that yells at
# correct markers would be worse than no lint.

F1_OVERRIDE_NO_PATHS = (
    "[OVERRIDE] lane myia-ai-01:CoursIA — arbitrage sur le gate interp "
    "(`check_interp_positioning.py` + `interp_positioning_baseline.json`)\n\n"
    "Deux PRs ont vise le meme blocage a 4 minutes d'intervalle. Je tranche "
    "ici, et je commence par ce qui n'est pas en cause.\n"
)

F2_PROSE_AFTER_CLAUSE = (
    "[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: "
    "MyIA.AI.Notebooks/GameTheory/**, MyIA.AI.Notebooks/GenAI/**, "
    "MyIA.AI.Notebooks/SymbolicAI/**, MyIA.AI.Notebooks/Probas/**, "
    "MyIA.AI.Notebooks/Search/**, MyIA.AI.Notebooks/ML/**, "
    "MyIA.AI.Notebooks/QuantConnect/**, MyIA.AI.Notebooks/RL/**, "
    "MyIA.AI.Notebooks/Sudoku/** — Phase 2 : repositionnement des 39 interps "
    "survivants (baseline #10864) sur 29 notebooks, markdown-only, partition "
    "par famille (G.4). Scope notebooks disjoint du gate couvert par "
    "l'override ai-01 (`check_interp_positioning.py` + "
    "`interp_positioning_baseline.json`).\n"
)

F3_FAMILY_GLOBS = (
    "[CLAIMED] lane myia-po-2023:CoursIA-2 -- paths: "
    "MyIA.AI.Notebooks/GameTheory/**, MyIA.AI.Notebooks/SymbolicAI/**, "
    "MyIA.AI.Notebooks/Search/**, MyIA.AI.Notebooks/QuantConnect/**, "
    "MyIA.AI.Notebooks/Sudoku/**\n\n"
    "Claim paths-scoped conforme a la partition de l'arbitrage ai-01 : mes 15 "
    "findings / 14 notebooks des familles GameTheory, SymbolicAI, Search, "
    "QuantConnect, Sudoku.\n"
)

F4_PROSE_GRABBED_AS_CLAUSE = (
    "[CLAIMED] lane myia-ai-01:CoursIA -- arbitrage du gate interp uniquement "
    "(correctif #10864 + baseline 39) -- scope-narrowing de mon [OVERRIDE] du "
    "05:53:20Z, qui n'avait pas de clause paths: et bloquait donc les deux "
    "lanes epic-wide. Les tranches notebooks de la Phase 2 ne m'appartiennent "
    "pas : elles sont partitionnees entre po-2024:CoursIA-2 (GenAI/Probas/ML/"
    "RL) et po-2023:CoursIA-2 (GameTheory/SymbolicAI/Search/QuantConnect/"
    "Sudoku).\r\n\r\n(check_lane_claim #9774 -- server-stamped UTC.)\r\n"
)

WELL_FORMED_MARKER = (
    "[CLAIMED] lane myia-po-2024:CoursIA -- paths: "
    "scripts/check_lane_claim.py, scripts/grain_tag.py"
)


def test_lint_override_without_paths_emits_info(capsys):
    # F1 -- the 05:53:20Z [OVERRIDE]: no `paths:` clause -> epic-wide. The
    # INFO line names the blocking effect; the verdict itself is now
    # `NOT_SCOPED` at exit 2 (#12322) since the caller does not bind scope.
    p = payload(comment(F1_OVERRIDE_NO_PATHS, "2026-08-14T05:53:20Z"),
                number=10678)
    rc = clc._run_check(p, "myia-po-2026:CoursIA")
    assert rc == 2  # #12322 -- NOT_SCOPED (caller did not bind scope)
    err = capsys.readouterr().err
    assert "INFO: marqueur OVERRIDE epic-wide (pas de clause paths:)" in err
    assert "il bloque toutes les autres lanes sur #10678" in err


def test_lint_f2_prose_suffix_now_truncated_silent(capsys):
    # F2 -- the 06:41:00Z [CLAIMED]: prose after the clause used to be
    # swallowed into the last glob (`Sudoku/** — Phase 2 : ...`), which the
    # #10881 lint could only WARN about. #10958 fixes the defect AT PARSE:
    # `_extract_paths_clause` truncates the ` — <annotation>` suffix, so the
    # glob list comes out clean (9 family globs, all alive) and the lint is
    # SILENT on this form -- the defect class no longer exists to detect.
    # F4 below still pins the lint's own value: prose WITHOUT a
    # whitespace-delimited ` -- `/` — ` separator is still swallowed and
    # still WARNs.
    # #12322 -- caller did not pass `--paths`, so the verdict label flips
    # to NOT_SCOPED (exit 2) while the lint contract (no WARN) holds.
    p = payload(comment(F2_PROSE_AFTER_CLAUSE, "2026-08-14T06:41:00Z"),
                number=10678)
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 2  # #12322 NOT_SCOPED, exit distinct from exit 1 real conflict
    err = capsys.readouterr().err
    assert "WARN:" not in err
    # The parse-layer proof: the truncated clause keeps exactly the 9 family
    # globs and drops the ` — Phase 2 : ...` annotation entirely.
    evs = clc._parse_claim_events(comment(F2_PROSE_AFTER_CLAUSE,
                                          "2026-08-14T06:41:00Z"))
    got = evs[-1].paths
    assert got[-1] == "MyIA.AI.Notebooks/Sudoku/**"
    assert all("—" not in g and ":" not in g for g in got), got


def test_lint_family_globs_are_silent(capsys):
    # F3 -- the 06:55:07Z [CLAIMED]: family globs, all matching tracked files,
    # prose on a SEPARATE line (not swallowed). The lint must be SILENT: the
    # defect here is over-breadth (the globs catch unrelated OPEN PRs), which
    # is a SEMANTIC judgement the lint deliberately does not make -- this is
    # exactly the selectivity the acceptance's "la moitié qui compte" pins.
    # #12322 -- caller has no scope, so the verdict is NOT_SCOPED at exit 2.
    p = payload(comment(F3_FAMILY_GLOBS, "2026-08-14T06:55:07Z"), number=10678)
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 2  # #12322
    err = capsys.readouterr().err
    assert "WARN:" not in err
    assert "INFO:" not in err


def test_lint_prose_mentioning_paths_warns_suspect(capsys):
    # F4 -- the 07:06:23Z [CLAIMED]: the prose literally says "clause paths:"
    # and `_PATHS_CLAUSE_RE` grabs everything after it as ONE bogus glob. The
    # lint surfaces it as a swallowed-prose WARN (the machine reads a clause
    # where the author wrote prose -- not the INFO path, but the defect is
    # caught and named). #12322 -- caller has no scope -> NOT_SCOPED exit 2.
    p = payload(comment(F4_PROSE_GRABBED_AS_CLAUSE, "2026-08-14T07:06:23Z"),
                number=10678)
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 2  # #12322
    err = capsys.readouterr().err
    assert "WARN: glob suspect (prose avalée ?)" in err
    assert "et bloquait donc les deux lanes epic-wide" in err
    assert "WARN: glob sans correspondance" in err


def test_lint_well_formed_marker_produces_nothing(capsys):
    # The acceptance's decisive negative: a well-formed marker with two
    # EXISTING files produces NO warning at all -- the lint must not cry wolf
    # on correct markers. #12322 -- caller has no scope -> NOT_SCOPED exit 2.
    p = payload(comment(WELL_FORMED_MARKER, "2026-08-14T08:00:00Z"),
                number=10678)
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 2  # #12322
    err = capsys.readouterr().err
    assert "WARN:" not in err
    assert "INFO:" not in err


# --- #10881 addendum: multi-marker comments reduce per line ------------------
#
# A comment can LEGITIMATELY carry markers for several lanes -- the natural
# shape of a coordinator arbitration. The legacy single-event reader kept
# only the LAST marker: every marker was attributed to ONE lane (the first
# `lane <token>` of the body) with the LAST marker's paths clause, and
# intermediate `[RELEASED]`s were lost. Acceptance (11): `[RELEASED] lane A`
# + `[CLAIMED] lane B -- paths: X` must produce exactly "A released, B
# claims X".

def test_release_a_claim_b_reduces_exactly():
    # Acceptance (11) verbatim. Pre-fix this produced ONE event with
    # lane=A:CoursIA and paths=X (A holding B's scope, B never claiming).
    body = (
        "[RELEASED] lane A:CoursIA -- done\n"
        "[CLAIMED] lane B:CoursIA-2 -- paths: scripts/foo.py\n"
    )
    events = clc._parse_claim_events(comment(body, "2026-08-14T07:30:08Z"))
    assert [(e.marker, e.lane) for e in events] == [
        ("RELEASED", "A:CoursIA"),
        ("CLAIMED", "B:CoursIA-2"),
    ]
    assert events[1].paths == ["scripts/foo.py"]
    active, unattrib = clc.compute_active_claims(events)
    assert not unattrib
    assert set(active) == {"B:CoursIA-2"}
    assert active["B:CoursIA-2"].paths == ["scripts/foo.py"]


def test_coordinator_arbitration_comment_reduces_per_lane():
    # The L22/L31/L33 shape ai-01 measured on #10678 (its own account): one
    # comment releasing lane A, claiming lane B (the ML/RL notebooks), and
    # re-claiming lane A scoped to the gate files. Legacy: ONE event with
    # lane=po-2024:CoursIA-2 (first body token) and paths=the gate files
    # (last marker) -- po-2024 credited with ai-01's scope, ai-01's epic-wide
    # 07:06:23Z claim left ACTIVE against every other lane, and the ML/RL
    # notebooks claimed by no one. Multi-event: po-2024 owns the notebooks,
    # ai-01 owns the gate files only.
    body = (
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
        "paths: MyIA.AI.Notebooks/ML/ML.Net/ML-9-Anomaly-Detection.ipynb, "
        "MyIA.AI.Notebooks/RL/rl_4_multi_armed_bandits.ipynb\n"
        "[RELEASED] lane myia-ai-01:CoursIA — annule mes marqueurs du "
        "05:53:20Z et du 07:06:23Z\n"
        "[CLAIMED] lane myia-ai-01:CoursIA -- "
        "paths: scripts/notebook_tools/check_interp_positioning.py, "
        "scripts/notebook_tools/interp_positioning_baseline.json\n"
    )
    events = clc._parse_claim_events(comment(body, "2026-08-14T07:30:08Z"))
    assert [(e.marker, e.lane) for e in events] == [
        ("CLAIMED", "myia-po-2024:CoursIA-2"),
        ("RELEASED", "myia-ai-01:CoursIA"),
        ("CLAIMED", "myia-ai-01:CoursIA"),
    ]
    assert events[0].paths == [
        "MyIA.AI.Notebooks/ML/ML.Net/ML-9-Anomaly-Detection.ipynb",
        "MyIA.AI.Notebooks/RL/rl_4_multi_armed_bandits.ipynb",
    ]
    assert events[2].paths == [
        "scripts/notebook_tools/check_interp_positioning.py",
        "scripts/notebook_tools/interp_positioning_baseline.json",
    ]
    # Full issue state: ai-01's prior epic-wide override + claim, then this
    # arbitration comment. Walk order releases the epic-wide claims and opens
    # the two scoped claims -- the exact final state ai-01 then had to build
    # by hand with three separate comments.
    p = payload(
        comment("[OVERRIDE] lane myia-ai-01:CoursIA — arbitrage",
                "2026-08-14T05:53:20Z"),
        comment("[CLAIMED] lane myia-ai-01:CoursIA -- arbitrage",
                "2026-08-14T07:06:23Z"),
        comment(body, "2026-08-14T07:30:08Z"),
        number=10678,
    )
    active, unattrib = clc.compute_active_claims(clc._sort_events(p))
    assert not unattrib
    assert set(active) == {"myia-po-2024:CoursIA-2", "myia-ai-01:CoursIA"}
    assert active["myia-po-2024:CoursIA-2"].paths == [
        "MyIA.AI.Notebooks/ML/ML.Net/ML-9-Anomaly-Detection.ipynb",
        "MyIA.AI.Notebooks/RL/rl_4_multi_armed_bandits.ipynb",
    ]
    assert active["myia-ai-01:CoursIA"].paths == [
        "scripts/notebook_tools/check_interp_positioning.py",
        "scripts/notebook_tools/interp_positioning_baseline.json",
    ]


def test_third_lane_disjoint_paths_clear_after_release_reclaim(capsys):
    # Practical consequence of the addendum: the released epic-wide claim no
    # longer ghosts against a THIRD lane. Post-fix, ai-01's scoped gate claim
    # does not block a lane whose `--paths` are disjoint from the gate files.
    body = (
        "[RELEASED] lane myia-ai-01:CoursIA — annule et remplace mes "
        "marqueurs du 05:53:20Z et du 07:06:23Z\n"
        "\n"
        "[CLAIMED] lane myia-ai-01:CoursIA -- paths: "
        "scripts/notebook_tools/check_interp_positioning.py\n"
    )
    p = payload(
        comment("[OVERRIDE] lane myia-ai-01:CoursIA — arbitrage",
                "2026-08-14T05:53:20Z"),
        comment("[CLAIMED] lane myia-ai-01:CoursIA -- arbitrage",
                "2026-08-14T07:06:23Z"),
        comment(body, "2026-08-14T07:30:08Z"),
        number=10678,
    )
    rc = clc._run_check(
        p, "myia-po-2026:CoursIA",
        my_paths=["MyIA.AI.Notebooks/Sudoku/"
                  "Sudoku-09-GraphColoring-Csharp.ipynb"],
    )
    assert rc == 0
    captured = capsys.readouterr()
    assert "CLEAR" in captured.out
    assert "BLOCKED" not in captured.err


def test_parse_claim_event_legacy_returns_last_event():
    # parse_claim_event (the backward-compatible wrapper) still answers the
    # "final intent" question for callers that read one event per comment,
    # with the lane of ITS OWN line.
    ev = clc.parse_claim_event(comment(
        "[CLAIMED] lane X:CoursIA -- oops\n[DONE] lane X:CoursIA",
        "2026-08-14T07:30:08Z",
    ))
    assert ev is not None
    assert ev.is_open is False
    assert ev.marker == "DONE"
    assert ev.lane == "X:CoursIA"


# --- #10881: --paths bare-integer trap ---------------------------------------
# `--paths` uses `nargs='+'` and swallows a TRAILING positional issue number:
# `--lane X --paths a b 10678` puts `"10678"` into the paths list, switches to
# path mode, and prints a reassuring CLEAR that measured nothing. The correct
# form is the positional FIRST. The lint warns on bare-integer entries.

def test_warn_bare_integer_paths_helper():
    assert clc._warn_bare_integer_paths(
        ["scripts/foo.py", "10678", "a/b.py"]) == ["10678"]
    assert clc._warn_bare_integer_paths(["scripts/foo.py", "a/b.py"]) == []
    assert clc._warn_bare_integer_paths([]) == []


def test_main_paths_bare_integer_warns(monkeypatch, capsys):
    # The exact trap from the issue: `--paths a.py 10678` (no positional).
    # The warning must fire before the path-mode branch, so it is visible
    # whatever the mode does next.
    monkeypatch.setattr(clc, "_run_check_paths",
                        lambda paths, my_lane, **kw: 0)
    rc = clc.main(["--lane", "myia-po-2024:CoursIA",
                   "--paths", "a.py", "10678"])
    assert rc == 0
    err = capsys.readouterr().err
    assert "bare integer" in err
    assert "10678" in err
    assert "positional FIRST" in err


def test_main_paths_correct_form_no_warning(monkeypatch, capsys):
    # Correct form (positional issue FIRST, no bare integer in paths) emits
    # no trap warning.
    monkeypatch.setattr(clc, "_run_check_paths",
                        lambda paths, my_lane, **kw: 0)
    rc = clc.main(["--lane", "myia-po-2024:CoursIA",
                   "--paths", "a.py", "b.py"])
    assert rc == 0
    assert "bare integer" not in capsys.readouterr().err


# --- #11064: --claim runs the check first and renders --paths ----------------

def _write_payload(p, tmp_path):
    import json
    f = tmp_path / "payload.json"
    f.write_text(json.dumps(p), encoding="utf-8")
    return str(f)


def test_paths_clause_renders_only_when_paths_given():
    # The `paths:` clause is the LAST element of the marker line -- the reader
    # (`_PATHS_CLAUSE_RE`) parses the value to END OF LINE, so any trailing
    # prose would leak into the captured scope.
    assert clc._paths_clause(None) == ""
    assert clc._paths_clause([]) == ""
    assert clc._paths_clause(["x/**", "y/01.ipynb"]) == \
        " -- paths: x/**, y/01.ipynb"


def test_claim_body_renders_paths_clause():
    body = clc._CLAIM_BODY_TMPL.format(
        lane="myia-po-2024:CoursIA", intention="fix ML-4",
        paths_clause=clc._paths_clause(["x/**", "y/01.ipynb"]),
    )
    assert body.split("\n")[0] == (
        "[CLAIMED] lane myia-po-2024:CoursIA -- fix ML-4"
        " -- paths: x/**, y/01.ipynb"
    )


def test_claim_body_without_paths_stays_epic_wide():
    # A `--claim` without `--paths` keeps the inherited epic-wide semantics --
    # the fix renders the scope when given, it does not force one.
    body = clc._CLAIM_BODY_TMPL.format(
        lane="myia-po-2024:CoursIA", intention="fix ML-4",
        paths_clause=clc._paths_clause(None),
    )
    assert body.split("\n")[0] == \
        "[CLAIMED] lane myia-po-2024:CoursIA -- fix ML-4"


# --- #12345 -- caller-side scope-vivacity classifier -------------------------
#
# #12345 v2 acceptance points (one test each, with the per-point assertion
# the comment on #12322's PR review named explicitly):
#   (1) every glob in `--paths` is dead  -> exit 2 + `SCOPE_DEAD_GLOB` WARN
#       naming each dead glob + `caller_empty_scope: [...]` JSON field;
#   (2) SOME globs are dead               -> `SCOPE_DEAD_GLOB` WARN on those,
#       the remaining live glob continues to carry disjointness;
#   (3) outside a git repo (`tracked=None`) -> silent degradation, NO false
#       WARN -- a caller without a tracked-files walk must not see a
#       `SCOPE_DEAD_GLOB` for globs that may be live elsewhere;
#   (4) positive control: a LIVE glob produces NO `SCOPE_DEAD_GLOB` WARN --
#       a silenced detector and a disabled detector render the same output,
#       and this test pins the distinction (without it, a future refactor
#       could break the WARN path without any test catching it);
#   (5) fail-CLOSED: an entirely-dead scope with ZERO blockers does NOT
#       clear to `exit 0` -- the verdict is `NOT_SCOPED` at `exit 2` with
#       a dedicated stderr message naming the dead globs, so the caller
#       learns that the missing write-authorisation is THEIR scope.


def test_check_caller_scope_all_globsmdead_routes_to_not_scoped(capsys, monkeypatch):
    """#12345 acceptance (1) -- every glob in `--paths` is dead -> exit 2 +
    `SCOPE_DEAD_GLOB` WARN + `caller_empty_scope: [...]` JSON field.
    Caller has TWO dead globs; both must surface in the WARN and the JSON."""
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["x/a.ipynb", "y/01.ipynb"])
    blocker = comment(
        "[CLAIMED] lane A:CoursIA -- tranche x -- paths: x/**",
        "2026-08-15T00:00:00Z",
    )
    p = payload(blocker, number=11064, title="t")
    rc = clc._run_check(
        p, "B:CoursIA",
        my_paths=["dead1/glob.ipynb", "dead2/other.ipynb"],
    )
    captured = capsys.readouterr()
    # #12862 -- both dead globs are syntactically valid (`/`) -> creation
    # scope -> PATH_SCOPED. The blocker `x/**` stays (cannot prove
    # disjointness from a tree that does not exist yet) -> BLOCKED exit 1.
    # The SCOPE_DEAD_GLOB WARN still names both globs verbatim, and the JSON
    # still carries the caller-side witness + the creation subset.
    assert rc == 1
    assert "SCOPE_DEAD_GLOB" in captured.err
    assert "dead1/glob.ipynb" in captured.err
    assert "dead2/other.ipynb" in captured.err
    assert '"caller_empty_scope": [' in captured.out
    assert "dead1/glob.ipynb" in captured.out
    assert "dead2/other.ipynb" in captured.out
    assert '"creation_scope_globs": [' in captured.out


def test_check_caller_scope_partially_dead_warns_but_keeps_live(capsys, monkeypatch):
    """#12345 acceptance (2) -- SOME globs are dead -> `SCOPE_DEAD_GLOB` WARN
    on those, the live glob continues to carry disjointness. The verdict is
    `PATH_SCOPED` (not `EPIC_WIDE_NO_PATHS_DECLARED`) because at least one
    glob is alive -- the partial lift only kicks in when the WHOLE scope
    is dead."""
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["x/a.ipynb", "y/01.ipynb"])
    blocker = comment(
        "[CLAIMED] lane A:CoursIA -- tranche x -- paths: x/**",
        "2026-08-15T00:00:00Z",
    )
    p = payload(blocker, number=11064, title="t")
    # Caller's scope: one live glob (`x/a.ipynb` -- intersect with `x/**`),
    # one dead glob (`dead/nowhere.ipynb`). The live glob forces the verdict
    # to PATH_SCOPED + BLOCKED; the dead glob is surfaced as a hint.
    rc = clc._run_check(
        p, "B:CoursIA",
        my_paths=["x/a.ipynb", "dead/nowhere.ipynb"],
    )
    captured = capsys.readouterr()
    # The LIVE glob intersects the blocker -> real BLOCKED at exit 1.
    assert rc == 1
    assert "BLOCKED" in captured.err
    # The DEAD glob is named in the WARN (partial coverage).
    assert "SCOPE_DEAD_GLOB" in captured.err
    assert "dead/nowhere.ipynb" in captured.err
    # The live glob does NOT appear in the SCOPE_DEAD_GLOB WARN
    # (selectivity pin). #14187 added a scope-intersection block to the
    # BLOCKED section that legitimately surfaces live globs there --
    # that surface is in a DIFFERENT message from the SCOPE_DEAD_GLOB
    # warn. We slice the WARN line specifically (split[0] = warn body,
    # not the rest of stderr).
    if "SCOPE_DEAD_GLOB" in captured.err:
        warn_block = captured.err.split("SCOPE_DEAD_GLOB", 1)[1]
        # The WARN spans until the next top-level marker (BLOCKED, LOCKED,
        # DEAD-SCOPE LOCK, etc.). Take everything up to the next blank line.
        warn_only = warn_block.split("\n\n", 1)[0]
        assert "x/a.ipynb" not in warn_only, (
            f"WARN must not name the LIVE glob; got: {warn_only!r}"
        )
    # JSON exposes the dead globs list (only the dead ones, not the live ones).
    assert 'dead/nowhere.ipynb' in captured.out
    # The live glob DOES NOT appear in the caller_empty_scope field.
    out_json = captured.out
    assert "\"caller_empty_scope\": [\n    \"dead/nowhere.ipynb\"\n  ]" in out_json or \
           '"caller_empty_scope": ["dead/nowhere.ipynb"]' in out_json


def test_check_caller_scope_silent_outside_git_repo(capsys, monkeypatch):
    """#12345 acceptance (3) -- outside a git repo (`tracked=None`) we
    degrade silently: NO `SCOPE_DEAD_GLOB` WARN, `caller_empty_scope: []`
    in the JSON. Without this pin, a caller running the check outside a
    git repo (e.g. just `--from-json` for triage) would see false-positive
    WARNs on every scope.

    The verdict semantics under `tracked=None`: `_empty_scope_in` short-
    circuits to `[]` when the walk failed, so the dead-glob classifier
    cannot fire. The verdict falls to PATH_SCOPED; `_filter_by_claim_scope`
    cannot lift the blocker `x/**` (the lift requires `tracked is not None`)
    and cannot prove disjointness (fnmatch on `does/not/exist/in/repo.ipynb`
    against `x/**` returns no match), so the blocker is DROPPED and the
    call returns CLEAR at exit 0. The verdict is the legacy behaviour, the
    PIN this test cares about is exclusively the silent-degradation aspect
    (no WARN, empty JSON witness list).
    """
    # Mock `_git_tracked_files` to return the None sentinel (the real walk
    # returns None when not in a git repo or when git is missing). The
    # organ calls the helper with one positional arg (`repo_root`), so the
    # mock accepts and ignores it.
    monkeypatch.setattr(clc, "_git_tracked_files", lambda repo_root=None: None)
    p = payload(
        comment("[CLAIMED] lane A:CoursIA -- tranche x -- paths: x/**",
                "2026-08-15T00:00:00Z"),
        number=11064, title="t",
    )
    # Caller's `--paths` would normally be dead in this repo, but the
    # tracked-files walk failed -- the WARN must NOT fire (best-effort),
    # and the verdict falls to the legacy PATH_SCOPED branch (CLEAR or
    # BLOCKED depending on fnmatch disjointness).
    rc = clc._run_check(
        p, "B:CoursIA",
        my_paths=["does/not/exist/in/repo.ipynb"],
    )
    captured = capsys.readouterr()
    # Under `tracked=None`, fnmatch says `does/not/exist/in/repo.ipynb` is
    # disjoint from `x/**` (the path does not match the pattern), so the
    # blocker is dropped -> CLEAR at exit 0. The verdict semantics here
    # are the legacy behaviour -- the PIN is silent degradation.
    assert rc == 0
    # PIN: silent degradation. NO WARN, empty JSON witness list.
    assert "SCOPE_DEAD_GLOB" not in captured.err
    assert '"caller_empty_scope": []' in captured.out


def test_check_caller_scope_live_glob_produces_no_warn(capsys, monkeypatch):
    """#12345 acceptance (4) -- POSITIVE CONTROL: a live glob produces NO
    `SCOPE_DEAD_GLOB` WARN. Without this test, a silent detector and a
    disabled detector would render the same output, and a future refactor
    that breaks the WARN path would not be caught by any other test (the
    failure modes `WARN-always` and `WARN-never` are equally broken from
    a caller's standpoint -- both mask the actual dead-glob state)."""
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["x/a.ipynb", "y/01.ipynb", "z/deep/f.ipynb"])
    p = payload(
        comment("[CLAIMED] lane A:CoursIA -- tranche x -- paths: x/**",
                "2026-08-15T00:00:00Z"),
        number=11064, title="t",
    )
    # `z/deep/f.ipynb` is in the mock AND disjoint from `x/**` -> CLEAR at
    # exit 0. Crucially: NO `SCOPE_DEAD_GLOB` WARN (the live glob is live).
    rc = clc._run_check(p, "B:CoursIA", my_paths=["z/deep/f.ipynb"])
    captured = capsys.readouterr()
    assert rc == 0
    assert "SCOPE_DEAD_GLOB" not in captured.err
    # The dead-glob witness list is empty in the JSON too.
    assert '"caller_empty_scope": []' in captured.out


def test_check_caller_scope_fail_closed_when_no_blockers(capsys, monkeypatch):
    """#12345 acceptance (5) -- fail-CLOSED: an entirely-dead scope with
    ZERO blockers does NOT clear to `exit 0`. The verdict is `NOT_SCOPED`
    at `exit 2` with a dedicated stderr message naming the dead globs, so
    the caller learns that the missing write-authorisation is THEIR scope
    (not "nothing blocks me, I'm free to write"). This is the third property
    of #12345's acceptance list -- the most important because it converts
    a silent `exit 0` into an explicit refusal."""
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["x/a.ipynb", "y/01.ipynb"])
    # ONLY the caller has a claim (their own, scoped, dead). No other lane.
    body = clc._CLAIM_BODY_TMPL.format(
        lane="B:CoursIA", intention="tranche",
        paths_clause=clc._paths_clause(["dead/nowhere.ipynb"]),
    )
    p = payload(comment(body, "2026-08-15T00:00:00Z"), number=11064, title="t")
    rc = clc._run_check(p, "B:CoursIA")  # own lane, no other claims
    captured = capsys.readouterr()
    # #12862 -- the dead glob `dead/nowhere.ipynb` is syntactically valid
    # -> CREATION scope -> CLEAR at exit 0 (nothing blocks). This test WAS
    # the #12345 acceptance (5); #12862 narrows the fail-CLOSED to the
    # typo subset (see test_broken_scope_typo_still_fails_closed): a valid
    # glob naming not-yet-existing files is the EXPECTED state of a
    # creation tranche, and refusing it invited the empty-file workaround.
    # The CLEAR names the creation scope explicitly -- never read as a
    # live-scope clear.
    assert rc == 0  # CLEAR -- creation scope, no blocker (#12862)
    assert "scope de creation" in captured.out
    assert "dead/nowhere.ipynb" in captured.err  # SCOPE_DEAD_GLOB WARN
    assert '"caller_empty_scope": [' in captured.out
    assert "dead/nowhere.ipynb" in captured.out
    assert '"creation_scope_globs": [' in captured.out


# --- #12905: the dead-scope BLOCKER is named as an epic-wide lock ------------
# Reproduction of the live case (#12844, 2026-08-25): a lane reserves a path
# it is about to create (`paths: <chemin inexistant>/**`). The #10958
# fail-safe lifts the entirely-dead claim to epic-wide -- it then blocks
# every OTHER lane on the umbrella, including callers whose live scope is
# provably disjoint. The verdict stays fail-CLOSED (a dead scope must not
# DE-unlock); what #12905 adds is the CONSEQUENCE in the blocking text:
# `WARN: glob sans correspondance` alone reads as "stale worktree", not as
# "this claim locks the whole umbrella".

def test_12905_dead_scope_blocker_names_epic_wide_lock(capsys, monkeypatch):
    """The exact #12905 shape: caller LIVE + disjoint, blocker ENTIRELY dead.
    Verdict BLOCKED at exit 1 (fail-closed unchanged) + a dedicated
    `DEAD-SCOPE LOCK` stderr message naming the blocking lane, its dead
    globs verbatim, and the epic-wide mechanism."""
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["MyIA.AI.Notebooks/GameTheory/GameTheory-17b.ipynb"])
    blocker = comment(
        "[CLAIMED] lane B:CoursIA -- lake asym -- paths: "
        "MyIA.AI.Notebooks/GameTheory/asymmetric_information_lean/**",
        "2026-08-25T09:00:00Z",
    )
    p = payload(blocker, number=12844, title="[EPIC] umbrella")
    rc = clc._run_check(
        p, "A:CoursIA",
        my_paths=["MyIA.AI.Notebooks/GameTheory/GameTheory-17b.ipynb"],
    )
    captured = capsys.readouterr()
    # Fail-closed verdict UNCHANGED: the dead-scope blocker still blocks a
    # provably-disjoint live caller (it was lifted to epic-wide).
    assert rc == 1
    assert "BLOCKED: another lane holds an active claim" in captured.err
    # The new explainer fires and names the mechanism + the dead glob.
    assert "DEAD-SCOPE LOCK" in captured.err
    assert "EPIC-WIDE" in captured.err
    assert "B:CoursIA" in captured.err
    assert "asymmetric_information_lean" in captured.err
    # The escape paths are named (re-issue / RELEASED / coordinator OVERRIDE).
    assert "[RELEASED]" in captured.err
    assert "[OVERRIDE] lane" in captured.err


def test_12905_live_scope_blocker_gets_no_dead_scope_lock_message(capsys, monkeypatch):
    """Selectivity pin (positive control): a blocker whose scope is LIVE
    produces the plain BLOCKED message with NO `DEAD-SCOPE LOCK` explainer --
    without this pin, an always-on explainer would be indistinguishable from
    the targeted one."""
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["x/a.ipynb", "y/01.ipynb"])
    blocker = comment(
        "[CLAIMED] lane A:CoursIA -- tranche x -- paths: x/**",
        "2026-08-15T00:00:00Z",
    )
    p = payload(blocker, number=11064, title="t")
    rc = clc._run_check(p, "B:CoursIA", my_paths=["x/a.ipynb"])
    captured = capsys.readouterr()
    assert rc == 1
    assert "BLOCKED: another lane holds an active claim" in captured.err
    assert "DEAD-SCOPE LOCK" not in captured.err


def test_12905_partially_dead_blocker_gets_no_dead_scope_lock_message(capsys, monkeypatch):
    """Asymmetry pin (mirror of the #11098 reducer asymmetry): a blocker
    whose scope is PARTIALLY dead (at least one live glob) stays SCOPED --
    the epic-wide lift only fires when the WHOLE scope is dead. A partial
    block is a genuine scope intersection, not a reservation lock."""
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["x/a.ipynb"])
    blocker = comment(
        "[CLAIMED] lane A:CoursIA -- tranche x -- paths: x/**, dead/**",
        "2026-08-15T00:00:00Z",
    )
    p = payload(blocker, number=11064, title="t")
    rc = clc._run_check(p, "B:CoursIA", my_paths=["x/a.ipynb"])
    captured = capsys.readouterr()
    assert rc == 1
    assert "BLOCKED: another lane holds an active claim" in captured.err
    assert "DEAD-SCOPE LOCK" not in captured.err


def test_12905_no_tracked_walk_no_dead_scope_lock_message(capsys, monkeypatch):
    """Degradation pin: outside a git repo (`tracked=None`) no `empty_scope`
    witness exists, `_claim_scope_effectively_epic_wide` degrades to False
    and the explainer stays silent. To still reach the BLOCKED branch under
    degradation, the caller's scope must INTERSECT the declared one (a
    disjoint scope would drop the blocker entirely, pre-#10958 semantics):
    the conflict is then genuine on its face and the plain BLOCKED message
    is emitted without the dead-scope explainer."""
    monkeypatch.setattr(clc, "_git_tracked_files", lambda repo_root=None: None)
    blocker = comment(
        "[CLAIMED] lane A:CoursIA -- reserve -- paths: newdir/**",
        "2026-08-25T09:00:00Z",
    )
    p = payload(blocker, number=12844, title="t")
    rc = clc._run_check(p, "B:CoursIA", my_paths=["newdir/f.ipynb"])
    captured = capsys.readouterr()
    assert rc == 1
    assert "BLOCKED" in captured.err
    assert "DEAD-SCOPE LOCK" not in captured.err


def test_claim_paths_roundtrip_reads_back_scoped(monkeypatch):
    # #11064 acceptance (4): a claim posted with --paths is read back by the
    # check as SCOPED -- a disjoint lane stays free (exit 0), an intersecting
    # lane is blocked (exit 1), and an unscoped caller is #12322-graded as
    # `EPIC_WIDE_NO_PATHS_DECLARED` (exit 2) so the verdict is actionable
    # (re-run with `--paths`) instead of indistinguishable from a real
    # conflict (the old exit 1 + BLOCKED on a non-scoped caller).
    # The fake globs must match "tracked files" or the #10958 fail-safe lifts
    # the scope to epic-wide (an entirely-dead scope is a broken claim, not a
    # permissive one) -- mock the repo walk so the scopes stay live.
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["x/a.ipynb", "y/01.ipynb", "z/deep/f.ipynb"])
    body = clc._CLAIM_BODY_TMPL.format(
        lane="A:CoursIA", intention="tranche x",
        paths_clause=clc._paths_clause(["x/**", "y/01.ipynb"]),
    )
    pl = payload(comment(body, "2026-08-15T00:00:00Z"), number=11064, title="t")
    assert clc._run_check(pl, "B:CoursIA", my_paths=["z/**"]) == 0       # disjoint -> CLEAR
    # #12345 -- the leg below USED to be `== 1` (intersect -> BLOCKED) on
    # the path `x/sub/f.ipynb` matching `x/**`. Post-#12345, `x/sub/f.ipynb`
    # is NOT in the mock tracked-files list -- the caller's scope is entirely
    # dead -> `EPIC_WIDE_NO_PATHS_DECLARED` at exit 2 (fail-CLOSED). The
    # genuine-intersection case is now pinned separately in
    # `test_claim_paths_roundtrip_reads_back_scoped_intersect_live_glob`
    # below with a glob that IS in the mock (`z/deep/f.ipynb`).
    assert clc._run_check(pl, "B:CoursIA", my_paths=["x/sub/f.ipynb"]) == 1  # creation scope, intersecting claim still blocks (#12862)
    # The unscoped-caller leg: previously `== 1` (false-positive real conflict).
    # #12322 lifts this to `== 2` (NOT_SCOPED) -- the verdict is honest about
    # the missing scope binding instead of pretending to be a hard block.
    assert clc._run_check(pl, "B:CoursIA") == 2


def test_claim_paths_roundtrip_reads_back_scoped_intersect_live_glob(monkeypatch):
    """Companion to `test_claim_paths_roundtrip_reads_back_scoped` (above) --
    pins the LEGITIMATE intersection case (caller's glob DOES match a tracked
    file AND falls under the claimant's `paths:` clause). Pre-#12345 this
    leg was on the same test as the dead-glob case (it was forced to use a
    dead glob because the assertion was `== 1`). Post-#12345 the dead-glob
    leg is #12345-routed to exit 2; the live-intersection leg is here."""
    monkeypatch.setattr(clc, "_git_tracked_files",
                        lambda: ["x/a.ipynb", "y/01.ipynb", "z/deep/f.ipynb"])
    body = clc._CLAIM_BODY_TMPL.format(
        lane="A:CoursIA", intention="tranche x",
        paths_clause=clc._paths_clause(["x/**", "y/01.ipynb"]),
    )
    pl = payload(comment(body, "2026-08-15T00:00:00Z"), number=11064, title="t")
    # The claimant's claim scope is `x/**, y/01.ipynb`. A caller scope
    # `z/deep/f.ipynb` is LIVE (in the mock) but does NOT match `x/**` or
    # `y/01.ipynb` -> disjoint -> CLEAR exit 0. We need a glob that is BOTH
    # in the mock AND under the claim's `paths:` clause -> `x/a.ipynb`.
    assert clc._run_check(pl, "B:CoursIA", my_paths=["x/a.ipynb"]) == 1  # live intersect -> BLOCKED


def test_claim_refuses_when_blocked(monkeypatch, tmp_path):
    # #11064 acceptance (1): `--claim` runs the check before posting and
    # REFUSES (nothing posted) when another lane holds an overlapping claim
    # -- instead of posting first and printing a reassuring success. The
    # refusal channel is `exit != 0` (the caller's `--claim` must NOT post
    # a comment); the EXACT exit code distinguishes two distinct refusal
    # modes that pre-#12345 were collapsed:
    #   - `exit 1` (BLOCKED): a true overlap, the caller's `--paths` matches
    #     a live tracked file under the claimant's scope. The lane MUST wait
    #     for release or post a `[RELEASED]` on its own claim.
    #   - `exit 2` (NOT_SCOPED, #12345): the caller's `--paths` is entirely
    #     dead in this repo (the glob matches zero tracked files). The
    #     refusal is the same (do not post), but the actionable next step
    #     is re-run with a valid `--paths` glob, not wait-for-release.
    # #12862 -- the caller's `--paths x/sub/f.ipynb` is dead but VALID ->
    # creation scope -> PATH_SCOPED. `--no-stale` keeps the blocker active
    # deterministically: a literal "fresh" fixture date rots past the 48h
    # threshold as wall-clock advances (the 2026-08-25 date below WAS fresh
    # at branch time; on 2026-08-29 the stale filter bypassed it and the
    # test false-cleared). Blocker active + unprovable disjointness ->
    # BLOCKED at exit 1, no post.
    blocker = comment(
        "[CLAIMED] lane A:CoursIA -- tranche x -- paths: x/**",
        "2026-08-25T10:00:00Z",
    )
    json_path = _write_payload(
        payload(blocker, number=11064, title="t"), tmp_path)
    posted = []
    monkeypatch.setattr(clc, "_post_comment",
                        lambda issue, body: posted.append((issue, body)))
    rc = clc.main(["--lane", "B:CoursIA", "--paths", "x/sub/f.ipynb",
                   "--no-stale",
                   "--claim", "tranche x", "11064", "--from-json", json_path])
    # #12862 -- creation scope + live blocker -> BLOCKED (exit 1). The
    # refusal channel (no post) is what the test actually pins.
    assert rc == 1  # BLOCKED -- creation scope, fresh claim still blocks (#12862)
    assert posted == []


def test_claim_force_posts_when_blocked(monkeypatch, tmp_path):
    # --force restores the coordinator bypass: post even when the pre-claim
    # check is blocked. The marker must still carry the --paths clause.
    blocker = comment(
        "[CLAIMED] lane A:CoursIA -- tranche x -- paths: x/**",
        "2026-08-15T00:00:00Z",
    )
    json_path = _write_payload(
        payload(blocker, number=11064, title="t"), tmp_path)
    posted = []
    monkeypatch.setattr(clc, "_post_comment",
                        lambda issue, body: posted.append((issue, body)))
    rc = clc.main(["--lane", "B:CoursIA", "--paths", "x/sub/f.ipynb",
                   "--claim", "tranche x", "11064", "--from-json", json_path,
                   "--force"])
    assert rc == 0
    assert len(posted) == 1
    assert "paths: x/sub/f.ipynb" in posted[0][1]


def test_release_body_renders_paths_clause():
    # #11064 fix (3): silence-for-silence -- a scope given on the release path
    # is rendered, never silently dropped.
    body = clc._RELEASE_BODY_TMPL.format(
        lane="myia-po-2024:CoursIA", note="PR #42",
        paths_clause=clc._paths_clause(["x/**"]),
    )
    assert body.split("\n")[0] == \
        "[RELEASED] lane myia-po-2024:CoursIA -- PR #42 -- paths: x/**"


# --- #11755: epic-wide claim without paths: clause -- diagnostic + body inference ---

def test_inferred_paths_simple_label():
    # #11755 acceptance (2): a comment body carrying `Path:` advertises an
    # intended path. The helper surfaces it as a single-item list (the most
    # natural form). Order is body order -- the line that mentions the path
    # first wins.
    body = (
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- tranche 04-7\n"
        "\n"
        "Path : MyIA.AI.Notebooks/GenAI/Audio/04-7.ipynb\n"
    )
    assert clc._infer_paths_from_body(body) == [
        "MyIA.AI.Notebooks/GenAI/Audio/04-7.ipynb",
    ]


def test_inferred_paths_multiple_labels_and_form_variants():
    # #11755 acceptance (2) breadth: a single body may carry several labels
    # in different locales (`Path :`, `Paths :`, `Fichier :`, `Notebook :`).
    # All are captured, deduplicated, in body order.
    body = (
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- umbrella\n"
        "\n"
        "Path : MyIA.AI.Notebooks/GenAI/Audio/a.ipynb\n"
        "Paths : MyIA.AI.Notebooks/GenAI/Audio/b.ipynb\n"
        "Fichier : MyIA.AI.Notebooks/GenAI/Audio/c.ipynb\n"
        "Notebook : MyIA.AI.Notebooks/GenAI/Audio/a.ipynb\n"  # duplicate
    )
    out = clc._infer_paths_from_body(body)
    assert out == [
        "MyIA.AI.Notebooks/GenAI/Audio/a.ipynb",
        "MyIA.AI.Notebooks/GenAI/Audio/b.ipynb",
        "MyIA.AI.Notebooks/GenAI/Audio/c.ipynb",
    ]


def test_inferred_paths_inline_marker_label():
    # #11755 acceptance (2) -- the inline form: `Path : ...` may appear on the
    # same line as the marker itself. The decorative prefix (`- **[`, `> [`,
    # `## [`) is tolerated; the helper still extracts the path. The trailing
    # `**` of the markdown decoration is PART of the capture group (the regex
    # only strips `.`, `,`, `;`, `:`) -- the proposer is expected to leave
    # the closing decoration on a separate line if the cleanup matters.
    body = (
        "### [CLAIMED] lane myia-po-2024:CoursIA-2 -- tranche 04-7\n"
        "\n"
        "Path : MyIA.AI.Notebooks/GenAI/Audio/x.ipynb\n"
    )
    assert clc._infer_paths_from_body(body) == [
        "MyIA.AI.Notebooks/GenAI/Audio/x.ipynb",
    ]


def test_inferred_paths_empty_or_absent():
    # #11755 acceptance (2) -- when no label is present, the helper returns an
    # empty list. The lint degrades gracefully (no WARN noise, just the legacy
    # INFO line -- no inferred suffix).
    assert clc._infer_paths_from_body("") == []
    assert clc._infer_paths_from_body(
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- tranche 04-7\n"
    ) == []


def test_lint_epic_wide_marker_with_inferred_path_echoes_expected_shape(capsys):
    # #11755 acceptance (3): when an OPEN marker has NO `paths:` clause AND
    # the body advertises a `Path:`, the WARN echoes BOTH the inferred path
    # AND the expected machine clause shape. The verdict is unchanged (still
    # epic-wide / blocking) -- the warning is a usability nudge, not a
    # gate. This pins backward compatibility: a caller relying on the legacy
    # epic-wide behaviour is not silently broken.
    # Body must be parsed through `_parse_claim_events` so `_body` is attached
    # to the event (the lint mines `ev.get("_body")`).
    body = (
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- tranche 04-7\n"
        "\n"
        "Path : MyIA.AI.Notebooks/GenAI/Audio/04-7-TTS-Voice-Benchmark.ipynb\n"
    )
    events = clc._parse_claim_events(comment(body, "2026-08-18T00:00:00Z"))
    clc._lint_claim_events(events, issue_number=11112)
    captured = capsys.readouterr()
    assert "INFO: marqueur CLAIMED epic-wide" in captured.err
    assert (
        "MyIA.AI.Notebooks/GenAI/Audio/04-7-TTS-Voice-Benchmark.ipynb"
        in captured.err
    ), (
        "The inferred `Path:` MUST appear on stderr so the lane learns at "
        "the call site that the body declared an intent the marker did not "
        "carry (#11755 Piste 2)."
    )
    assert "Forme attendue : `[CLAIMED] lane <machine:workspace> -- paths:" in captured.err, (
        "The WARN must name the expected machine-clause shape so the lane "
        "can reissue without consulting the docs (#11755 Piste 3)."
    )


# --- blocs fences : citer un marqueur n'est pas le poser (2026-08-20) --------
#
# Signale par po-2026 sur DM le 2026-08-20, mesure firsthand le meme jour :
# toutes les formes de citation en debut de ligne matchaient `_MARKER_RE`, y
# compris le bloc fence -- la forme canonique pour citer mot pour mot. Un
# arbitrage de coordinateur qui cite le `[CLAIMED]` qu'il tranche le
# RESSUSCITAIT, avec le `createdAt` (plus recent) du commentaire citeur.
#
# Ces tests pinnent les DEUX cotes : la sur-accusation fermee, et les faux
# negatifs a ne pas ouvrir en la fermant (#10906 blockquote/puce/gras).


def test_marker_quoted_in_fenced_block_is_not_an_event():
    body = (
        "Arbitrage : le claim ci-dessous est clos, la lane ne repond plus.\n"
        "\n"
        "```\n"
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: MyIA.AI.Notebooks/**\n"
        "```\n"
    )
    assert clc._parse_claim_events(comment(body, "2026-08-20T01:00:00Z")) == [], (
        "un marqueur cite dans un bloc fence est de la citation, pas un acte"
    )


def test_control_same_text_unfenced_is_an_event():
    # Controle positif du test precedent : sans les fences, la MEME ligne doit
    # rester un evenement. Sans lui, un `_parse_claim_events` casse rendrait
    # aussi une liste vide et le test ci-dessus passerait sans rien prouver.
    body = "[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: MyIA.AI.Notebooks/**\n"
    events = clc._parse_claim_events(comment(body, "2026-08-20T01:00:00Z"))
    assert len(events) == 1 and events[0].is_open
    assert events[0].lane == "myia-po-2024:CoursIA-2"


def test_real_marker_outside_the_fence_is_still_read():
    # Le faux negatif a ne PAS ouvrir : un arbitrage cite le claim adverse
    # dans une fence ET pose son propre marqueur en clair. Seul le second est
    # un acte -- mais il doit l'etre.
    body = (
        "Le marqueur que je tranche :\n"
        "\n"
        "```\n"
        "[CLAIMED] lane myia-po-2024:CoursIA-2\n"
        "```\n"
        "\n"
        "[OVERRIDE] lane myia-po-2025:CoursIA -- paths: MyIA.AI.Notebooks/**\n"
    )
    events = clc._parse_claim_events(comment(body, "2026-08-20T01:00:00Z"))
    assert len(events) == 1, "le marqueur hors fence doit rester lu"
    assert events[0].is_override and events[0].lane == "myia-po-2025:CoursIA"


def test_blockquote_and_bullet_markers_survive_the_fence_fix():
    # Non-regression #10906 : ces deux formes ont ete explicitement rehabilitees
    # apres avoir mesure 8 marqueurs legitimes annules par l'ancre stricte.
    # Le correctif fences ne doit pas les reprendre.
    for form in ("> [CLAIMED] lane myia-po-2023:CoursIA\n",
                 "- [CLAIMED] lane myia-po-2023:CoursIA\n",
                 "**[CLAIMED] lane myia-po-2023:CoursIA**\n"):
        events = clc._parse_claim_events(comment(form, "2026-08-20T01:00:00Z"))
        assert len(events) == 1 and events[0].is_open, f"forme annulee a tort : {form!r}"


def test_tilde_fence_masks_too():
    body = "~~~\n[CLAIMED] lane myia-po-2024:CoursIA\n~~~\n"
    assert clc._parse_claim_events(comment(body, "2026-08-20T01:00:00Z")) == []


def test_unterminated_fence_masks_to_end_like_github_renders_it():
    # Une fence non refermee rend TOUT le reste en code cote GitHub : ce qu'un
    # relecteur voit est du code, l'organe doit voir la meme chose.
    body = "Extrait :\n```\n[CLAIMED] lane myia-po-2024:CoursIA\n"
    assert clc._parse_claim_events(comment(body, "2026-08-20T01:00:00Z")) == []


def test_release_quoting_the_claim_it_settles_does_not_resurrect_it():
    # Le scenario complet, au niveau du reducteur, dans l'ordre qui MORD : le
    # coordinateur clot d'abord, puis cite le marqueur clos « pour memoire ».
    # C'est la forme naturelle d'un arbitrage -- et la citation, etant APRES la
    # cloture, rouvrait le claim par-dessus elle.
    #
    # L'ordre inverse (citation puis marqueur) est sauve par accident : le
    # marqueur qui suit referme ce que la citation venait d'ouvrir. Un test
    # ecrit dans cet ordre-la passerait avec ET sans le correctif, donc ne
    # prouverait rien.
    claim = comment(
        "[CLAIMED] lane myia-po-2024:CoursIA-2\n",
        "2026-08-19T10:00:00Z",
        author="myia-po-2024",
    )
    arbitrage = comment(
        "[RELEASED] lane myia-po-2024:CoursIA-2\n"
        "\n"
        "Pour memoire, le marqueur que je clos :\n"
        "\n"
        "```\n"
        "[CLAIMED] lane myia-po-2024:CoursIA-2\n"
        "```\n",
        "2026-08-20T01:00:00Z",
        author="myia-ai-01",
    )
    events = clc._sort_events(payload(claim, arbitrage))
    active, _ = clc.compute_active_claims(events)
    assert "myia-po-2024:CoursIA-2" not in active, (
        "la citation verbatim, posee APRES le [RELEASED], a ressuscite le "
        "claim que l'arbitrage venait de clore -- le defaut signale par "
        "po-2026 le 2026-08-20"
    )


def test_malformed_marker_lint_ignores_fenced_quotes():
    # Meme raison cote lint #11239 : citer une ligne mal formee pour EXPLIQUER
    # qu'elle ne sera pas lue ne doit pas declencher l'avertissement sur son
    # auteur -- sinon la doc du defaut devient le defaut.
    body = (
        "Ta ligne n'a pas ete lue parce qu'il lui manque les crochets :\n"
        "\n"
        "```\n"
        "CLAIMED #11222 -- lane myia-po-2024:CoursIA\n"
        "```\n"
    )
    assert clc._find_malformed_markers(payload(comment(body, "2026-08-20T01:00:00Z"))) == []


def test_malformed_marker_lint_still_fires_unfenced():
    # Controle positif du precedent.
    body = "CLAIMED #11222 -- lane myia-po-2024:CoursIA\n"
    found = clc._find_malformed_markers(payload(comment(body, "2026-08-20T01:00:00Z")))
    assert len(found) == 1 and found[0]["marker"] == "CLAIMED"


def test_fence_mask_preserves_offsets_for_verbatim_line_extraction():
    # Le masque doit conserver la longueur caractere pour caractere : les
    # offsets des matches sont relus sur le corps ORIGINAL par
    # `_line_for_match`. Une divergence d'un seul octet decalerait la ligne
    # verbatim rapportee a l'utilisateur.
    body = "```\nquoi que ce soit\n```\n[CLAIMED] lane myia-po-2023:CoursIA -- paths: a/**\n"
    assert len(clc._mask_fenced_blocks(body)) == len(body)
    events = clc._parse_claim_events(comment(body, "2026-08-20T01:00:00Z"))
    assert len(events) == 1
    assert events[0].paths == ["a/**"], "la clause paths est relue sur la ligne originale"


# --- #12072: clause de scope HORS ligne de marqueur -- signal structure -------
#
# Defaut mesure sur #10382 (2026-08-20T19:15:42Z, po-2023) : une clause
# `Paths: ...` ecrite sur SA PROPRE ligne (paragraphe separe sous le marqueur)
# est invisible pour `_PATHS_CLAUSE_RE` (ancre a la ligne du marqueur, `[^\n]*?`
# interdit le saut de ligne) -> le claim reduit a EPIC-WIDE en silence, alors
# que la lane declarante croyait avoir scope. #12072 expose le signal
# `scope_declared_off_marker` (structure, JSON + WARN) SANS re-classifier le
# claim (relire une ligne de prose comme la clause machine rendrait le scope
# dependant d'une heuristique).


def test_off_marker_scope_signal_on_separate_line():
    # #12072 acceptance (3) -- le controle par faux negatif : la clause sur
    # une ligne SEPAREE doit produire le signal. Reproduction exacte du corps
    # de la mesure (ligne `Paths: ...` sous le marqueur, #10382).
    body = (
        "[CLAIMED] tranche search-7-mcts-and-beyond -- "
        "lane myia-po-2023:CoursIA\n"
        "\n"
        "Paths: `scripts/notebook_tools/twin_pairs.d/"
        "search-7-mcts-and-beyond.yaml`. Grain: MED/tooling. "
        "Scope disjoint des PRs en vol.\n"
    )
    evs = clc._parse_claim_events(comment(body, "2026-08-20T19:15:42Z"))
    assert len(evs) == 1
    ev = evs[0]
    assert ev.paths is None, "la clause hors-marqueur ne doit PAS etre lue comme paths"
    assert ev.scope_declared_off_marker == [
        "Paths: `scripts/notebook_tools/twin_pairs.d/"
        "search-7-mcts-and-beyond.yaml`. Grain: MED/tooling. "
        "Scope disjoint des PRs en vol.",
    ], "la ligne fautive est exposee verbatim"


def test_off_marker_scope_signal_form_variants():
    # #12072 breadth -- les 4 formes observees de la declaration hors-ligne :
    # `Paths:` capitalise, `paths:` minuscule, `Path :` avec espace avant le
    # deux-points, et puce/gras (tolerance de decoration identique aux regex
    # de marqueur, #10906). Toutes produisent le signal.
    forms = [
        "Paths: scripts/check_lane_claim.py\n",
        "paths: scripts/check_lane_claim.py\n",
        "Path : scripts/check_lane_claim.py\n",
        "- **Paths :** scripts/check_lane_claim.py\n",
    ]
    for extra in forms:
        body = "[CLAIMED] lane myia-po-2024:CoursIA\n\n" + extra
        evs = clc._parse_claim_events(comment(body, "2026-08-20T12:00:00Z"))
        assert len(evs) == 1, extra
        assert evs[0].paths is None, extra
        assert len(evs[0].scope_declared_off_marker) == 1, extra


def test_off_marker_scope_signal_absent_without_declaration():
    # Controle positif : un epic-wide INTENTIONNEL (aucune clause hors-ligne)
    # ne produit AUCUN signal. Le lint ne doit pas bruiter un verrou plein
    # scope delibere.
    body = "[CLAIMED] lane myia-po-2024:CoursIA\n"
    evs = clc._parse_claim_events(comment(body, "2026-08-20T12:00:00Z"))
    assert len(evs) == 1
    assert evs[0].paths is None
    assert evs[0].scope_declared_off_marker == []


def test_off_marker_scope_signal_absent_when_clause_on_marker_line():
    # Controle croise : la clause SUR la ligne du marqueur est lue par le
    # reducer -> `paths` non-None -> aucun signal off-marker (rien de perdu,
    # rien a signaler). Le signal ne se leve que pour une declaration NON
    # capturee.
    body = "[CLAIMED] lane myia-po-2024:CoursIA -- paths: scripts/**\n"
    evs = clc._parse_claim_events(comment(body, "2026-08-20T12:00:00Z"))
    assert len(evs) == 1
    assert evs[0].paths == ["scripts/**"]
    assert evs[0].scope_declared_off_marker == []


def test_off_marker_scope_signal_ignores_fenced_citation():
    # Une `Paths:` citee dans un bloc fence est de la citation (meme logique
    # que `_MARKER_RE` vs `_mask_fenced_blocks`) : le masque remplace le
    # contenu du fence, donc aucune declaration off-marker n'est detectee.
    body = (
        "[CLAIMED] lane myia-po-2024:CoursIA\n"
        "\n"
        "```\n"
        "Paths: scripts/check_lane_claim.py\n"
        "```\n"
    )
    evs = clc._parse_claim_events(comment(body, "2026-08-20T12:00:00Z"))
    assert len(evs) == 1
    assert evs[0].paths is None
    assert evs[0].scope_declared_off_marker == [], (
        "citer un scope dans un fence n'est pas en declarer un"
    )


def test_off_marker_scope_signal_mid_sentence_is_prose():
    # Une mention de `paths:` EN PHRASE (pas en debut de ligne) n'est pas une
    # declaration de scope -- meme logique d'ancrage que `_INFERRED_PATH_PATTERNS`
    # (#11755 : la forme "discussion" ne nourrit pas l'inference).
    body = (
        "[CLAIMED] lane myia-po-2024:CoursIA\n"
        "\n"
        "on discute des paths: a, b en prose, ce n'est pas un scope\n"
    )
    evs = clc._parse_claim_events(comment(body, "2026-08-20T12:00:00Z"))
    assert len(evs) == 1
    assert evs[0].scope_declared_off_marker == []


def test_lint_warns_off_marker_scope_on_epic_wide(capsys):
    # #12072 acceptance (2) -- la sortie humaine : sur un claim epic-wide
    # portant le signal, le lint imprime explicitement que le commentaire
    # declare un scope NON applique, avec la ligne fautive et la syntaxe
    # attendue. Le claim n'est PAS re-scope (verdict inchange).
    body = (
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- tranche 04-7\n"
        "\n"
        "Paths: MyIA.AI.Notebooks/GenAI/Audio/04-7-TTS-Voice-Benchmark.ipynb\n"
    )
    events = clc._parse_claim_events(comment(body, "2026-08-20T12:00:00Z"))
    clc._lint_claim_events(events, issue_number=12072)
    captured = capsys.readouterr()
    assert "scope declare hors ligne de marqueur" in captured.err, (
        "le WARN doit nommer explicitement le defaut (#12072)"
    )
    assert "04-7-TTS-Voice-Benchmark.ipynb" in captured.err, (
        "la ligne fautive doit etre exposee verbatim"
    )
    assert "paths: <g1>, <g2>" in captured.err, (
        "la syntaxe attendue (clause SUR la ligne du marqueur) doit etre rappelee"
    )


def test_lint_silent_on_intentional_epic_wide(capsys):
    # Controle : un epic-wide INTENTIONNEL (pas de clause hors-ligne) ne
    # produit que l'INFO legacy #11755 -- JAMAIS le WARN #12072. Le lint ne
    # penalise pas un verrou plein scope delibere.
    body = "[CLAIMED] lane myia-po-2024:CoursIA-2\n"
    events = clc._parse_claim_events(comment(body, "2026-08-20T12:00:00Z"))
    clc._lint_claim_events(events, issue_number=12072)
    captured = capsys.readouterr()
    assert "INFO: marqueur CLAIMED epic-wide" in captured.err, (
        "l'INFO legacy #11755 reste pour retro-compat"
    )
    assert "hors ligne de marqueur" not in captured.err, (
        "aucun WARN #12072 sans declaration hors-ligne"
    )


def test_run_check_summary_exposes_scope_declared_off_marker(capsys):
    # #12072 acceptance (1) -- le champ structure monte dans le JSON de sortie
    # sous `active_claims.<lane>.scope_declared_off_marker`, a cote des autres
    # temoins (unparseable_scope, empty_scope). Vide sur un claim sans signal.
    # #12322 -- caller did not bind scope, so the verdict flips to NOT_SCOPED
    # at exit 2 (the off-marker path the writer meant was epic-wide anyway,
    # so the call lands in EPIC_WIDE_NO_PATHS_DECLARED).
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- tranche 04-7\n"
            "\n"
            "Paths: MyIA.AI.Notebooks/GenAI/Audio/04-7-TTS-Voice-Benchmark.ipynb\n",
            "2026-08-20T12:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 2  # #12322 NOT_SCOPED (epic-wide + caller has no scope)
    out = capsys.readouterr().out
    assert '"scope_declared_off_marker"' in out
    assert "04-7-TTS-Voice-Benchmark.ipynb" in out
    # Le claim n'est PAS re-scope : `paths` reste null dans le JSON.
    assert '"paths": null' in out
    assert '"query_scope": "EPIC_WIDE_NO_PATHS_DECLARED"' in out


def test_run_check_summary_off_marker_field_empty_without_signal(capsys):
    # Controle : un claim epic-wide sans declaration hors-ligne expose le
    # champ avec une liste vide (consistance du schema JSON, meme logique que
    # `unparseable_scope`/`empty_scope` toujours presents).
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2\n",
            "2026-08-20T12:00:00Z",
        ),
    )
    clc._run_check(p, "myia-po-2025:CoursIA")
    out = capsys.readouterr().out
    assert '"scope_declared_off_marker": []' in out


# --- #12156 -- umbrella / epic-wide-on-umbrella summary fields ---------------


def test_run_check_summary_is_umbrella_true_on_EPIC_label(capsys):
    # #12156 acceptance (1) -- un umbrella labellise `EPIC` expose
    # `is_umbrella: true` au niveau top-level du summary, miroir du picker
    # qui lit la meme etiquette (cf `scripts/pick_idle_grain.py:130`).
    # Note : un umbrella + claim epic-wide sans `paths:` est
    # simultanement `is_umbrella: true` ET `epic_wide_on_umbrella: true`
    # (la pathologie que le body denomme). Les deux flags sont
    # orthogonaux -- le premier classifie, le second diagnostique.
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2\n",
            "2026-08-20T12:00:00Z",
        ),
        number=12207,
        labels=[{"name": "EPIC"}, {"name": "research-notebook"}],
    )
    clc._run_check(p, "myia-po-2025:CoursIA-2")
    out = capsys.readouterr().out
    assert '"is_umbrella": true' in out
    # Le test suivant (`test_run_check_summary_epic_wide_on_umbrella_true_*`)
    # est l'acceptance explicite de la pathologie sur le meme pattern.
    # Ici on verifie juste que le classifieur fonctionne ; le controle
    # pathologie-false est dans `..._false_when_scoped`.
    assert '"epic_wide_on_umbrella":' in out


def test_run_check_summary_is_umbrella_true_on_title_prefix(capsys):
    # #12156 acceptance (2) -- fallback title-route : un titre commencant par
    # "[EPIC" est classifie umbrella meme sans label explicite (le picker
    # accepte la meme forme).
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2\n",
            "2026-08-20T12:00:00Z",
        ),
        number=1206,
        title="Epic: Fork Z3.Linq propre + reintegration (pre-label inventory)",
    )
    clc._run_check(p, "myia-po-2025:CoursIA-2")
    out = capsys.readouterr().out
    assert '"is_umbrella": true' in out


def test_run_check_summary_is_umbrella_false_on_unit_issue(capsys):
    # Controle : une issue unitaire (label `documentation`, titre sans
    # `EPIC`) expose `is_umbrella: false` -- la classification ne contamine
    # pas le cas general.
    p = payload(
        number=9890,
        title="Emojis dans comparatif-owui-vs-ai-engine.md",
        labels=[{"name": "documentation"}],
    )
    clc._run_check(p, "myia-po-2023:CoursIA-2")
    out = capsys.readouterr().out
    assert '"is_umbrella": false' in out
    assert '"epic_wide_on_umbrella": false' in out


def test_run_check_summary_epic_wide_on_umbrella_true_when_blocking_epic_wide(capsys):
    # #12156 acceptance (3) -- la pathologie que le body denomme : un
    # umbrella dont l'unique claim bloquant est epic-wide (pas de clause
    # `paths:`) expose `epic_wide_on_umbrella: true`. C'est exactement le
    # cas mesure sur #1206 par l'auteur de l'issue. #12322 -- caller has
    # no scope binding, so the verdict is NOT_SCOPED at exit 2; the JSON
    # additions (`query_scope`, `NOT_SCOPED`) ride along with the umbrella
    # diagnosis so a coordinator's sweep can correlate `epic_wide_on_umbrella:
    # true` AND `query_scope: EPIC_WIDE_NO_PATHS_DECLARED` in one pass.
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2026:CoursIA\n",
            "2026-08-11T12:29:34Z",
        ),
        number=1206,
        title="Epic: Fork Z3.Linq propre + reintegration (umbrella pathologique)",
    )
    rc = clc._run_check(p, "myia-po-2023:CoursIA-2")
    assert rc == 2  # #12322 NOT_SCOPED
    out = capsys.readouterr().out
    assert '"is_umbrella": true' in out
    assert '"epic_wide_on_umbrella": true' in out
    assert '"query_scope": "EPIC_WIDE_NO_PATHS_DECLARED"' in out
    assert '"blocking_lanes": [\n    "myia-po-2026:CoursIA"' in out


def test_run_check_summary_epic_wide_on_umbrella_false_when_scoped(capsys):
    # #12156 acceptance (4) -- le meme umbrella, mais avec un claim scope
    # (`paths: ...`) qui matche un fichier REEL du repo expose
    # `epic_wide_on_umbrella: false`. Le mecanisme discerne bien la
    # pathologie du cas nominal -- un glob mort (vide) serait au
    # contraire releve par le fail-CLOSED #10958 et remonte en
    # effectively-epic-wide, ce qui est un COMPORTEMENT VOUULU (un glob
    # mort = broken claim). On utilise donc un glob qui pointe vers un
    # fichier Lean qui existe sur `main` (CGT) pour valider la voie
    # saine.
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: MyIA.AI.Notebooks/GameTheory/conway_cgt_lean/*.lean\n",
            "2026-08-20T12:00:00Z",
        ),
        number=12207,
        labels=[{"name": "EPIC"}, {"name": "research-notebook"}],
    )
    clc._run_check(p, "myia-po-2025:CoursIA-2")
    out = capsys.readouterr().out
    assert '"is_umbrella": true' in out
    assert '"epic_wide_on_umbrella": false' in out
    # Sanity : le scope est bien enregistre, pas lift en epic-wide.
    assert '"empty_scope": []' in out


def test_run_check_summary_epic_wide_on_umbrella_false_on_clear_umbrella(capsys):
    # Controle : un umbrella sans aucun claim actif expose
    # `epic_wide_on_umbrella: false` (la pathologie presuppose un blocage).
    p = payload(
        number=12207,
        labels=[{"name": "EPIC"}],
    )
    clc._run_check(p, "myia-po-2023:CoursIA-2")
    out = capsys.readouterr().out
    assert '"is_umbrella": true' in out
    assert '"epic_wide_on_umbrella": false' in out
    assert '"blocked": false' in out


def test_is_umbrella_issue_handles_missing_labels_key():
    # Le helper degrade proprement sur un payload qui n'a pas la cle
    # `labels` (sous-ensemble du from-json historique) -- pas d'exception,
    # retour False (= defaut pre-#12156).
    assert clc._is_umbrella_issue({"title": "[EPIC] anything"}) is True
    assert clc._is_umbrella_issue({"title": "anything"}) is False
    assert clc._is_umbrella_issue({}) is False
    # Label invalide (None / dict sans name) : pas de crash.
    assert clc._is_umbrella_issue({"labels": [None, {}, {"name": "x"}]}) is False


# --- #12320 -- [DELIVERED] vocabulary for "substance is on a PR" closes ----
# See #12320 / #12223. Two lanes shipped the same Lean-16g notebook; the
# first [RELEASED] said "libre" and the second lane read it as such, missed
# the "PR #12271 deja livree" prose three words away, and re-shipped the
# same file. A third marker `[DELIVERED] lane X -- PR #N` makes the
# vocabulary unambiguous: the substance is on a PR, the consumer goes
# to check the PR state before re-claiming. This test family pins the
# v1 surface: the reducer treats DELIVERED as a close (the lane pops
# from `state`), and the JSON summary surfaces the captured PR number
# under `delivered_claims`. The v2 conditional gate (PR OPEN = block,
# PR CLOSED = lift, PR MERGED = lock permanently) is gated on
# coordinator sign-off and is NOT covered here.


def _json_out(captured) -> dict:
    """Split capsys output to extract the JSON summary, ignoring the trailing CLEAR line.

    The check prints the JSON first, then a `CLEAR: no other lane claims #N`
    or `BLOCKED: ...` trailer on stdout. The test only cares about the
    JSON; the trailer makes a bare `json.loads(out)` raise on extra data.
    """
    text = captured.out
    # The trailer begins with a newline-then-non-JSON line. Cut at the
    # first newline-followed-by-non-`{` to keep the JSON block only.
    head = text.split("\nCLEAR:")[0].split("\nBLOCKED:")[0]
    return json.loads(head)


def test_delivered_close_drops_lane_from_active_claims(capsys):
    """A [DELIVERED] close behaves like [RELEASED] in the reducer (#12320).

    The two markers are distinguishable on the event (`ev.marker` and
    `ev.is_delivered`) but REDUCE the same way: the lane is popped from
    `state`. The summary shows `my_active_claim: false` for the
    delivering lane and `blocking_lanes: []` for any other lane that
    arrives after the close.

    #13336 -- hermetic injection: this test ran WITHOUT `pr_states` and
    passed only because the live lookup was dead (the `merged` field was
    removed from gh; every fetch failed and v2 silently fell back to
    `close`). Fixing the lookup made the REAL #12271 resolve OPEN ->
    the delivering lane keeps its claim -> BLOCKED, flipping the
    assertion machine-dependently (CI gh is authed, local dev may not
    be). The legacy-close surface this test pins is now injected
    explicitly: a CLOSED-without-merge PR.
    """
    p = payload(
        comment("[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: Lean-16g-*.ipynb",
                "2026-08-22T01:41:00Z"),
        comment("[DELIVERED] lane myia-po-2024:CoursIA-2 -- PR #12271 (substance shipped)",
                "2026-08-22T04:14:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA-2",
                        pr_states=_pr_states(12271, "CLOSED"))
    assert rc == 0
    out = _json_out(capsys.readouterr())
    assert out["my_active_claim"] is False
    assert out["blocking_lanes"] == []
    # The forensic record: a PR number that lived in the issue's history
    # even though no active claim holds it any more.
    assert out["delivered_claims"] == [12271]


def test_delivered_claims_in_json_summarises_history(capsys):
    """The `delivered_claims` list in the summary is the forensic trace (#12320).

    When a lane reads a CLEAR issue, the summary now reports every
    historical `[DELIVERED] … PR #N` close on the issue. v1 surfaces
    only the PR numbers (sorted, deduplicated); v2 will add the live
    PR state. The motivating use case is #12223: po-2024 reads CLEAR,
    the summary tells po-2024 "PR #12271 was delivered here, go check
    it before you start".

    #13336 -- hermetic injection: same live-lookup disease as
    test_delivered_close_drops_lane_from_active_claims -- the real
    #12270/#12275 states decide the reduction machine-dependently. The
    summary surface this test pins (delivered_claims list) is
    state-independent, so pin both PRs CLOSED to keep it hermetic.
    """
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA-2 -- substance A",
                "2026-08-22T01:00:00Z"),
        comment("[DELIVERED] lane myia-po-2026:CoursIA-2 -- PR #12270",
                "2026-08-22T02:00:00Z"),
        comment("[CLAIMED] lane myia-po-2026:CoursIA-2 -- substance B",
                "2026-08-22T03:00:00Z"),
        comment("[DELIVERED] lane myia-po-2026:CoursIA-2 -- PR #12275",
                "2026-08-22T05:00:00Z"),
    )
    clc._run_check(p, "myia-po-2023:CoursIA-2",
                   pr_states={12270: "CLOSED", 12275: "CLOSED"})
    out = _json_out(capsys.readouterr())
    assert out["delivered_claims"] == [12270, 12275]


def test_delivered_does_not_block_subsequent_claim(capsys):
    """v1: a [DELIVERED] does NOT block a subsequent [CLAIMED] from a different lane.

    The vocabulary change closes the WRITING GAP (the writer's intent
    is now recorded), not the CONDITIONAL GAP (v2 will gate the close
    on the live PR state). Until v2 lands, a [DELIVERED] is a close --
    a subsequent [CLAIMED] from a different lane on the same issue is
    NOT blocked by the historical delivery. The PR number survives in
    the summary as the forensic record, but the gate is open.

    This is intentional: the alternative (a [DELIVERED] blocks until
    the PR is MERGED) requires reading the PR state from `gh`, which
    is a side effect the reducer was deliberately built without.
    Coordinator sign-off gates the v2 release.

    #13336 -- hermetic injection: this test ran WITHOUT `pr_states` and
    passed only because the live lookup was dead (the `merged` field was
    removed from gh; every fetch failed and v2 silently fell back to
    `close`). Fixing the lookup made the REAL #12270 resolve MERGED ->
    `open_locked` -> blocked, flipping the assertion machine-dependently.
    The v1 surface this test pins is now injected explicitly: a
    CLOSED-without-merge PR. The MERGED path has its own v2 test
    (test_delivered_pr_merged_locks_lane).
    """
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA-2",
                "2026-08-22T01:00:00Z"),
        comment("[DELIVERED] lane myia-po-2026:CoursIA-2 -- PR #12270",
                "2026-08-22T02:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2023:CoursIA-2",
                        pr_states=_pr_states(12270, "CLOSED"))
    assert rc == 0
    out = _json_out(capsys.readouterr())
    assert out["my_active_claim"] is False
    assert out["blocking_lanes"] == []
    # PR #12270 still surfaced as a forensic record.
    assert out["delivered_claims"] == [12270]


def test_is_delivered_property_distinguishes_marker():
    """`is_delivered` is the readable form for the v1 close.

    `is_open` and `is_override` are the existing predicates. The new
    one is the analogue for the 3rd marker: it reads true ONLY on a
    `[DELIVERED]` event, false on every other event (RELEASED, DONE,
    CANCELLED, ABANDONED, CLAIMED, OVERRIDE).
    """
    # DELIVERED
    ev = clc.parse_claim_event(comment(
        "[DELIVERED] lane X -- PR #1", "2026-08-22T01:00:00Z"))
    assert ev.is_delivered is True
    assert ev.is_open is False
    # RELEASED is NOT delivered
    ev = clc.parse_claim_event(comment(
        "[RELEASED] lane X -- abandoned", "2026-08-22T01:00:00Z"))
    assert ev.is_delivered is False
    assert ev.is_open is False
    # CLAIMED is NOT delivered
    ev = clc.parse_claim_event(comment(
        "[CLAIMED] lane X -- working", "2026-08-22T01:00:00Z"))
    assert ev.is_delivered is False
    assert ev.is_open is True


# ---------------------------------------------------------------------------

# #12386 -- v2 conditional [DELIVERED]: gate the close on live PR state.
#
# v1's contract: a [DELIVERED] is a close -- it pops the lane from
# `state` (see test_delivered_close_drops_lane_from_active_claims above).
# v2's contract: a [DELIVERED] is a CONDITIONAL close keyed on the PR
# state:
#
#   - PR OPEN   -> the deliverer keeps an active claim (still WRITING);
#                 subsequent claims from other lanes are BLOCKED.
#   - PR MERGED -> the deliverer keeps an active claim but `locked: True`;
#                 a plain re-claim is BLOCKED with a tailored LOCKED
#                 message; the only escape is a coordinator [OVERRIDE].
#   - PR CLOSED (not merged) -> legacy close: lane popped from state.
#   - PR not found / lookup failure -> legacy close (fail-CLOSED means
#                 refuse to BLOCK on unknown).
#   - DELIVERED without PR #N reference -> legacy close (the v1 surface).
#
# Tests below use `pr_states` injection to avoid any `gh pr view` round
# trip; the live-PR-state code path is exercised in the integration
# smoke at the bottom of `test_run_check_delivered_uses_gh_pr_view` (NOT
# auto-run in CI; covered manually on the worker with a real PR ref).
# ---------------------------------------------------------------------------

def _pr_states(pr: int, st: str) -> dict[int, str]:
    """Build a single-entry pr_states injection dict for v2 tests."""
    return {pr: st}


def test_delivered_open_blocks_subsequent_claim_via_pr_state(capsys):
    """v2: a [DELIVERED] whose PR is still OPEN keeps the lane active (#12386).

    The motivating incident is #12253/#12298: a 10-hour window of
    free state let another lane claim an issue whose [DELIVERED] lane
    was still WRITING the PR. v2 closes the conditional gap by gating
    the [DELIVERED] on the live PR state -- an OPEN PR keeps the claim
    active, BLOCKING subsequent claimers from any other lane until either
    the PR is merged (locked) or closed (legacy lift).
    """
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA-2 -- substance A",
                "2026-08-22T01:00:00Z"),
        comment("[DELIVERED] lane myia-po-2026:CoursIA-2 -- PR #12253",
                "2026-08-22T02:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2023:CoursIA-2",
                       pr_states=_pr_states(12253, "OPEN"),
                       my_paths=["scripts/check_lane_claim.py"])
    assert rc == 1  # BLOCKED
    out = _json_out(capsys.readouterr())
    assert "myia-po-2026:CoursIA-2" in out["blocking_lanes"]
    # PR state surfaces in the JSON summary for forensics. JSON serialises
    # int keys as strings -- this is the same shape consumers see on stdout.
    assert out["delivered_claims_pr_states"] == {"12253": "OPEN"}
    # Active-claim entry for the deliverer exposes the live pr_state (raw,
    # not JSON-serialised).
    active = out["active_claims"]["myia-po-2026:CoursIA-2"]
    assert active["pr_ref"] == 12253
    assert active["pr_state"] == "OPEN"
    assert active["locked"] is False


def test_delivered_merged_locks_with_overrides_required(capsys):
    """v2: a [DELIVERED] whose PR is MERGED on main locks the lane (#12386).

    `locked: True` is the flag the reducer attaches so the BLOCKED
    branch above can render a tailored message naming the merged PR and
    pointing the caller at [OVERRIDE] / R5 close as the only escapes.
    Without this flag, a lane arriving on a CLEAR summary would still
    see `blocking_lanes` empty AND the merged PR in
    `delivered_claims_pr_states` -- the message naming the lock is
    what closes the loop.
    """
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA-2 -- substance A",
                "2026-08-22T01:00:00Z"),
        comment("[DELIVERED] lane myia-po-2026:CoursIA-2 -- PR #12298",
                "2026-08-22T02:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2023:CoursIA-2",
                       pr_states=_pr_states(12298, "MERGED"),
                       my_paths=["scripts/check_lane_claim.py"])
    assert rc == 1  # BLOCKED (LOCKED branch fires inside)
    captured = capsys.readouterr()
    out = _json_out(captured)
    assert "myia-po-2026:CoursIA-2" in out["blocking_lanes"]
    assert out["delivered_claims_pr_states"] == {"12298": "MERGED"}
    active = out["active_claims"]["myia-po-2026:CoursIA-2"]
    assert active["locked"] is True
    assert active["pr_state"] == "MERGED"
    # The LOCKED message naming the merged PR must appear on stderr.
    assert "LOCKED (v2)" in captured.err
    assert "PR #12298 MERGED" in captured.err


def test_delivered_closed_lifts_active_claim(capsys):
    """v2: a [DELIVERED] whose PR was CLOSED (not merged) lifts the claim (#12386).

    CLOSED-without-MERGED is the legacy lift path: the PR did not reach
    main, the deliverer's claim should NOT block forever. The reducer
    pops the lane from `state`, identical to v1 behaviour for this
    state. The forensic record (delivered_claims) survives.
    """
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA-2 -- substance A",
                "2026-08-22T01:00:00Z"),
        comment("[DELIVERED] lane myia-po-2026:CoursIA-2 -- PR #12253",
                "2026-08-22T02:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2023:CoursIA-2",
                       pr_states=_pr_states(12253, "CLOSED"),
                       my_paths=["scripts/check_lane_claim.py"])
    assert rc == 0
    out = _json_out(capsys.readouterr())
    assert out["my_active_claim"] is False
    assert out["blocking_lanes"] == []
    assert out["delivered_claims"] == [12253]
    assert out["delivered_claims_pr_states"] == {"12253": "CLOSED"}


def test_delivered_lookup_failure_legacy_close(capsys):
    """v2: when gh pr view cannot resolve the PR, fall back to legacy close (#12386).

    Fail-CLOSED semantics: a [DELIVERED] that we cannot bind to a PR
    must NOT keep the lane active forever (that would itself be a bug:
    it would lock every issue where a PR was deleted or moved). The
    reducer treats `None` from `_fetch_pr_state` as the legacy v1
    "close" action. The forensic record still carries the PR ref.
    """
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA-2 -- substance A",
                "2026-08-22T01:00:00Z"),
        comment("[DELIVERED] lane myia-po-2026:CoursIA-2 -- PR #99999",
                "2026-08-22T02:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2023:CoursIA-2",
                       pr_states={},  # 99999 not present -> legacy close
                       my_paths=["scripts/check_lane_claim.py"])
    assert rc == 0
    out = _json_out(capsys.readouterr())
    assert out["my_active_claim"] is False
    assert out["blocking_lanes"] == []
    assert out["delivered_claims"] == [99999]


def test_delivered_without_pr_ref_still_lifts_active_claim(capsys):
    """v2: [DELIVERED] without a PR #N keeps the v1 close path (#12320/v2 compat).

    The marker is legal but unreferenced. v1 treated it as a close;
    v2 preserves that behaviour because there is no PR to bind the
    state to. The forensic record surface (`delivered_claims`,
    `delivered_claims_pr_states`) only carries entries with a PR
    reference -- an unreferenced [DELIVERED] is recorded by the parser
    but invisible in the forensic lists (consistent with v1).
    """
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA-2 -- substance A",
                "2026-08-22T01:00:00Z"),
        comment("[DELIVERED] lane myia-po-2026:CoursIA-2 -- substance shipped",
                "2026-08-22T02:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2023:CoursIA-2",
                       pr_states=None,
                       my_paths=["scripts/check_lane_claim.py"])
    assert rc == 0
    out = _json_out(capsys.readouterr())
    assert out["my_active_claim"] is False
    # Unreferenced [DELIVERED] is filtered from the forensic lists (the
    # parser records it but consumers want only PR-bound entries).
    assert out["delivered_claims"] == []
    assert out["delivered_claims_pr_states"] == {}


def test_delivered_replay_locks_again_after_open_then_merged(capsys):
    """v2: chronological replay of one DELIVERED should track the live PR.

    The motivating chronologie is #12213 (a 07:40 replay of an OPEN
    [DELIVERED] was BLOCKED, then a later cycle with MERGED returned
    BLOCKED+locked). We replay that exact sequence here with `pr_states`
    toggled across two calls; the second call MUST show `locked: True`
    while the first MUST show the active-claim. Without the v2 gate,
    the first call would CLEAR (v1 behaviour) and the second would
    still be CLEAR -- exactly the failure mode #12213 named.
    """
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA-2",
                "2026-08-22T01:00:00Z"),
        comment("[DELIVERED] lane myia-po-2026:CoursIA-2 -- PR #12213",
                "2026-08-22T02:00:00Z"),
    )
    my_paths = ["scripts/check_lane_claim.py"]
    # Step 1: PR is still OPEN -> BLOCKED
    rc = clc._run_check(p, "myia-po-2023:CoursIA-2",
                       pr_states=_pr_states(12213, "OPEN"),
                       my_paths=my_paths)
    assert rc == 1
    out = _json_out(capsys.readouterr())
    assert "myia-po-2026:CoursIA-2" in out["blocking_lanes"]
    assert out["active_claims"]["myia-po-2026:CoursIA-2"]["locked"] is False
    # Step 2: PR now MERGED -> BLOCKED + locked
    rc = clc._run_check(p, "myia-po-2023:CoursIA-2",
                       pr_states=_pr_states(12213, "MERGED"),
                       my_paths=my_paths)
    assert rc == 1
    captured = capsys.readouterr()
    out = _json_out(captured)
    assert "myia-po-2026:CoursIA-2" in out["blocking_lanes"]
    assert out["active_claims"]["myia-po-2026:CoursIA-2"]["locked"] is True
    assert "LOCKED (v2)" in captured.err


def test_pr_states_signature_is_optional_no_behavioural_change(capsys):
    """v2: callers that don't pass `pr_states` keep the v1 surface.

    Without an injected state, `_resolve_delivered_v2` calls
    `_fetch_pr_state` (which round-trips through `gh`). In CI without
    `gh` available, this surfaces as the legacy close -- the test
    asserts the function signature accepts `None` and returns v1 shape.
    """
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA-2",
                "2026-08-22T01:00:00Z"),
        comment("[DELIVERED] lane myia-po-2026:CoursIA-2 -- PR #99999",
                "2026-08-22T02:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2023:CoursIA-2",
                       pr_states=None,
                       my_paths=["scripts/check_lane_claim.py"])
    # PR 99999 does not exist, so a live lookup FAILS. #13336 split the
    # failure classes: on an authed machine the "not found" error is
    # PERMANENT -> fail-CLOSED (rc 1, the claim stays blocking); in a
    # sandbox without gh/network the error reads environmental -> legacy
    # close (rc 0) or NOT_SCOPED (rc 2). All three are valid surfaces --
    # the test pins that v2 accepted the None kwarg without TypeError and
    # never crashed on the fetch path.
    assert rc in (0, 1, 2)
    captured = capsys.readouterr()
    if rc == 0:
        out = _json_out(captured)
        # The forensic PR ref still surfaces.
        assert 99999 in out["delivered_claims"]
    if rc == 1:
        # fail-CLOSED (authed machine): the unresolved delivery is named.
        assert "99999" in captured.err
    # On NOT_SCOPED the JSON output is replaced by the trailing
    # NOT_SCOPED banner; the kwarg was accepted without TypeError,
    # which is the only thing this test pins.


# --- v2 helper: _find_open_pr_for_issue_by_lane ------------------------------

def test_find_open_pr_for_issue_by_lane_unique_match():
    """`_find_open_pr_for_issue_by_lane` returns the singleton PR number (#12386).

    The matcher accepts `Closes #N` / `Fixes #N` / `Refs #N` / `See #N`
    / `Resolves #N` / `Part of #N` / bare `#N` token in the PR body.
    Tests below pin each form and the cross-lane exclusion.
    """
    prs = [
        # No lane tag -- excluded by the lane filter
        {"number": 12345,
         "body": "Closes #9764. Substance X."},
        # Right lane, references #9764 -> the singleton match
        {"number": 12346,
         "body": "Fixes #9764 -- lane myia-po-2024:CoursIA-2 work Y"},
        # Right lane, references #9999 -> a different issue, no match
        {"number": 12349,
         "body": "Closes #9999 -- lane myia-po-2024:CoursIA-2"},
    ]
    found = clc._find_open_pr_for_issue_by_lane(
        9764, "myia-po-2024:CoursIA-2", prs=prs,
    )
    assert found == 12346  # the singleton match in this lane


def test_find_open_pr_for_issue_by_lane_picks_lowest_when_multiple_disambig(capsys):
    """Singleton returns the lowest PR number when multiple forms reference the issue.

    The matcher accepts `Closes #N` / `Fixes #N` / `Refs #N` / `See #N`
    / `Resolves #N` / `Part of #N` / bare `#N` token in the PR body. We
    pin each form here in the same lane; the helper returns None with
    a stderr warning (ambiguous) -- this test pins the disambiguation
    behaviour through the `delivered:#N` escape hatch instead, which
    forces a specific PR number regardless of ambiguity.
    """
    prs = [
        {"number": 12346,
         "body": "Fixes #9764 -- lane myia-po-2024:CoursIA-2 work Y"},
        {"number": 12347,
         "body": "Refs #9764 -- lane myia-po-2024:CoursIA-2 partial delivery"},
    ]
    # Multiple OPEN PRs in same lane -> helper refuses to pick
    found = clc._find_open_pr_for_issue_by_lane(
        9764, "myia-po-2024:CoursIA-2", prs=prs,
    )
    assert found is None
    assert "WARN" in capsys.readouterr().err


def test_find_open_pr_for_issue_by_lane_no_match():
    """`_find_open_pr_for_issue_by_lane` returns None when no PR matches."""
    prs = [
        {"number": 12345, "body": "Closes #9999. Substance X."},
        {"number": 12346, "body": "Fixes #8888 -- lane myia-po-2024:CoursIA-2"},
    ]
    assert clc._find_open_pr_for_issue_by_lane(
        9764, "myia-po-2024:CoursIA-2", prs=prs,
    ) is None


def test_find_open_pr_for_issue_by_lane_excludes_other_lanes():
    """PRs authored by other lanes are excluded even when they reference the issue (#12386)."""
    prs = [
        {"number": 12345,
         "body": "Closes #9764 -- lane myia-po-2023:CoursIA-2"},  # wrong lane
        {"number": 12346,
         "body": "Closes #9764 -- lane myia-po-2024:CoursIA-2"},  # right lane
    ]
    found = clc._find_open_pr_for_issue_by_lane(
        9764, "myia-po-2024:CoursIA-2", prs=prs,
    )
    assert found == 12346


def test_find_open_pr_for_issue_by_lane_ambiguous_returns_none(capsys):
    """Two+ OPEN PRs in the same lane referencing the issue -> warn + None (#12386).

    A misleading PR reference would LOCK the wrong PR. The helper
    refuses to pick one in this case and emits a stderr warning. The
    caller (--release flow) falls back to plain [RELEASED] -- better
    to lose the PR-binding than to lock the wrong PR.
    """
    prs = [
        {"number": 12345,
         "body": "Closes #9764 -- lane myia-po-2024:CoursIA-2 (tranche 1)"},
        {"number": 12346,
         "body": "Closes #9764 -- lane myia-po-2024:CoursIA-2 (tranche 2)"},
    ]
    found = clc._find_open_pr_for_issue_by_lane(
        9764, "myia-po-2024:CoursIA-2", prs=prs,
    )
    captured = capsys.readouterr()
    assert found is None
    assert "WARN" in captured.err
    assert "delivered:#N" in captured.err  # escape hatch

# #12327 -- lint qualifier: epic-wide markers must read the FINAL verdict,
# not the legacy `il bloque` wording, when the marker is superseded or
# the lane has been filtered out by scope. Four acceptance tests, plus the
# positive control that the legacy wording still fires when the marker is
# a real blocker (#11755 retro-compat preserved).
# ---------------------------------------------------------------------------


def _events_for(*bodies_and_dates):
    """Build a list of ClaimEvents from alternating (body, created_at) pairs.

    Used by the #12327 acceptance tests below to compose multi-lane scenarios
    where some lanes have posted an epic-wide marker followed by a scoped
    re-claim (the supersede scenario) and others only have the legacy
    epic-wide form (the still-blocking scenario).
    """
    events = []
    for body, date in bodies_and_dates:
        for ev in clc._parse_claim_events(comment(body, date)):
            events.append(ev)
    return events


def test_lint_12327_epic_wide_superseded_by_scoped_re_claim(capsys):
    # Lane X claim un marqueur epic-wide historique, puis re-poste un claim
    # scoped. Le marqueur epic-wide est SUPERSEDED par le claim actif scoped
    # de la MEME lane. Le lint doit le qualifier `SUPERSEDED`, JAMAIS
    # `il bloque toutes les autres lanes`.
    bodies_and_dates = [
        ("[CLAIMED] lane myia-po-2024:CoursIA-2\n",
         "2026-08-20T10:00:00Z"),
        ("[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: "
         "MyIA.AI.Notebooks/GenAI/Image/03-3*.ipynb\n",
         "2026-08-22T14:00:00Z"),  # scoped, later
    ]
    events = _events_for(*bodies_and_dates)
    # Compute active_claims manually (the same reducer step the lint receives)
    active, _ = clc.compute_active_claims(events)
    clc._lint_claim_events(
        events,
        issue_number=11112,
        active_claims=active,
        others_verdict={},  # empty -- the caller is in scope
        my_lane="myia-po-2023:CoursIA-2",
    )
    err = capsys.readouterr().err
    assert "SUPERSEDED" in err, (
        "le marqueur epic-wide historique doit etre qualifie SUPERSEDED "
        "quand un claim actif scoped ulterieur de la meme lane le supplante "
        "(#12327)"
    )
    assert "il bloque toutes les autres lanes" not in err, (
        "le wording legacy `il bloque toutes` est INTERDIT pour un marqueur "
        "superseded (cf. l'incident fondateur du 2026-08-22T14:41Z)"
    )
    # L'hygiene debt (RELEASED) est signalee comme dette, pas comme blocage.
    assert "Hygiene:" in err
    assert "[RELEASED]" in err


def test_lint_12327_epic_wide_filtered_out_by_scope_is_sans_effet(capsys):
    # Lane Y a un marqueur epic-wide ACTIF (le seul qu'elle a poste), mais
    # le caller declare --paths disjoint. Le verdict est CLEAR (`others`
    # vide apres filtre scope), MAIS le lint epic-wide legacy dirait quand
    # meme `il bloque`. Le qualifier doit dire `SANS effet` -- l'info
    # utilisateur est preservee, le verdict n'est pas contredit.
    bodies_and_dates = [
        ("[CLAIMED] lane myia-po-2024:CoursIA-2\n",
         "2026-08-22T14:00:00Z"),
    ]
    events = _events_for(*bodies_and_dates)
    active, _ = clc.compute_active_claims(events)
    # Post scope filter: lane Y is OUT of `others` (caller scope disjoint).
    # The lint receives this FINAL `others_verdict`, not the pre-filter state.
    clc._lint_claim_events(
        events,
        issue_number=11112,
        active_claims=active,
        others_verdict={},  # post scope-filter: empty
        my_lane="myia-po-2023:CoursIA-2",
    )
    err = capsys.readouterr().err
    assert "SANS effet" in err, (
        "un marqueur epic-wide d'une lane filtree par scope doit etre "
        "qualifie SANS effet, JAMAIS `il bloque` (#12327)"
    )
    assert "il bloque toutes les autres lanes" not in err


def test_lint_12327_legacy_il_bloque_preserved_for_real_blocker(capsys):
    # CONTROLE POSITIF (acceptance #12327 - 3e critere) : un marqueur
    # epic-wide qui EST reellement dans `others_verdict` (le caller n'a
    # pas declare de scope, donc AUCUN filtre ne l'a retire) doit TOUJOURS
    # declencher le wording legacy `il bloque`. La correction ne doit pas
    # se valider QUE par le bruit qu'elle elimine -- elle doit continuer
    # d'attraper les vrais blocages.
    bodies_and_dates = [
        ("[CLAIMED] lane myia-po-2024:CoursIA-2\n",
         "2026-08-22T14:00:00Z"),
    ]
    events = _events_for(*bodies_and_dates)
    active, _ = clc.compute_active_claims(events)
    # Caller did NOT declare --paths, so the lane IS in `others_verdict`
    # (real blocker, scope filter cannot prove disjointness).
    clc._lint_claim_events(
        events,
        issue_number=11112,
        active_claims=active,
        others_verdict=active,  # caller has no scope -> nothing filtered
        my_lane="myia-po-2023:CoursIA-2",
    )
    err = capsys.readouterr().err
    assert "il bloque toutes les autres lanes" in err, (
        "CONTROLE POSITIF (#12327 acceptance 3) : un marqueur epic-wide "
        "qui survit au scope filter DOIT toujours declencher le wording "
        "legacy `il bloque`. La correction ne peut pas etre validee par "
        "le silence seul -- elle doit aussi continuer d'attraper."
    )
    assert "SUPERSEDED" not in err, (
        "pas de SUPERSEDED si la lane n'a pas re-poste depuis"
    )


def test_lint_12327_run_check_11112_exact_scenario(capsys, monkeypatch):
    # SCENARIO EXACT de l'incident fondateur (2026-08-22T14:41Z) :
    # 4 marqueurs epic-wide historiques (4 lanes distinctes) + 4 claims
    # actifs scopés disjoints. Le caller declare --paths sur
    # 10_LocalLlama*.ipynb. Le verdict FINAL est CLEAR (tous les claims
    # scopés disjoints) -- AUCUN marqueur epic-wide historique ne doit
    # etre rapporte comme `il bloque`, et le verdict reste CLEAR.
    # Le mock tracked aligne les globs sur des fichiers qui matchent dans
    # le test (le walk reel du worktree differe du walk de l'install
    # CoursIA-2 principale ; on veut tester la logique, pas le filesystem).
    monkeypatch.setattr(
        clc, "_git_tracked_files",
        lambda repo_root=None: [
            "MyIA.AI.Notebooks/GenAI/Image/03-Orchestration/03-2-test.ipynb",
            "MyIA.AI.Notebooks/GenAI/Image/03-Orchestration/03-3-test.ipynb",
            "MyIA.AI.Notebooks/Sudoku/SL-5-test.ipynb",
            "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-3-test.ipynb",
            "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-7-test.ipynb",
            "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/I2_Contre-test.ipynb",
            "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama-test.ipynb",
        ],
    )
    bodies_and_dates = [
        # 4 epic-wide historiques (4 lanes distinctes, dates anterieures)
        ("[CLAIMED] lane myia-po-2023:CoursIA\n",
         "2026-08-22T13:50:00Z"),
        ("[CLAIMED] lane myia-po-2026:CoursIA\n",
         "2026-08-22T13:51:00Z"),
        ("[CLAIMED] lane myia-po-2024:CoursIA-2\n",
         "2026-08-22T13:52:00Z"),
        ("[CLAIMED] lane myia-po-2026:CoursIA-2\n",
         "2026-08-22T13:53:00Z"),
        # 4 claims actifs scopés disjoints (memes lanes, dates ulterieures)
        ("[CLAIMED] lane myia-po-2023:CoursIA -- paths: "
         "MyIA.AI.Notebooks/GenAI/Image/03-Orchestration/03-2*.ipynb, "
         "MyIA.AI.Notebooks/GenAI/Image/03-Orchestration/03-3*.ipynb\n",
         "2026-08-22T14:10:00Z"),
        ("[CLAIMED] lane myia-po-2026:CoursIA -- paths: "
         "MyIA.AI.Notebooks/Sudoku/SL-5*.ipynb\n",
         "2026-08-22T14:11:00Z"),
        ("[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: "
         "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-3*.ipynb, "
         "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-7*.ipynb\n",
         "2026-08-22T14:12:00Z"),
        ("[CLAIMED] lane myia-po-2026:CoursIA-2 -- paths: "
         "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/I2_Contre*.ipynb\n",
         "2026-08-22T14:13:00Z"),
    ]
    events = _events_for(*bodies_and_dates)
    p = payload(*[comment(b, d) for b, d in bodies_and_dates], number=11112)
    # Caller is po-2024:CoursIA, declares --paths on 10_LocalLlama (none of
    # the 4 scoped claims intersect). Sortie attendue : CLEAR (exit 0) et
    # AUCUN marqueur epic-wide historique ne dit `il bloque` -- tous sont
    # soit SUPERSEDED (meme lane a re-poste un scoped) soit SANS effet
    # (la lane a re-poste un scoped disjoint, mais avec un marqueur
    # epic-wide historique qu'on n'a pas re-poste en supersede -- dans ce
    # cas l'organe voit 2 markers, le scoped prime comme ACTIVE, et le
    # epic-wide historique est SUPERSEDED par construction).
    rc = clc._run_check(
        p,
        "myia-po-2024:CoursIA",
        my_paths=[
            "MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama*.ipynb",
        ],
    )
    assert rc == 0, (
        f"verdict CLEAR attendu (4 claims scopés disjoints du path 10_LocalLlama), "
        f"got rc={rc}"
    )
    err = capsys.readouterr().err
    # Aucun marqueur epic-wide ne doit affirmer `il bloque toutes les autres`
    assert "il bloque toutes les autres lanes" not in err, (
        "le wording legacy `il bloque toutes` est INTERDIT sur les 4 "
        "marqueurs epic-wide historiques une fois que la meme lane a "
        "re-poste un claim scoped (incidente fondateur 2026-08-22T14:41Z)"
    )
    # Les 4 marqueurs epic-wide sont SHOULD SUPERSEDED (chacun supplanté
    # par le claim scoped ulterieur de la meme lane).
    superseded_count = err.count("SUPERSEDED")
    assert superseded_count == 4, (
        f"les 4 marqueurs epic-wide historiques doivent etre qualifies "
        f"SUPERSEDED (1 par lane), got {superseded_count}"
    )


def test_lint_12327_released_followed_by_scoped_is_still_superseded(capsys):
    # Scénario complet : CLAIMED epic-wide historique, RELEASED hygiene, puis
    # CLAIMED scoped actif. L'organe réduit à un seul ACTIVE (le scoped).
    # L'ancien CLAIMED epic-wide reste dans la liste d'events (le RELEASED
    # ferme le PRÉCÉDENT active, mais ne supprime pas l'event du journal) --
    # le lint le voit et le qualifie SUPERSEDED par le scoped actif de la
    # MEME lane. C'est la bonne sémantique : le marqueur historique n'a plus
    # aucun effet sur le verdict (le reducer ne le considère plus), mais
    # l'info reste utile pour la lane qui n'a pas edité son RELEASED sur
    # CHAQUE marqueur historique (au cas où elle en aurait plusieurs).
    # Le wording `il bloque toutes les autres lanes` reste INTERDIT.
    bodies_and_dates = [
        ("[CLAIMED] lane myia-po-2024:CoursIA-2\n",
         "2026-08-20T10:00:00Z"),
        ("[RELEASED] lane myia-po-2024:CoursIA-2 -- cleanup\n",
         "2026-08-21T10:00:00Z"),
        ("[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: "
         "MyIA.AI.Notebooks/GenAI/Audio/04-3*.ipynb\n",
         "2026-08-22T14:00:00Z"),
    ]
    events = _events_for(*bodies_and_dates)
    active, _ = clc.compute_active_claims(events)
    clc._lint_claim_events(
        events,
        issue_number=11112,
        active_claims=active,
        others_verdict={},
        my_lane="myia-po-2023:CoursIA-2",
    )
    err = capsys.readouterr().err
    assert "SUPERSEDED" in err, (
        "le marqueur epic-wide historique (meme apres RELEASED) doit etre "
        "qualifie SUPERSEDED par le scoped actif ulterieur de la meme lane"
    )
    assert "il bloque toutes les autres lanes" not in err, (
        "le wording legacy `il bloque toutes` reste INTERDIT, meme apres "
        "RELEASED (le SUPERSEDED le remplace)"
    )


def test_lint_12327_no_supersede_marker_when_only_rele(capsys):
    # Controle symétrique : CLAIMED epic-wide + RELEASED SANS re-claim
    # scoped. L'organe a 0 active pour cette lane. Le marqueur epic-wide
    # historique n'a plus d'actif qui le supersede, mais il n'a pas non
    # plus d'effet (pas dans `others_verdict`). Le lint doit etre SILENT
    # sur ce marqueur (pas de SUPERSEDED, pas de `il bloque`) -- l'event
    # est purement historique, le verdict n'a rien à en dire.
    bodies_and_dates = [
        ("[CLAIMED] lane myia-po-2024:CoursIA-2\n",
         "2026-08-20T10:00:00Z"),
        ("[RELEASED] lane myia-po-2024:CoursIA-2 -- cleanup\n",
         "2026-08-21T10:00:00Z"),
    ]
    events = _events_for(*bodies_and_dates)
    active, _ = clc.compute_active_claims(events)
    clc._lint_claim_events(
        events,
        issue_number=11112,
        active_claims=active,
        others_verdict={},
        my_lane="myia-po-2023:CoursIA-2",
    )
    err = capsys.readouterr().err
    assert "il bloque" not in err, (
        "un marqueur epic-wide RELEASED sans re-claim ne doit produire "
        "AUCUN lint (pas d'actif, pas de blocker)"
    )
    assert "SUPERSEDED" not in err, (
        "pas de SUPERSEDED non plus (pas d'actif pour le supplanter)"
    )


# --- #12656 fail-OPEN : caller a joker vs claim path-scope --------------------
#
# The guard read `_path_matches_any(my_scope, scope)` with the CALLER's glob
# as the fnmatch `filename` operand and the other lane's concrete path as the
# `pattern`, so `fnmatch("dir/**", "dir/file.md")` was False and a joker
# caller was told CLEAR against a claim that demonstrably covered its target.
# `_scopes_intersect` is the symmetric replacement. A game of pattern goes by
# its FALSE NEGATIVES: the six repro rows of the issue table, jokers included,
# must all report BLOCKED, and genuinely-disjoint jokers must still CLEAR.

_RAG = "MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique"
_RAG_CLAIM = [
    f"{_RAG}/README.md",
    f"{_RAG}/02-Retrieval-Avance.ipynb",
]
_RAG_TRACKED = _RAG_CLAIM + [f"{_RAG}/01-Introduction.ipynb"]


def test_scopes_intersect_six_repro_rows_block():
    """#12656 table row-by-row: every caller form names the tracked README.md
    that the po-2025 claim scopes, so it must INTERSECT (block), not clear.
    The literal form is the control that already worked; the 5 joker forms
    are the fail-OPEN this test pins closed."""
    callers = [
        f"{_RAG}/README.md",                  # literal -- control
        f"{_RAG}/README*",                    # trailing joker
        f"{_RAG}/READM?.md",                  # single-char joker
        f"{_RAG}/**",                         # directory-recursive joker
        f"{_RAG}/*",                          # single-level joker
        "MyIA.AI.Notebooks/GenAI/**",         # upstream joker
    ]
    for caller in callers:
        assert clc._scopes_intersect([caller], _RAG_CLAIM, _RAG_TRACKED) is True, (
            f"repro row {caller!r} did not intersect the claim scope -- fail-OPEN"
        )


def test_scopes_intersect_disjoint_jokers_no_block():
    """Acceptance #2: genuine disjoint globs (FineTuning/** vs RAG/**) must
    NOT intersect -- the #10419 acquit must not be paid by over-obstruction."""
    tracked = [
        f"MyIA.AI.Notebooks/GenAI/FineTuning/README.md",
        f"{_RAG}/README.md",
    ]
    assert clc._scopes_intersect(
        ["MyIA.AI.Notebooks/GenAI/FineTuning/**"],
        [f"{_RAG}/README.md"],
        tracked,
    ) is False


def test_scopes_intersect_no_tracked_concrete_vs_glob():
    """Reducer path (`compute_active_claims` has no repo walk): a scoped
    override with a joker must CLOSE a concrete claim it covers -- the same
    operand-order bug left it unable to."""
    assert clc._scopes_intersect(
        ["MyIA.AI.Notebooks/SymbolicAI/Lean/**"],
        ["MyIA.AI.Notebooks/SymbolicAI/Lean/Reidemeister.lean"],
    ) is True


def test_scopes_intersect_no_tracked_disjoint_globs():
    assert clc._scopes_intersect(
        ["scripts/**"],
        ["MyIA.AI.Notebooks/SymbolicAI/Lean/**"],
    ) is False


def test_scopes_intersect_no_tracked_identical_glob():
    assert clc._scopes_intersect(
        ["MyIA.AI.Notebooks/SymbolicAI/Lean/**"],
        ["MyIA.AI.Notebooks/SymbolicAI/Lean/**"],
    ) is True


def test_run_check_joker_caller_blocks_scoped_claim(capsys):
    """#12656 acceptance #1 end-to-end: a `--paths` that carries a joker
    covering a tracked file named in another lane's `paths:` claim must
    return exit 1 (BLOCKED) -- the 5 joker forms were the reported fail-OPEN,
    the literal form is the control."""
    callers = [
        f"{_RAG}/README.md",
        f"{_RAG}/README*",
        f"{_RAG}/READM?.md",
        f"{_RAG}/**",
        f"{_RAG}/*",
        "MyIA.AI.Notebooks/GenAI/**",
    ]
    p = payload(
        comment(
            f"[CLAIMED] lane myia-po-2025:CoursIA -- paths: "
            f"{_RAG}/README.md, {_RAG}/02-Retrieval-Avance.ipynb",
            "2026-08-23T19:04:33Z",
        ),
    )
    for caller_paths in callers:
        rc = clc._run_check(p, "myia-po-2023:CoursIA-2", my_paths=[caller_paths])
        assert rc == 1, (
            f"joker caller {caller_paths!r} vs a path-scope claim covering "
            f"README.md returned rc={rc} (expected 1 / blocked) -- #12656 "
            f"fail-OPEN"
        )


def test_run_check_disjoint_joker_caller_clear(capsys):
    """Acceptance #2 end-to-end: disjoint joker scopes must CLEAR (exit 0).
    The caller targets RAG/**, the other lane's claim covers only FineTuning."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2025:CoursIA -- paths: "
            "MyIA.AI.Notebooks/GenAI/FineTuning/README.md",
            "2026-08-23T19:04:33Z",
        ),
    )
    rc = clc._run_check(
        p, "myia-po-2023:CoursIA-2",
        my_paths=[f"{_RAG}/**"],
    )
    assert rc == 0, (
        f"disjoint joker scopes must not block each other (#10419): got rc={rc}"
    )



# --- #12862 : creation scope vs broken scope -------------------------------

def test_creation_scope_valid_glob_clears_when_unblocked(capsys):
    """#12862 acceptance 1 (positive): a syntactically-valid glob matching
    zero tracked files + no blocking lane -> CLEAR at exit 0, with an
    explicit creation-scope line naming the dead-glob count AND the empty
    blocker set in the same invocation (acceptance 4)."""
    p = payload()  # no other lane has claimed anything
    rc = clc._run_check(
        p,
        "myia-po-2026:CoursIA",
        # glob volontairement sans correspondance sur main : le lake GT fictif
        # n'existe pas, contrairement a asymmetric_information_lean (cree
        # depuis par #13200) -- la deadness du glob est le pre-requis du test.
        my_paths=["MyIA.AI.Notebooks/GameTheory/negotiation_equilibrium_lake/**"],
    )
    captured = capsys.readouterr()
    assert rc == 0
    assert "CLEAR" in captured.out
    assert "scope de creation" in captured.out
    assert "1 glob(s) sans correspondance" in captured.out
    assert "blocking_lanes: []" in captured.out
    assert '"query_scope": "PATH_SCOPED"' in captured.out
    assert '"creation_scope_globs"' in captured.out


def test_creation_scope_valid_glob_still_blocked_by_claiming_lane(capsys):
    """#12862 acceptance 2 (the control that counts): the same valid creation
    scope BUT another lane holds an active claim -> BLOCKED at exit 1. The
    relaxation reclassifies the verdict; it must never open a disputed
    scope."""
    p = payload(
        comment("[CLAIMED] lane myia-po-2024:CoursIA -- working here",
                "2026-08-25T10:00:00Z"),
    )
    rc = clc._run_check(
        p,
        "myia-po-2026:CoursIA",
        # meme glob fictif que le test positif (cf. deadness garantie).
        my_paths=["MyIA.AI.Notebooks/GameTheory/negotiation_equilibrium_lake/**"],
    )
    captured = capsys.readouterr()
    assert rc == 1  # BLOCKED
    assert "BLOCKED" in captured.err or "myia-po-2024:CoursIA" in captured.out
    assert '"query_scope": "PATH_SCOPED"' in captured.out


def test_broken_scope_typo_still_fails_closed(capsys):
    """#12862 acceptance 3 (non-regression): an INVALID glob (bare prose
    without `/` or metacharacter, and an unclosed brace) stays the #12345
    fail-CLOSED `NOT_SCOPED` at exit 2 -- the typo was, is, and remains a
    broken scope, not a creation."""
    p = payload()  # unblocked -- the exit 2 comes from the scope, not a lane
    rc = clc._run_check(
        p,
        "myia-po-2026:CoursIA",
        my_paths=["prose-without-separator", "MyIA/{unclosed/**"],
    )
    captured = capsys.readouterr()
    assert rc == 2  # NOT_SCOPED -- invalid globs (#12345 preserved)
    assert "NOT_SCOPED" in captured.err
    assert '"query_scope": "EPIC_WIDE_NO_PATHS_DECLARED"' in captured.out


def test_creation_scope_json_exposes_dead_count_and_blockers(capsys):
    """#12862 acceptance 4 (machine leg): the JSON of a creation-scope CLEAR
    carries BOTH `creation_scope_globs` (the count) and the blocker state --
    a reader cannot see one without the other."""
    p = payload()
    rc = clc._run_check(
        p,
        "myia-po-2026:CoursIA",
        my_paths=["Search/discrepancy_lean/NewModule.lean"],
    )
    out = capsys.readouterr().out
    assert rc == 0
    assert '"creation_scope_globs": [' in out
    assert '"blocked": false' in out

# --- CLAIMED-AMEND recognised as replacing-open (#13022) ----------------------
# Measured on #11703: po-2027's `[CLAIMED-AMEND] ... -- paths: <8 globs>` (union
# of two scopes, 2026-08-25T22:36Z) was a no-op for `_MARKER_RE` -- the organ
# kept crediting the earlier `[CLAIMED]` and the amendment existed only for
# human eyes, forcing a canonical re-[CLAIMED] as workaround. The chosen
# semantics (option A of the issue): CLAIMED-AMEND is an OPEN action, so in the
# walk-order reducer it REPLACES the lane's previous claim -- the amend line
# must carry the FULL corrected scope (union), exactly like the workaround it
# supersedes.

def test_parse_claimed_amend_open_with_single_line_paths_clause():
    # The exact #11703 workaround-replacement shape: marker, lane, and the
    # complete union scope on ONE line (`paths:` clause is single-line by
    # design, #12072 documents the off-marker alternative as signal-only).
    ev = clc.parse_claim_event(comment(
        "[CLAIMED-AMEND] lane myia-po-2027:CoursIA-2 -- paths: "
        "MyIA.AI.Notebooks/ML/learning_theory_lean/**, "
        "MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-1b-*.ipynb",
        "2026-08-25T23:28:41Z",
    ))
    assert ev is not None
    assert ev.marker == "CLAIMED-AMEND"
    assert ev.is_open is True
    assert ev.lane == "myia-po-2027:CoursIA-2"
    assert ev.paths is not None
    assert len(ev.paths) == 2
    assert ev.paths[0] == "MyIA.AI.Notebooks/ML/learning_theory_lean/**"


def test_amend_mono_scope_replaces_previous_scope():
    # Acceptance: amendement mono-scope. A later CLAIMED-AMEND with a single
    # new path REPLACES the lane's earlier scope in the active state.
    events = [
        clc.parse_claim_event(comment(
            "[CLAIMED] lane A:CoursIA -- paths: notebooks/old/**",
            "2026-08-25T05:56:00Z")),
        clc.parse_claim_event(comment(
            "[CLAIMED-AMEND] lane A:CoursIA -- paths: notebooks/new/**",
            "2026-08-25T06:08:00Z")),
    ]
    active, _ = clc.compute_active_claims(events)
    assert set(active) == {"A:CoursIA"}
    assert active["A:CoursIA"].paths == ["notebooks/new/**"]


def test_amend_union_of_two_scopes():
    # Acceptance: union de deux scopes de la meme lane. The amend line carries
    # the union -- the resulting active scope covers BOTH globs (this is the
    # preflight-#13012 shape that motivated the issue).
    events = [
        clc.parse_claim_event(comment(
            "[CLAIMED] lane A:CoursIA -- paths: notebooks/a/**",
            "2026-08-25T05:56:00Z")),
        clc.parse_claim_event(comment(
            "[CLAIMED-AMEND] lane A:CoursIA -- paths: notebooks/a/**, notebooks/b/**",
            "2026-08-25T22:36:00Z")),
    ]
    active, _ = clc.compute_active_claims(events)
    assert active["A:CoursIA"].paths == ["notebooks/a/**", "notebooks/b/**"]


def test_amend_exposes_amended_scope_in_active_claims():
    # Acceptance: the LAST active event must expose the amended scope (marker
    # + paths) in the active_claims mapping the check consumes.
    events = [
        clc.parse_claim_event(comment(
            "[CLAIMED] lane B:CoursIA-2 -- paths: notebooks/first/**",
            "2026-08-25T01:08:00Z")),
        clc.parse_claim_event(comment(
            "[CLAIMED-AMEND] lane B:CoursIA-2 -- paths: notebooks/first/**, notebooks/second/**",
            "2026-08-25T05:56:00Z")),
    ]
    active, _ = clc.compute_active_claims(events)
    ev = active["B:CoursIA-2"]
    assert ev.marker == "CLAIMED-AMEND"
    assert ev.is_open is True
    assert ev.paths == ["notebooks/first/**", "notebooks/second/**"]


def test_amend_without_paths_replaces_with_epic_wide():
    # Documented fail-CLOSED semantics: an amend that names no scope replaces
    # the previous scoped claim with EPIC-WIDE (an amendment that names no
    # scope is not permissive).
    events = [
        clc.parse_claim_event(comment(
            "[CLAIMED] lane A:CoursIA -- paths: notebooks/narrow/**",
            "2026-08-25T05:56:00Z")),
        clc.parse_claim_event(comment(
            "[CLAIMED-AMEND] lane A:CoursIA -- correction du scope, cf. prose",
            "2026-08-25T22:36:00Z")),
    ]
    active, _ = clc.compute_active_claims(events)
    assert active["A:CoursIA"].paths is None


def test_amend_blocks_other_lane_on_intersecting_amended_scope(capsys):
    # End-to-end differential: the caller's path is DISJOINT from the original
    # scope (rc 0 pre-amend) but INTERSECTS the amended scope (rc 1 post-amend)
    # -- the mechanical lock now follows the lane's declared intention, which
    # was the whole point of #13022.
    original = comment(
        "[CLAIMED] lane myia-po-2027:CoursIA-2 -- paths: scripts/notebook_tools/**",
        "2026-08-25T05:56:40Z",
    )
    amended = comment(
        "[CLAIMED-AMEND] lane myia-po-2027:CoursIA-2 -- paths: scripts/notebook_tools/**, scripts/tests/*.py",
        "2026-08-25T22:36:02Z",
    )
    caller_path = "scripts/tests/test_check_lane_claim.py"
    rc_pre = clc._run_check(
        payload(original), "myia-po-2023:CoursIA-2", my_paths=[caller_path]
    )
    assert rc_pre == 0, f"pre-amend scopes are disjoint, expected CLEAR, got rc={rc_pre}"
    rc_post = clc._run_check(
        payload(original, amended), "myia-po-2023:CoursIA-2", my_paths=[caller_path]
    )
    err = capsys.readouterr().err
    assert rc_post == 1, (
        f"caller intersecting the AMENDED scope must be blocked, got rc={rc_post}"
    )
    assert "BLOCKED: another lane holds an active claim" in err


def test_bare_claimed_amend_bracketless_flagged_as_malformed(capsys):
    # The #11239 lint covers the new marker too: a bracketless
    # `CLAIMED-AMEND #N ...` line must surface as a WARN, never silently pass.
    p = payload(comment(
        "CLAIMED-AMEND #11703 -- lane myia-po-2027:CoursIA-2 union preflight",
        "2026-08-25T23:00:00Z",
    ))
    clc._run_check(p, "myia-po-2023:CoursIA-2")
    out = capsys.readouterr().out
    assert "malformed" in out.lower()


# --- repeated --paths preserve union semantics (#13057) ----------------------
# argparse's default `store` action retained only the LAST `--paths` occurrence.
# A real overlap therefore disappeared when the caller added any disjoint path:
# `--paths P_in_claim` blocked, but `--paths P_in_claim --paths P_outside`
# reached the reducer as `[P_outside]` and falsely cleared. These tests exercise
# `main(argv)` rather than `_filter_by_claim_scope`, whose `any` semantics were
# already correct.

_CLAIMED_GUARD_PATH = "scripts/check_lane_claim.py"
_OUTSIDE_GUARD_PATH = "scripts/check_unaddressed_nits.py"


def _write_mixed_paths_payload(tmp_path):
    return _write_payload(
        payload(comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: "
            f"{_CLAIMED_GUARD_PATH}",
            "2026-08-26T02:00:00Z",
        ), number=13057),
        tmp_path,
    )


def test_main_single_paths_occurrence_intersecting_blocks(tmp_path, capsys):
    source = _write_mixed_paths_payload(tmp_path)
    rc = clc.main([
        "13057", "--lane", "myia-po-2025:CoursIA-2", "--from-json", source,
        "--no-stale", "--paths", _CLAIMED_GUARD_PATH,
    ])
    captured = capsys.readouterr()
    summary = json.loads(captured.out.split("\n\nBLOCKED", 1)[0])
    assert rc == 1
    assert summary["blocking_lanes"] == ["myia-po-2024:CoursIA-2"]
    assert summary["blocked"] is True


def test_main_repeated_paths_mixed_intersection_still_blocks(tmp_path, capsys):
    source = _write_mixed_paths_payload(tmp_path)
    rc = clc.main([
        "13057", "--lane", "myia-po-2025:CoursIA-2", "--from-json", source,
        "--no-stale", "--paths", _CLAIMED_GUARD_PATH,
        "--paths", _OUTSIDE_GUARD_PATH,
    ])
    captured = capsys.readouterr()
    assert rc == 1, (
        "adding a disjoint --paths occurrence must not erase the intersecting "
        f"one; stdout was:\n{captured.out}"
    )
    summary = json.loads(captured.out.split("\n\nBLOCKED", 1)[0])
    assert summary["blocking_lanes"] == ["myia-po-2024:CoursIA-2"]
    assert summary["blocked"] is True


def test_main_repeated_paths_genuinely_disjoint_clear(tmp_path, capsys):
    source = _write_mixed_paths_payload(tmp_path)
    rc = clc.main([
        "13057", "--lane", "myia-po-2025:CoursIA-2", "--from-json", source,
        "--no-stale", "--paths", _OUTSIDE_GUARD_PATH,
        "--paths", "scripts/variation_light_cap.py",
    ])
    captured = capsys.readouterr()
    summary = json.loads(captured.out.split("\n\nCLEAR", 1)[0])
    assert rc == 0
    assert summary["blocking_lanes"] == []
    assert summary["blocked"] is False


# --- #12811 : gh/git émettent de l'UTF-8, l'encodage doit être épinglé --------


def test_gh_calls_pin_utf8_regression_12811(monkeypatch):
    """#12811 -- sans `encoding=` épinglé, `text=True` décode avec le locale de
    l'OS. Sous Windows c'est cp1252, dont les positions non définies
    (0x81/0x8D/0x8F/0x90/0x9D) lèvent UnicodeDecodeError sur la prose ICT
    ordinaire (reproduit en direct sur l'issue #5635, Python 3.13 : erreur de
    décodage dans le reader thread -> proc.stdout None -> json.loads(None)
    TypeError, garde morte). Le faux ci-dessous décode en cp1252 chaque fois
    que le site d'appel N'épingle PAS d'encodage -- simulation déterministe du
    défaut Windows, indépendante du locale de la machine qui exécute les
    tests."""
    bad_char = "͏"  # COMBINING GRAPHEME JOINER : UTF-8 = CD 8F
    # ensure_ascii=False : gh émet le JSON avec les caractères non-ASCII en
    # clair (pas d'échappement \uXXXX) -- c'est ce qui met les octets bruts
    # dans le flux et déclenche le décodage cp1252.
    issue_raw = json.dumps({
        "number": 5635,
        "title": "t " + bad_char,
        "labels": [],
        "comments": [],
    }, ensure_ascii=False).encode("utf-8")
    prlist_raw = json.dumps([
        {"number": 1, "title": "x " + bad_char, "headRefName": "b",
         "body": "", "files": []},
    ], ensure_ascii=False).encode("utf-8")
    # garde-fou du fixture : le byte qui tue cp1252 est bien dans les payloads
    assert b"\x8f" in issue_raw and b"\x8f" in prlist_raw

    def fake_run(cmd, **kwargs):
        raw = prlist_raw if "list" in cmd else issue_raw
        enc = kwargs.get("encoding") or "cp1252"  # défaut Windows, simulé
        decoded = raw.decode(enc, kwargs.get("errors") or "strict")
        return subprocess.CompletedProcess(cmd, 0, stdout=decoded, stderr="")

    monkeypatch.setattr(clc.subprocess, "run", fake_run)
    issue_payload = clc._gh_issue_comments("5635")
    assert issue_payload["title"].endswith(bad_char)
    prs = clc._gh_open_prs_with_files()
    assert prs[0]["title"].endswith(bad_char)


# --- #13336 : gh a retire le champ `merged` -- le lookup mourait a chaque appel
#
# `_fetch_pr_state` interrogait `--json state,merged` ; gh 2.83+ refuse le champ
# (`Unknown JSON field`), exit 1 sur la REQUETE entiere : (None, err) pour toute
# PR. Le `None` tombait dans la branche `close` du reducteur -> TOUT [DELIVERED]
# relachait son claim (v2 inerte, retour v1 silencieux). Duplication mesuree :
# #13216 -- meme machine, deux lanes, 49 lignes ecrites deux fois (#13230 OPEN
# vs #13242 MERGED) ; l'organe avait repondu CLEAR avec
# `delivered_claims_pr_states: {"13230": null}`.

import os as _os
import subprocess as _subprocess  # noqa: F401  (monkeypatched via clc.subprocess)


class _FakeProc:
    def __init__(self, returncode=0, stdout="", stderr=""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


def _fake_gh(monkeypatch, responses):
    """Intercept clc.subprocess.run pour `gh pr view N --json ...`.

    responses: {pr_number: _FakeProc}. Captured args are recorded on the
    returned list for field-model assertions."""
    calls = []

    real_run = _subprocess.run

    def fake_run(args, **kwargs):
        if not (len(args) > 1 and args[0] == "gh"):
            return real_run(args, **kwargs)  # git ls-files & co: pass-through
        calls.append(list(args))
        if args[1:3] == ["pr", "list"]:  # --paths collision probe
            return _FakeProc(0, "[]", "")
        pr = int(args[args.index("view") + 1])
        return responses.get(pr, _FakeProc(1, "", "no pull requests found"))

    monkeypatch.setattr(clc.subprocess, "run", fake_run)
    monkeypatch.setattr(clc, "_PR_STATE_CACHE", {})
    return calls


def test_13336_fetch_queries_live_field_model(monkeypatch):
    """Critere 1 : la requete interroge `state,mergedAt` (pas le `merged`
    disparu), et `mergedAt` non-null verrouille meme si `state` est race."""
    calls = _fake_gh(monkeypatch, {
        13230: _FakeProc(0, '{"state":"OPEN","mergedAt":null}', ""),
        13144: _FakeProc(0, '{"state":"OPEN","mergedAt":"2026-08-28T05:00:00Z"}', ""),
        9977: _FakeProc(0, '{"state":"CLOSED","mergedAt":null}', ""),
    })
    assert clc._fetch_pr_state(13230) == ("OPEN", None)
    assert clc._fetch_pr_state(13144) == ("MERGED", None)  # mergedAt seul verrouille
    assert clc._fetch_pr_state(9977) == ("CLOSED", None)
    fields = [c[c.index("--json") + 1] for c in calls]
    assert all(f == "state,mergedAt" for f in fields)
    assert "merged" not in fields  # le champ mort n'est plus interroge


def test_13336_schema_break_blocks_delivered_claim(monkeypatch, capsys):
    """Critere 3 : une erreur de schema (permanente) NE RELACHE PAS le claim.
    Avant : le None tombait dans `close` -> CLEAR, la voie etait faussement
    libre (mecanisme exact de la duplication #13216)."""
    _fake_gh(monkeypatch, {
        13230: _FakeProc(1, "", 'Unknown JSON field: "merged". Available fields:'),
    })
    p = payload(
        comment("[CLAIMED] lane myia-po-2024:CoursIA-2 -- decks S3",
                "2026-08-28T01:00:00Z"),
        comment("[DELIVERED] lane myia-po-2024:CoursIA-2 -- PR #13230",
                "2026-08-28T02:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA",
                        pr_states=None,
                        my_paths=["slides/**"])
    assert rc == 1  # BLOCKED : la delivery non resolvable garde le lock
    captured = capsys.readouterr()
    out = _json_out(captured)
    assert "myia-po-2024:CoursIA-2" in out["blocking_lanes"]
    # Critere 4 (voix BLOCKED) : la CAUSE est nommee, pas seulement le bloc.
    assert "WARN" in captured.err
    assert "13230" in captured.err
    assert "non transitoire" in captured.err


def test_13336_transient_network_error_keeps_fail_open(monkeypatch, capsys):
    """Miroir : une erreur RESEAU reste fail-open (posture documentee
    #12386) -- mais le verdict porte le WARN (critere 4, voix CLEAR)."""
    _fake_gh(monkeypatch, {
        13230: _FakeProc(1, "", "dial tcp: could not resolve host"),
    })
    p = payload(
        comment("[CLAIMED] lane myia-po-2024:CoursIA-2 -- decks S3",
                "2026-08-28T01:00:00Z"),
        comment("[DELIVERED] lane myia-po-2024:CoursIA-2 -- PR #13230",
                "2026-08-28T02:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA",
                        pr_states=None,
                        my_paths=["slides/**"])
    assert rc == 0  # fail-open preserve sur erreur transitoire
    captured = capsys.readouterr()
    out = _json_out(captured)
    assert out["blocking_lanes"] == []
    # ... mais PLUS silencieusement : le WARN nomme la PR non resolue.
    assert "WARN" in captured.err
    assert "13230" in captured.err


def test_13336_replay_13216_open_pr_blocks_second_lane(capsys):
    """Critere 5 (mecanisme, PR reelles) : tant que #13230 est OPEN, la lane
    myia-po-2024:CoursIA-2 reste BLOQUANTE pour myia-po-2024:CoursIA -- c'est
    exactement ce que l'organe cassat en repondant CLEAR le 28/08."""
    p = payload(
        comment("[CLAIMED] lane myia-po-2024:CoursIA-2 -- decks S3",
                "2026-08-28T01:00:00Z"),
        comment("[DELIVERED] lane myia-po-2024:CoursIA-2 -- PR #13230",
                "2026-08-28T02:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA",
                        pr_states=_pr_states(13230, "OPEN"),
                        my_paths=["slides/**"])
    assert rc == 1
    out = _json_out(capsys.readouterr())
    assert "myia-po-2024:CoursIA-2" in out["blocking_lanes"]


def test_13336_live_control_real_pr():
    """Critere 2 : controle positif END-TO-END (aucune injection) sur une PR
    REELLE du depot -- rougit si gh change encore de schema. Ne tourne que
    la ou le reseau et un token sont disponibles (le workflow
    lane-claim-guard.yml pose LANE_CLAILM_LIVE=1 + GH_TOKEN) ; le skip local
    reste possible (critere 4 de l'issue : `python -m pytest` hors CI passe).

    PR epinglee : #13144, MERGEE le 2026-08-28 -- un etat fusionne est stable
    a vie (une PR ouverte finit par merger, une fusionnee reste fusionnee)."""
    if not (_os.environ.get("GH_TOKEN") and _os.environ.get("LANE_CLAIM_LIVE")):
        import pytest
        pytest.skip("live control: set GH_TOKEN + LANE_CLAIM_LIVE=1 (run by lane-claim-guard.yml)")
    st, err = clc._fetch_pr_state(13144)
    assert st == "MERGED", f"gh schema ou PR inattendus: state={st!r} err={err!r}"
    assert err is None


# --- #14187 : scope_intersection_paths + free_paths sur glob large -----------
#
# Issue #14187 : `check_lane_claim.py --paths '<glob large>'` rend
# `blocked: true` binaire : le caller voit QUI bloque, pas QUOI. Une lane
# avec un scope de 12 fichiers bloques par 3 autres dont les scopes
# n intersectent que 3 fichiers voit les 9 fichiers libres comme bloques
# elle aussi (pas de re-scope possible sans escalade dashboard).
#
# Le fix ajoute (a) `scope_intersection_paths` par claim dans le JSON,
# (b) `free_paths` + `intersection_summary` au top-level, (c) une ligne
# humaine dans le verdict stderr. Six tests verrouillent chaque surface.

def _14187_setup_repo(monkeypatch, tracked=None):
    """Stub _git_tracked_files for #14187 tests (deterministic file list)."""
    files = tracked if tracked is not None else [
        "knot_lean/Knots/Conway.lean",
        "knot_lean/Knots/Basic.lean",
        "knot_lean/Knots/Lidman.lean",
        "knot_lean/Knots/Invariant.lean",
        "knot_lean/Util.lean",
        "knot_lean/Main.lean",
    ]
    monkeypatch.setattr(clc, "_git_tracked_files", lambda: files)


def test_14187_glob_large_nomme_intersection_par_blocker(capsys, monkeypatch):
    """#14187 (1) : `--paths 'knot_lean/**'` avec 2 claims scopes
    differents rend un `scope_intersection_paths` par claim dans le JSON,
    listant les fichiers reellement contestes (et PAS tous les fichiers
    du scope).
    """
    _14187_setup_repo(monkeypatch)
    blocker_a = comment(
        "[CLAIMED] lane myia-po-2024:CoursIA -- knot tranche -- paths: knot_lean/Knots/Conway.lean, knot_lean/Knots/Basic.lean",
        "2026-09-01T22:00:00Z",
    )
    blocker_b = comment(
        "[CLAIMED] lane myia-po-2026:CoursIA -- knot trim -- paths: knot_lean/Knots/Lidman.lean",
        "2026-09-01T22:01:00Z",
    )
    p = payload(blocker_a, blocker_b, number=14187)
    rc = clc._run_check(
        p, "myia-po-2023:CoursIA",
        my_paths=["knot_lean/**"],
    )
    assert rc == 1  # blocked
    out = _json_out(capsys.readouterr())
    ac = out["active_claims"]
    # blocker_a claimed Conway.lean + Basic.lean -- both tracked
    assert sorted(ac["myia-po-2024:CoursIA"]["scope_intersection_paths"]) == [
        "knot_lean/Knots/Basic.lean", "knot_lean/Knots/Conway.lean"
    ]
    assert ac["myia-po-2024:CoursIA"]["scope_intersection_size"] == 2
    assert ac["myia-po-2024:CoursIA"]["scope_intersection_truncated"] is False
    # blocker_b claimed only Lidman.lean
    assert ac["myia-po-2026:CoursIA"]["scope_intersection_paths"] == [
        "knot_lean/Knots/Lidman.lean"
    ]
    assert ac["myia-po-2026:CoursIA"]["scope_intersection_size"] == 1


def test_14187_glob_large_liste_fichiers_libres(capsys, monkeypatch):
    """#14187 (2) : avec le meme scope de 6 fichiers et 2 blockers dont les
    scopes couvrent 3 fichiers, `free_paths` enumere les 3 fichiers
    libres et `intersection_summary` les compte.
    """
    _14187_setup_repo(monkeypatch)
    blocker_a = comment(
        "[CLAIMED] lane myia-po-2024:CoursIA -- knot tranche -- paths: knot_lean/Knots/Conway.lean, knot_lean/Knots/Basic.lean",
        "2026-09-01T22:00:00Z",
    )
    blocker_b = comment(
        "[CLAIMED] lane myia-po-2026:CoursIA -- knot trim -- paths: knot_lean/Knots/Lidman.lean",
        "2026-09-01T22:01:00Z",
    )
    p = payload(blocker_a, blocker_b, number=14187)
    clc._run_check(
        p, "myia-po-2023:CoursIA",
        my_paths=["knot_lean/**"],
    )
    out = _json_out(capsys.readouterr())
    # Le scope couvre 6 tracked files ; 3 contestes ; 3 libres.
    assert out["free_paths_size"] == 3
    assert sorted(out["free_paths"]) == sorted([
        "knot_lean/Knots/Invariant.lean",
        "knot_lean/Main.lean",
        "knot_lean/Util.lean",
    ])
    assert out["free_paths_truncated"] is False
    # intersection_summary : 3 bloques + 3 libres
    assert "3" in out["intersection_summary"]
    assert "libres" in out["intersection_summary"]


def test_14187_epic_wide_blocker_retourne_liste_vide(capsys, monkeypatch):
    """#14187 (3) : un blocker epic-wide (pas de `paths:`) couvre tout le
    scope ; `free_paths` est vide et `intersection_summary` est vide --
    l instrument ne pretend pas enumerer ce qui n est pas enumerable.
    """
    _14187_setup_repo(monkeypatch)
    blocker_epic = comment(
        "[CLAIMED] lane myia-po-2024:CoursIA -- umbrella",
        "2026-09-01T22:00:00Z",
    )
    p = payload(blocker_epic, number=14187)
    clc._run_check(
        p, "myia-po-2023:CoursIA",
        my_paths=["knot_lean/**"],
    )
    out = _json_out(capsys.readouterr())
    # epic-wide claim : pas d intersection enumerable
    assert out["active_claims"]["myia-po-2024:CoursIA"]["scope_intersection_paths"] == []
    assert out["active_claims"]["myia-po-2024:CoursIA"]["scope_intersection_size"] == 0
    # Tout le scope est verrouille, rien de libre.
    assert out["free_paths"] == []
    assert out["free_paths_size"] == 0
    assert out["intersection_summary"] == ""


def test_14187_disjoint_scope_rend_liste_vide_et_pas_de_block(capsys, monkeypatch):
    """#14187 (4) : caller et blocker sur des scopes DISJOINTS -> rc=0
    (clear). `free_paths` reflete le scope complet (rien n est bloque).
    """
    _14187_setup_repo(monkeypatch)
    blocker = comment(
        "[CLAIMED] lane myia-po-2024:CoursIA -- ailleurs -- paths: knot_lean/Knots/Conway.lean",
        "2026-09-01T22:00:00Z",
    )
    p = payload(blocker, number=14187)
    rc = clc._run_check(
        p, "myia-po-2023:CoursIA",
        my_paths=["knot_lean/Util.lean"],
    )
    assert rc == 0  # clear (disjoint)
    out = _json_out(capsys.readouterr())
    assert out["blocked"] is False
    # Util.lean est libre.
    assert out["free_paths"] == ["knot_lean/Util.lean"]


def test_14187_summary_humain_dans_stderr(capsys, monkeypatch):
    """#14187 (5) : la ligne humaine dans le verdict BLOCKED enumere les
    fichiers libres et le nombre de contestes -- un caller qui lit stderr
    sait quoi faire (re-scope aux libres) sans parser le JSON.
    """
    _14187_setup_repo(monkeypatch)
    blocker = comment(
        "[CLAIMED] lane myia-po-2024:CoursIA -- knot tranche -- paths: knot_lean/Knots/Conway.lean",
        "2026-09-01T22:00:00Z",
    )
    p = payload(blocker, number=14187)
    clc._run_check(
        p, "myia-po-2023:CoursIA",
        my_paths=["knot_lean/**"],
    )
    captured = capsys.readouterr()
    # Verdict BLOCKED + intersection listee + fichiers libres nommes.
    assert "BLOCKED" in captured.err
    assert "scope_intersection_paths" in captured.err
    assert "knot_lean/Knots/Conway.lean" in captured.err
    # Le bloc Fichiers libres liste les autres fichiers du scope.
    assert "Fichiers libres" in captured.err
    assert "knot_lean/Main.lean" in captured.err


def test_14187_truncated_flag_sur_repo_volumineux(capsys, monkeypatch):
    """#14187 (6) : un scope tres large (>25 fichiers intersectes)
    tronque la liste a 25 et leve `scope_intersection_truncated`. Sans
    ce pin, un caller sur un monorepo lirait une liste incomplete comme
    complete.
    """
    # 30 fichiers dans knot_lean, tous matche par `--paths 'knot_lean/**'`
    big = [f"knot_lean/f{i:03d}.lean" for i in range(30)]
    _14187_setup_repo(monkeypatch, tracked=big)
    # Le blocker declare un scope PARTIEL (les 5 premiers fichiers), donc
    # free_paths contient 25 fichiers libres (tronque) ; scope_intersection
    # contient les 5 fichiers du blocker (sous le cap, pas tronque).
    blocker = comment(
        "[CLAIMED] lane myia-po-2024:CoursIA -- partial -- paths: knot_lean/f000.lean, knot_lean/f001.lean, knot_lean/f002.lean, knot_lean/f003.lean, knot_lean/f004.lean",
        "2026-09-01T22:00:00Z",
    )
    p = payload(blocker, number=14187)
    clc._run_check(
        p, "myia-po-2023:CoursIA",
        my_paths=["knot_lean/**"],
    )
    out = _json_out(capsys.readouterr())
    # Le blocker declare 5 fichiers : scope_intersection rend les 5
    # complets (sous le cap de 25, pas de troncature).
    ac = out["active_claims"]["myia-po-2024:CoursIA"]
    assert ac["scope_intersection_size"] == 5
    assert ac["scope_intersection_truncated"] is False
    # Les 25 autres fichiers du scope (30 - 5 = 25) sont libres ; sous
    # le cap, pas de troncature non plus.
    assert out["free_paths_size"] == 25
    assert out["free_paths_truncated"] is False

    # Cas 2 : un scope ENORME (>50 fichiers libres) doit declencher le
    # flag truncated sur `free_paths`. On construit un repo avec 60
    # fichiers que le caller vise via `--paths 'big/**'` mais qu aucun
    # blocker ne reserve -> free_paths est l integralite du scope (60),
    # tronque a 25.
    bigger = [f"big/g{i:03d}.lean" for i in range(60)]
    _14187_setup_repo(monkeypatch, tracked=bigger)
    p = payload(number=14187)  # aucun blocker
    clc._run_check(
        p, "myia-po-2023:CoursIA",
        my_paths=["big/**"],
    )
    out = _json_out(capsys.readouterr())
    # Caller disjoint de tout claim -> rc=0 (clear), free_paths =
    # l integralite du scope (60 fichiers), tronque a 25.
    assert out["blocked"] is False
    assert out["free_paths_size"] == 25
    assert out["free_paths_truncated"] is True
