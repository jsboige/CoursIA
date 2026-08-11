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


def payload(*comments, number=9764, title="t"):
    return {"number": number, "title": title, "comments": list(comments)}


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
    for marker in ("RELEASED", "DONE", "CANCELLED", "ABANDONED"):
        ev = clc.parse_claim_event(comment(
            f"[{marker}] lane myia-po-2024:CoursIA -- done",
            "2026-08-06T23:00:00Z",
        ))
        assert ev is not None
        assert ev.is_open is False
        assert ev.marker == marker


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


def test_check_blocked_when_claim_comment_mentions_marker_in_prose(capsys):
    # Full-flow regression for the #10228 FN: a claim comment that ALSO mentions
    # a close marker in instructional prose must still BLOCK another lane. This
    # is the exact shape of ai-01's dispatch comments (claim + release instructions).
    body = (
        "[CLAIMED] lane myia-po-2025:CoursIA-2 -- Taches 1-2 (CPU).\r\n\r\n"
        "(Release with `[RELEASED]` when your PR lands.)"
    )
    p = payload(comment(body, "2026-08-09T21:19:00Z", author="myia-ai-01"))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    assert rc == 1                          # BLOCKED, not CLEAR (the FN returned 0)
    captured = capsys.readouterr()
    assert "BLOCKED" in captured.err
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


def test_check_blocked_when_other_lane_active(capsys):
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- working here",
        "2026-08-06T22:43:31Z",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    assert rc == 1
    captured = capsys.readouterr()
    assert "BLOCKED" in captured.err
    assert "myia-po-2025:CoursIA" in captured.out


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


def test_stale_threshold_fresh_claim_still_blocks(capsys):
    # Other lane claimed 2h ago; threshold 24h -> still BLOCKED.
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- working here",
        "2026-08-07T10:00:00Z",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA",
                        stale_threshold=24.0, now=NOW)
    assert rc == 1
    captured = capsys.readouterr()
    assert "BLOCKED" in captured.err


def test_stale_threshold_stale_plus_fresh_blocks_on_fresh(capsys):
    # Two other lanes: one stale (48h), one fresh (1h). The fresh one blocks.
    p = payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA -- old",
                "2026-08-05T12:00:00Z"),
        comment("[CLAIMED] lane myia-po-2023:CoursIA -- fresh",
                "2026-08-07T11:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA",
                        stale_threshold=24.0, now=NOW)
    assert rc == 1
    captured = capsys.readouterr()
    # The stale one is warned about, the fresh one blocks.
    assert "STALE_CLAIM myia-po-2025:CoursIA" in captured.err
    assert "BLOCKED" in captured.err
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
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- very old orphan",
        "2026-08-01T00:00:00Z",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA", now=NOW)
    assert rc == 1
    captured = capsys.readouterr()
    assert "STALE_CLAIM" not in captured.err
    assert "BLOCKED" in captured.err


def test_stale_threshold_unparseable_not_treated_stale(capsys):
    # A claim whose createdAt is unparseable cannot be dated -> NOT stale
    # (conservative: we cannot prove an age, so we do not lift the block).
    p = payload(comment(
        "[CLAIMED] lane myia-po-2025:CoursIA -- undated",
        "not-an-iso-date",
    ))
    rc = clc._run_check(p, "myia-po-2024:CoursIA",
                        stale_threshold=24.0, now=NOW)
    assert rc == 1


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
    # I claimed, then the coordinator overrode to ANOTHER lane -> BLOCKED for me.
    p = payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- working here",
                "2026-08-09T11:41:43Z"),
        comment("[OVERRIDE] lane myia-po-2026:CoursIA -- reassign",
                "2026-08-09T22:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA-2")
    assert rc == 1
    captured = capsys.readouterr()
    assert "BLOCKED" in captured.err
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


# --- the actual SCOPE behaviour at the check layer ---------------------------

def test_check_override_no_paths_preserves_legacy_epic_wide_behaviour(capsys):
    # Override WITHOUT `paths:` clause, check WITHOUT `--paths` -> legacy
    # epic-wide block. This pins backward compatibility: a caller that did
    # not opt into the new scope mechanism keeps the old behaviour.
    p = payload(
        comment("[CLAIMED] lane myia-po-2026:CoursIA -- original",
                "2026-08-09T11:00:00Z"),
        comment("[OVERRIDE] lane myia-po-2024:CoursIA -- substance favors",
                "2026-08-09T22:00:00Z"),
    )
    rc = clc._run_check(p, "myia-po-2026:CoursIA")
    assert rc == 1
    captured = capsys.readouterr()
    assert "BLOCKED" in captured.err
    assert "myia-po-2024:CoursIA" in captured.out


def test_check_override_paths_blocks_other_lane_on_matching_path(capsys):
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
    assert rc == 1
    captured = capsys.readouterr()
    assert "BLOCKED" in captured.err
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
    # so the verdict is BLOCKED; that is not what this test is pinning. We
    # only check that the scope payload leaks into the JSON, NOT the verdict.
    p = payload(
        comment(
            "[OVERRIDE] lane myia-po-2024:CoursIA -- paths: Lean/**, scripts/**",
            "2026-08-09T22:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA-2")
    out = capsys.readouterr().out
    assert rc == 1  # override granted A, so B is blocked (epic-wide read)
    assert "Lean/**" in out
    assert "scripts/**" in out


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
            "paths: MyIA.AI.Notebooks/Sudoku/Sudoku-9-GraphColoring-Csharp.ipynb",
            "2026-08-11T04:02:00Z",
        )
    )
    assert ev is not None
    assert ev.marker == "CLAIMED"
    assert ev.is_open
    assert ev.paths == [
        "MyIA.AI.Notebooks/Sudoku/Sudoku-9-GraphColoring-Csharp.ipynb",
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
                "paths: Search/Part1-Foundations/Search-3-Informed-Csharp.ipynb",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane myia-po-2023:CoursIA -- "
                "paths: Sudoku/Sudoku-9-GraphColoring-Csharp.ipynb",
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
    p = payload(
        comment("[CLAIMED] lane myia-po-2023:CoursIA -- "
                "paths: Sudoku/Sudoku-9-GraphColoring-Csharp.ipynb",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane myia-po-2024:CoursIA -- "
                "paths: Planning/Planners-5-Heuristics-Csharp.ipynb",
                "2026-08-11T04:03:00Z"),
        comment("[CLAIMED] lane myia-po-2025:CoursIA -- "
                "paths: Search/Part1-Foundations/Search-3-Informed-Csharp.ipynb",
                "2026-08-11T04:04:00Z"),
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- "
                "paths: Search/Part1-Foundations/Search-5-GeneticAlgorithms-Csharp.ipynb",
                "2026-08-11T04:05:00Z"),
        comment("[CLAIMED] lane myia-po-2026:CoursIA -- "
                "paths: GameTheory/GameTheory-4-NashEquilibrium-Csharp.ipynb",
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
        comment("[CLAIMED] lane A:CoursIA -- paths: Sudoku/Sudoku-9.ipynb",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane B:CoursIA-2 -- paths: Sudoku/Sudoku-9.ipynb",
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
    p = payload(
        comment("[CLAIMED] lane A:CoursIA -- paths: Search/Search-3.ipynb",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane B:CoursIA-2 -- working on Sudoku",
                "2026-08-11T04:05:00Z"),
    )
    rc = clc._run_check(p, "A:CoursIA")
    assert rc == 1
    assert "B:CoursIA-2" in capsys.readouterr().err


def test_check_my_claim_scope_derived_from_claim_not_just_cli(capsys):
    # my_scope is built from the caller's OWN [CLAIMED] paths clause, NOT only
    # from --paths. A lane that posted a scoped [CLAIMED] but calls the check
    # without --paths still gets disjointness honoured against another scoped
    # lane. This is the leg that makes the #10419 fix usable without forcing
    # every worker to pass --paths on every invocation.
    p = payload(
        comment("[CLAIMED] lane A:CoursIA -- paths: Lean/Foo.lean",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane B:CoursIA-2 -- paths: scripts/foo.py",
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
        comment("[CLAIMED] lane A:CoursIA -- paths: Lean/Foo.lean",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane B:CoursIA-2 -- paths: scripts/bar.py",
                "2026-08-11T04:05:00Z"),
    )
    rc = clc._run_check(p, "A:CoursIA", my_paths=["scripts/bar.py"])
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
    """Two lanes with disjoint marker-line excerpts both render in BLOCKED."""
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
    assert rc == 1
    err = capsys.readouterr().err
    # The bare BLOCKED message used to say "Do not start -- pick another grain,
    # or wait for release." Variante 2 adds the side-by-side intent block.
    assert "BLOCKED" in err
    assert "Part1-Foundations BFS notebook" in err
    assert "Part3-Advanced A* notebook" in err
    assert "Claimed scopes" in err  # the new header line


def test_trio_ortools_scenario_disjoint_intents_visible(capsys):
    """Trio OR-Tools scenario (the decisive test for Variante 2).

    Three lanes, each with a valid [CLAIMED] on the same EPIC #10382 but
    on DISJOINT notebooks. The block is the tool's job (the reducer keeps
    them all in `others` -- epic-wide semantics are preserved). The FIX is
    that the BLOCKED verdict now surfaces all three intents side-by-side,
    so a coordinator reads "three disjoint notebooks" at a glance instead
    of "three blocking claims" and can decide whether the scope overlap
    actually warrants arbitration, or whether each lane can proceed.
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
    # Reducer keeps all three in `others` (no scope mechanism for [CLAIMED]
    # yet -- that's the next iteration; the immediate fix is the verdict
    # SURFACES them legibly).
    assert rc == 1
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
    printed in the BLOCKED verdict. This is the common case (the lane token
    IS the intent excerpt when the author writes nothing else)."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2025:CoursIA",
            "2026-08-10T14:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    assert rc == 1
    err = capsys.readouterr().err
    assert "BLOCKED" in err
    # The intent is the lane token (the only thing on the marker line).
    assert "myia-po-2025:CoursIA" in err


def test_blocked_message_includes_paths_narrowing_hint(capsys):
    """The new BLOCKED hint mentions `[CLAIMED] paths: ...` as a narrowing
    path. The path-scope clause is already supported for [OVERRIDE] (#10342);
    [CLAIMED] with paths: is a natural follow-up, but the immediate value of
    Variante 2 is to teach the reader that this is the next move.
    """
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2025:CoursIA — working here",
            "2026-08-10T14:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA")
    assert rc == 1
    err = capsys.readouterr().err
    assert "paths:" in err
    assert "scope-narrowing" in err
