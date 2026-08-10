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
    # Plain `[CLAIMED]` (not an override) is always epic-wide, even when the
    # caller supplies `--paths`. The scope is a coordinator's adjudication
    # tool; a worker's claim never carries it. This pins the boundary.
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
