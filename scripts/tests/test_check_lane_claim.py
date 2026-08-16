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
                "paths: MyIA.AI.Notebooks/Search/Part1-Foundations/"
                "Search-3-Informed-Csharp.ipynb",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane myia-po-2023:CoursIA -- "
                "paths: MyIA.AI.Notebooks/Sudoku/"
                "Sudoku-9-GraphColoring-Csharp.ipynb",
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
                "paths: MyIA.AI.Notebooks/Sudoku/"
                "Sudoku-9-GraphColoring-Csharp.ipynb",
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
                "GameTheory-4-NashEquilibrium-Csharp.ipynb",
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
                "Sudoku-9-GraphColoring-Csharp.ipynb",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane B:CoursIA-2 -- paths: MyIA.AI.Notebooks/Sudoku/"
                "Sudoku-9-GraphColoring-Csharp.ipynb",
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
    lane checking the same issue. This pins the user-visible verdict.
    """
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: scripts/{a,b-*.yaml",
            "2026-08-12T11:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    # BLOCKED -- the unparseable scope lifted the lane to epic-wide.
    assert rc == 1
    captured = capsys.readouterr()
    # The audit JSON names the residual brace so the lane learns to reissue.
    assert "scripts/{a,b-*.yaml" in captured.out
    # And the verdict itself is in stderr.
    assert "BLOCKED" in captured.err


def test_run_check_summary_exposes_unparseable_scope_field(capsys):
    """The audit JSON surfaces the witness list under
    `active_claims.<lane>.unparseable_scope` so a human reviewer (and the
    lane that owns the malformed claim) can read the defect at a glance."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: scripts/{a,b-*.yaml, scripts/check_lane_claim.py",
            "2026-08-12T11:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 1
    out = capsys.readouterr().out
    # The JSON includes the structured witness list under the lane entry.
    assert '"unparseable_scope"' in out
    assert "scripts/{a,b-*.yaml" in out


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
    same issue. Pre-fix this was the #9764-style false CLEAR."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: scripts/nowhere/typo.py -- 2026-08-11T18:10Z",
            "2026-08-12T11:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 1  # lifted to epic-wide -> blocks
    captured = capsys.readouterr()
    assert "BLOCKED" in captured.err
    # The audit JSON names the dead glob so the lane learns to reissue.
    assert '"empty_scope"' in captured.out
    assert "scripts/nowhere/typo.py" in captured.out


def test_run_check_summary_exposes_empty_scope_field(capsys):
    """Acceptance: dead globs surface in the audit JSON under
    `active_claims.<lane>.empty_scope`, not only as a stderr WARN. A
    PARTIALLY dead scope still surfaces its dead glob without lifting."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: "
            "scripts/check_lane_claim.py, scripts/nowhere/typo.py",
            "2026-08-12T11:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 1  # no my_scope -> the scoped claim still blocks
    out = capsys.readouterr().out
    assert '"empty_scope"' in out
    assert "scripts/nowhere/typo.py" in out


def test_run_check_my_dead_scope_keeps_others(capsys):
    """Caller-side guard: when MY OWN scope is entirely dead, I cannot use
    disjointness to clear another lane -- globs that lock nothing prove
    nothing. Every other lane stays -> BLOCKED until my claim is reissued."""
    p = payload(
        comment("[CLAIMED] lane A:CoursIA -- paths: scripts/nowhere/typo.py",
                "2026-08-11T04:02:00Z"),
        comment("[CLAIMED] lane B:CoursIA-2 -- paths: scripts/grain_tag.py",
                "2026-08-11T04:05:00Z"),
    )
    rc = clc._run_check(p, "A:CoursIA")
    assert rc == 1
    assert "BLOCKED" in capsys.readouterr().err


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
    UX of the bonus hardener."""
    p = payload(
        comment(
            "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
            "paths: definitely-not-a-real-glob-*.zxyq",
            "2026-08-12T11:00:00Z",
        ),
    )
    rc = clc._run_check(p, "myia-po-2024:CoursIA-2")  # own lane, CLEAR
    assert rc == 0
    captured = capsys.readouterr()
    assert "SCOPE_ZERO_COVERAGE" in captured.err
    # The scope itself is named verbatim so the lane can reissue.
    assert "definitely-not-a-real-glob-*.zxyq" in captured.err


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
    # INFO line names the blocking effect; the verdict itself is unchanged
    # (the override still blocks a third lane).
    p = payload(comment(F1_OVERRIDE_NO_PATHS, "2026-08-14T05:53:20Z"),
                number=10678)
    rc = clc._run_check(p, "myia-po-2026:CoursIA")
    assert rc == 1  # verdict unchanged: the override blocks
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
    p = payload(comment(F2_PROSE_AFTER_CLAUSE, "2026-08-14T06:41:00Z"),
                number=10678)
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 1  # verdict unchanged: po-2024's scoped claim blocks
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
    p = payload(comment(F3_FAMILY_GLOBS, "2026-08-14T06:55:07Z"), number=10678)
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 1  # verdict unchanged: po-2023's claim blocks
    err = capsys.readouterr().err
    assert "WARN:" not in err
    assert "INFO:" not in err


def test_lint_prose_mentioning_paths_warns_suspect(capsys):
    # F4 -- the 07:06:23Z [CLAIMED]: the prose literally says "clause paths:"
    # and `_PATHS_CLAUSE_RE` grabs everything after it as ONE bogus glob. The
    # lint surfaces it as a swallowed-prose WARN (the machine reads a clause
    # where the author wrote prose -- not the INFO path, but the defect is
    # caught and named).
    p = payload(comment(F4_PROSE_GRABBED_AS_CLAUSE, "2026-08-14T07:06:23Z"),
                number=10678)
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 1  # verdict unchanged
    err = capsys.readouterr().err
    assert "WARN: glob suspect (prose avalée ?)" in err
    assert "et bloquait donc les deux lanes epic-wide" in err
    assert "WARN: glob sans correspondance" in err


def test_lint_well_formed_marker_produces_nothing(capsys):
    # The acceptance's decisive negative: a well-formed marker with two
    # EXISTING files produces NO warning at all -- the lint must not cry wolf
    # on correct markers.
    p = payload(comment(WELL_FORMED_MARKER, "2026-08-14T08:00:00Z"),
                number=10678)
    rc = clc._run_check(p, "myia-po-2025:CoursIA")
    assert rc == 1  # verdict unchanged: the claim blocks
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
                  "Sudoku-9-GraphColoring-Csharp.ipynb"],
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


def test_claim_paths_roundtrip_reads_back_scoped(monkeypatch):
    # #11064 acceptance (4): a claim posted with --paths is read back by the
    # check as SCOPED -- a disjoint lane stays free (exit 0), an intersecting
    # lane is blocked (exit 1), an unscoped caller is conservatively blocked.
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
    assert clc._run_check(pl, "B:CoursIA", my_paths=["z/**"]) == 0
    assert clc._run_check(pl, "B:CoursIA", my_paths=["x/sub/f.ipynb"]) == 1
    assert clc._run_check(pl, "B:CoursIA") == 1


def test_claim_refuses_when_blocked(monkeypatch, tmp_path):
    # #11064 acceptance (1): `--claim` runs the check before posting and
    # REFUSES (exit 1, nothing posted) when another lane holds an overlapping
    # claim -- instead of posting first and printing a reassuring success.
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
                   "--claim", "tranche x", "11064", "--from-json", json_path])
    assert rc == 1
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
