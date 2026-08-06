#!/usr/bin/env python3
"""Lane-claim guard -- the "one command before you edit" of issue #9774.

#9774 (mandat user 2026-08-06) diagnosed why two lanes delivered #9764 twice:
the `[CLAIMED]` signal lived on the per-lane dashboard, which (a) does not cross
lanes, (b) is garbage-collected by auto-condensation, and (c) mixed local and
UTC timestamps -- a stamp `2026-08-07T00:52Z` that was actually 00:52 CEST
inverted the cross-lane claim order and nearly got the coordinator to entrench
the wrong priority. None of it was a discipline failure: both workers passed
their `gh pr list` guard, which only sees PUSHED work. The collision is born in
the "I decided to work on X" -> "I pushed" window, where the only signal is the
claim, and the claim was in a silo.

This tool operationalises the worker-side of the fix (the rule change itself
needs user sign-off; this is the mechanism that the rule will call):

  - **check** (default): before editing a file for a grain on issue #N, run
        check_lane_claim.py N --lane myia-po-2024:CoursIA
    It reads the issue comments, reconstructs the claim state per lane, and
    exits 1 if ANOTHER lane holds an active (unreleased) claim -- do not start,
    pick elsewhere. Exit 0 means the way is clear (optionally: your own lane
    already claimed, you are resuming).

  - **--claim "<intention>"**: post a `[CLAIMED] lane <machine:workspace>`
    comment. GitHub server-stamps it UTC -- the body carries NO timestamp, so
    Defaut 2 (local time wearing a `Z` suffix) is impossible by construction.

  - **--release [--note "..."]**: post a `[RELEASED]` comment, closing the
    active claim of this lane on the issue.

The authoritative timestamp is the comment's server `createdAt`, NEVER a stamp
written in the body. That is the whole of the Defaut-2 fix.

The lane token is read by `grain_tag.extract_lane` -- the SAME reader the Grain
tag and the G-VAR-2 organ use (#9485, single reader), so a claim comment and a
PR body never disagree on what a lane is.

Limitation (documented): claim state is comment-based. A merged PR that
references the issue is not auto-detected as a release -- the lane should
`--release` (or post `[DONE]`) when its PR lands. Detecting merges is a future
flag; the comment contract is the MVP.

Exit codes: 0 ok / 1 blocked (other lane holds active claim) / 2 io-or-gh error.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# Shared lane reader (#9485) -- see scripts/grain_tag.py.
from grain_tag import extract_lane

# --- markers -----------------------------------------------------------------

# A comment is a claim EVENT only if it carries one of these bracketed markers.
# `[DONE]`/`[RELEASED]`/`[CANCELLED]`/`[ABANDONED]` close a claim; `[CLAIMED]`
# opens one. Read on ISSUE comments (the claim registry per #9774), not on the
# dashboard. Case-insensitive, tolerates inner spaces.
_MARKER_RE = re.compile(
    r"\[\s*(CLAIMED|RELEASED|CANCELLED|ABANDONED|DONE)\s*\]", re.IGNORECASE
)
_OPEN = {"CLAIMED"}
_CLOSE = {"RELEASED", "CANCELLED", "ABANDONED", "DONE"}


class ClaimEvent(dict):
    """Typed-ish view over a parsed claim event.

    Keys: lane (str|None), action ("open"|"close"), marker (str upper),
    created_at (str ISO, server UTC), author (str|None), url (str|None).
    `created_at` comes from the comment's server field, never from the body.
    """

    @property
    def lane(self) -> str | None:
        return self.get("lane")

    @property
    def is_open(self) -> bool:
        return self.get("action") == "open"

    @property
    def created_at(self) -> str | None:
        return self.get("created_at")

    @property
    def marker(self) -> str | None:
        return self.get("marker")

    @property
    def author(self) -> str | None:
        return self.get("author")

    @property
    def url(self) -> str | None:
        return self.get("url")


def parse_claim_event(comment: dict) -> ClaimEvent | None:
    """Classify one issue comment into a claim event, or None if not a marker.

    The decisive marker is the LAST bracketed one in the body (final intent).
    The lane is read by `extract_lane`; None when the body carries no lane token
    (surfaced as "unattributed", never guessed). The timestamp is the comment's
    server `createdAt` -- the Defaut-2 fix: body stamps are not trusted.
    """
    body = comment.get("body") or ""
    marks = _MARKER_RE.findall(body)
    if not marks:
        return None
    marker = marks[-1].upper()  # last marker = final intent in that comment
    action = "open" if marker in _OPEN else "close"
    author = (comment.get("author") or {}).get("login")
    return ClaimEvent(
        lane=extract_lane(body),
        action=action,
        marker=marker,
        created_at=comment.get("createdAt"),
        author=author,
        url=comment.get("url"),
    )


def compute_active_claims(events: list[ClaimEvent]) -> tuple[dict, list[ClaimEvent]]:
    """Reduce a chronologically-ordered event list to active claims per lane.

    Returns `(active_by_lane, unattributed)`:
      - `active_by_lane`: {lane: ClaimEvent} for lanes whose LATEST event is an
        open. Computed by walking events in order (caller sorts); later events
        overwrite earlier ones, and a close removes the lane.
      - `unattributed`: events whose body carried a marker but no lane token --
        the tool surfaces them for manual verification, it does not guess.
    """
    state: dict[str, ClaimEvent] = {}
    unattributed: list[ClaimEvent] = []
    for ev in events:
        if ev.lane is None:
            unattributed.append(ev)
            continue
        if ev.is_open:
            state[ev.lane] = ev
        else:
            state.pop(ev.lane, None)
    return state, unattributed


# --- gh plumbing -------------------------------------------------------------

def _gh_issue_comments(issue: str) -> dict:
    """Fetch issue metadata + comments as JSON via `gh`. Raises on failure."""
    proc = subprocess.run(
        [
            "gh", "issue", "view", str(issue),
            "--json", "number,title,comments",
        ],
        capture_output=True, text=True, shell=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh issue view {issue} failed (exit {proc.returncode}): "
            f"{proc.stderr.strip()}"
        )
    return json.loads(proc.stdout)


def _sort_events(payload: dict) -> list[ClaimEvent]:
    """Parse + chronologically sort claim events from an `gh issue view` payload."""
    events = [
        ev for c in payload.get("comments", [])
        if (ev := parse_claim_event(c)) is not None
    ]
    # Server createdAt, ISO 8601 UTC -> lexicographic order == chronological.
    events.sort(key=lambda e: e.created_at or "")
    return events


def _post_comment(issue: str, body: str) -> None:
    """Post an issue comment via `gh issue comment --body-file`.

    A body file (not --body) avoids shell-escaping the marker / em-dash / quotes
    and keeps the posted text byte-exact. Written under the OS temp dir, not the
    worktree, so it never leaks into a commit (cf L677-L4 body-file discipline).
    """
    with tempfile.NamedTemporaryFile(
        "w", suffix=".md", delete=False, encoding="utf-8"
    ) as fh:
        fh.write(body)
        path = fh.name
    proc = subprocess.run(
        ["gh", "issue", "comment", str(issue), "--body-file", path],
        capture_output=True, text=True, shell=False,
    )
    Path(path).unlink(missing_ok=True)
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh issue comment {issue} failed (exit {proc.returncode}): "
            f"{proc.stderr.strip()}"
        )


# --- formatted output --------------------------------------------------------

_CLAIM_BODY_TMPL = (
    "[CLAIMED] lane {lane} -- {intention}\n\n"
    "(check_lane_claim #9774 -- server-stamped UTC; body timestamps are NOT "
    "authoritative. Release with `[RELEASED]` when your PR lands.)\n"
)
_RELEASE_BODY_TMPL = (
    "[RELEASED] lane {lane} -- {note}\n"
)


def _fmt_utc(iso: str | None) -> str:
    return (iso or "?").replace("T", " ").replace("Z", " UTC")


# --- modes -------------------------------------------------------------------

def _run_check(payload: dict, my_lane: str) -> int:
    events = _sort_events(payload)
    active, unattributed = compute_active_claims(events)
    others = {ln: ev for ln, ev in active.items() if ln != my_lane}
    mine = active.get(my_lane)

    summary = {
        "issue": payload.get("number"),
        "title": payload.get("title"),
        "my_lane": my_lane,
        "my_active_claim": bool(mine),
        "blocking_lanes": sorted(others),
        "active_claims": {
            ln: {
                "claimed_at": ev.created_at,
                "by": ev.author,
                "marker": ev.marker,
                "url": ev.url,
            }
            for ln, ev in sorted(active.items())
        },
        "unattributed_markers": len(unattributed),
        "blocked": bool(others),
    }
    print(json.dumps(summary, ensure_ascii=False, indent=2))

    # Human verdict after the JSON.
    if others:
        who = ", ".join(
            f"{ln} (@{_fmt_active(ev)})" for ln, ev in sorted(others.items())
        )
        print(
            f"\nBLOCKED: another lane holds an active claim on "
            f"#{payload.get('number')}: {who}.\n"
            f"Do not start -- pick another grain, or wait for release.",
            file=sys.stderr,
        )
        return 1
    note = " (resuming your own active claim)" if mine else ""
    print(f"\nCLEAR: no other lane claims #{payload.get('number')}{note}.")
    return 0


def _fmt_active(ev: ClaimEvent) -> str:
    return f"{ev.author or '?'}, {_fmt_utc(ev.created_at)}"


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description=(
            "Lane-claim guard (#9774): check/post [CLAIMED] on an issue before "
            "editing. Defaut-2-safe: server UTC timestamps only."
        )
    )
    p.add_argument("issue", help="issue number (or URL)")
    p.add_argument("--lane", required=True,
                   help="your lane, e.g. myia-po-2024:CoursIA")
    p.add_argument("--from-json", metavar="FILE",
                   help="read `gh issue view` JSON from FILE (offline/test mode)")
    act = p.add_mutually_exclusive_group()
    act.add_argument("--claim", metavar="INTENTION",
                     help="post a [CLAIMED] comment for your lane")
    act.add_argument("--release", nargs="?", const="", default=None,
                     metavar="NOTE", help="post a [RELEASED] comment")
    args = p.parse_args(argv)

    # Posting modes: short-circuit before any read.
    if args.claim is not None:
        body = _CLAIM_BODY_TMPL.format(lane=args.lane, intention=args.claim)
        try:
            _post_comment(args.issue, body)
        except RuntimeError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 2
        print(f"posted [CLAIMED] lane {args.lane} on #{args.issue}")
        return 0
    if args.release is not None:
        note = args.release or "released"
        body = _RELEASE_BODY_TMPL.format(lane=args.lane, note=note)
        try:
            _post_comment(args.issue, body)
        except RuntimeError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 2
        print(f"posted [RELEASED] lane {args.lane} on #{args.issue}")
        return 0

    # Check mode.
    try:
        if args.from_json:
            payload = json.loads(Path(args.from_json).read_text(encoding="utf-8"))
        else:
            payload = _gh_issue_comments(args.issue)
    except (RuntimeError, json.JSONDecodeError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return _run_check(payload, args.lane)


if __name__ == "__main__":
    sys.exit(main())
