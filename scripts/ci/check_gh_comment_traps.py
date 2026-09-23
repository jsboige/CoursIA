#!/usr/bin/env python3
r"""Detect posted bodies that never reached the API as intended -- the posting traps.

Two members of the same family (#16866, #17326), both silent, both caught by
the emission-side rule `.claude/rules/gh-posting-hygiene.md`; this organ is the
measurable half.

Member 1 -- literal `@<path>` (#16866): `gh api -f body=@f.md` posts the
LITERAL string `@f.md`. The `@` expansion only works on typed fields
(`-F body=@f.md`), so the comment lands with a ~30-50 char body that is a path,
with zero error on the way. Three occurrences were measured on two seats and
two OS (#16855 c.5740907673 on a Linux container, #16766 and #16723 on Windows,
14 s apart). On PR bodies the sibling form is `gh pr create -b @f.md`.

Member 2 -- payload JSON as body (#17326, instance #17270): when the WHOLE
payload JSON is passed as the body, GitHub publishes a long, plausible-looking
JSON object whose `body` value holds the real body, escaped. The length guard
of rule 2 is structurally blind to it (the published body is LONG); the signal
is structural: the body parses as a JSON object carrying a string `body` key.
Measured cost: the tag_required organ went red naming a discipline breach while
the lane's source body was perfectly correct.

Coverage: recent issue comments (the endpoint covers issue AND PR comments,
since a PR is an issue) for both members, plus the bodies of OPEN PRs (member 2
was measured on a PR body, which the comments endpoint never sees).

Verdicts:
    TRAPPED  at least one body carries either trap signature (exit 1)
    CLEAN    no trapped body in the window (exit 0)
    UNKNOWN  network/gh failure -- infrastructure never forges a red (#14849)
             (exit 0, ::warning)

Usage:
    python scripts/ci/check_gh_comment_traps.py
    python scripts/ci/check_gh_comment_traps.py --hours 96 --json
    python scripts/ci/check_gh_comment_traps.py --repo jsboige/CoursIA
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timedelta, timezone

REPO = "jsboige/CoursIA"

# A trapped body is a single token: `@` + a path containing a separator, with
# no whitespace (a user @mention never carries a path separator, and a real
# comment body has spaces). Length floor mirrors the #16866 guard: a file body
# is never < 100 chars when it actually posted.
TRAP_RE = re.compile(r"^@[^\s]*[\\/][^\s]*$")
TRAP_MAX_LEN = 100


def classify_body(body: str) -> bool:
    """True if the body carries the `@<path>` literal-expansion trap signature."""
    stripped = (body or "").strip()
    return len(stripped) < TRAP_MAX_LEN and bool(TRAP_RE.fullmatch(stripped))


def classify_payload_body(body: str) -> str | None:
    """The inner body when the WHOLE published body is the payload JSON object.

    Returns the extracted `body` string (the real body, escaped inside its own
    envelope) so the remediation can PATCH it back verbatim, or None when the
    body is not that shape. Structural, not metric: a body that merely CONTAINS
    a JSON snippet (fenced or inline, e.g. a diagnostic quoting a payload) has
    prose around it and does not parse as a whole -- no false positive. A
    legitimate body that would be exactly `{"body": "..."}` does not exist.
    """
    stripped = (body or "").strip()
    if not stripped.startswith("{"):
        return None
    try:
        parsed = json.loads(stripped)
    except json.JSONDecodeError:
        return None
    if isinstance(parsed, dict) and isinstance(parsed.get("body"), str):
        return parsed["body"]
    return None


def fetch_comments(repo: str, since_iso: str) -> list[dict] | None:
    """Return issue comments since a timestamp, or None on infrastructure failure."""
    from urllib.parse import quote
    path = f"repos/{repo}/issues/comments?since={quote(since_iso)}&per_page=100"
    cmd = ["gh", "api", "--paginate", path]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=120,
                             encoding="utf-8", errors="replace")
    except (subprocess.TimeoutExpired, OSError):
        return None
    if out.returncode != 0:
        return None
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError:
        return None


def scan(comments: list[dict]) -> list[dict]:
    trapped = []
    for c in comments:
        body = c.get("body") or ""
        if classify_body(body):
            trapped.append({
                "id": c.get("id"),
                "url": c.get("html_url"),
                "created_at": c.get("created_at"),
                "user": (c.get("user") or {}).get("login"),
                "kind": "literal-path",
                "body": body,
            })
            continue
        inner = classify_payload_body(body)
        if inner is not None:
            first_line = inner.splitlines()[0] if inner.splitlines() else ""
            trapped.append({
                "id": c.get("id"),
                "url": c.get("html_url"),
                "created_at": c.get("created_at"),
                "user": (c.get("user") or {}).get("login"),
                "kind": "json-payload",
                "body": body,
                "inner_len": len(inner),
                "inner_first_line": first_line,
            })
    return trapped


def fetch_pr_bodies(repo: str) -> list[dict] | None:
    """Return open PRs (number, title, body, url), or None on infra failure."""
    path = f"repos/{repo}/pulls?state=open&per_page=100"
    cmd = ["gh", "api", "--paginate", path]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=120,
                             encoding="utf-8", errors="replace")
    except (subprocess.TimeoutExpired, OSError):
        return None
    if out.returncode != 0:
        return None
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError:
        return None


def scan_prs(prs: list[dict]) -> list[dict]:
    """Both trap members on PR bodies -- member 1 hits `gh pr create -b @f.md`,
    member 2 hits a PR created with the whole payload JSON as its body."""
    trapped = []
    for p in prs:
        body = p.get("body") or ""
        kind = None
        inner = None
        if classify_body(body):
            kind = "literal-path"
        else:
            inner = classify_payload_body(body)
            if inner is not None:
                kind = "json-payload"
        if kind is None:
            continue
        entry = {
            "number": p.get("number"),
            "url": p.get("html_url"),
            "title": p.get("title"),
            "kind": kind,
            "body": body,
        }
        if inner is not None:
            lines = inner.splitlines()
            entry["inner_len"] = len(inner)
            entry["inner_first_line"] = lines[0] if lines else ""
        trapped.append(entry)
    return trapped


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--hours", type=int, default=48,
                    help="scan window in hours (default 48)")
    ap.add_argument("--repo", default=REPO)
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    args = ap.parse_args()

    since = (datetime.now(timezone.utc) - timedelta(hours=args.hours)).isoformat()
    comments = fetch_comments(args.repo, since)
    prs = fetch_pr_bodies(args.repo)
    if comments is None and prs is None:
        print("::warning ::gh api unreachable on both sources -- verdict UNKNOWN (never a red)")
        if args.json:
            print(json.dumps({"verdict": "UNKNOWN", "trapped": [], "trapped_prs": []}))
        return 0
    if comments is None or prs is None:
        # One source unreachable: scan the healthy half, warn on the other --
        # infra failure never forges a red, but never silences a healthy half.
        print("::warning ::gh api unreachable on one source -- scanning the other")

    trapped = scan(comments or [])
    trapped_prs = scan_prs(prs or [])
    any_trapped = bool(trapped or trapped_prs)
    fix_comment = (
        "  fix: gh api repos/{repo}/issues/comments/<id> -X PATCH "
        "-F body=@<real-file.md>".format(repo=args.repo)
    )
    fix_pr = "  fix: extract the inner body value, then gh pr edit <N> --body-file <real-file.md>"
    if args.json:
        print(json.dumps({
            "verdict": "TRAPPED" if any_trapped else "CLEAN",
            "scanned": len(comments or []),
            "scanned_prs": len(prs or []),
            "window_hours": args.hours,
            "trapped": trapped,
            "trapped_prs": trapped_prs,
        }, indent=2))
    else:
        print(f"scanned {len(comments or [])} comments over the last {args.hours}h"
              f" and {len(prs or [])} open PR bodies")
        for t in trapped:
            print(f"TRAPPED c.{t['id']} by {t['user']} at {t['created_at']} "
                  f"[{t['kind']}]: {t['body'][:80]!r}")
            print(f"  {t['url']}")
            print(fix_comment if t["kind"] == "literal-path" else fix_pr)
        for t in trapped_prs:
            print(f"TRAPPED PR #{t['number']} [{t['kind']}]: {t['title']}")
            print(f"  {t['url']}")
            if t["kind"] == "json-payload":
                print(f"  inner body first line: {t['inner_first_line']!r} ({t['inner_len']} chars)")
            print(fix_pr)
        if not any_trapped:
            print("CLEAN -- no literal @<path> body and no payload-JSON body in the window")

    return 1 if any_trapped else 0


if __name__ == "__main__":
    sys.exit(main())
