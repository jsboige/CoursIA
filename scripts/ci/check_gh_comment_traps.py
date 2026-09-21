#!/usr/bin/env python3
r"""Detect comments whose body is a literal file path -- the `gh -f body=@file` trap.

Context (#16866): `gh api -f body=@f.md` posts the LITERAL string `@f.md`. The
`@` expansion only works on typed fields (`-F body=@f.md`), so the comment
lands with a ~30-50 char body that is a path, with zero error on the way. Three
occurrences were measured on two seats and two OS (#16855 c.5740907673 on a
Linux container, #16766 and #16723 on Windows, 14 s apart) -- the class hits
any lane that posts a file body through `-f`.

The behavioral rule that prevents the trap lives in
`.claude/rules/gh-posting-hygiene.md`. This organ is the measurable half: it
scans recent issue comments (the endpoint covers issue AND PR comments, since a
PR is an issue) and flags bodies that carry the trap signature, so the
escalation criterion from #16866 ("3rd occurrence") is measured, not felt.

Verdicts:
    TRAPPED  at least one comment body is a literal `@<path>` token (exit 1)
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


def fetch_comments(repo: str, since_iso: str) -> list[dict] | None:
    """Return issue comments since a timestamp, or None on infrastructure failure."""
    from urllib.parse import quote
    path = f"repos/{repo}/issues/comments?since={quote(since_iso)}&per_page=100"
    cmd = ["gh", "api", "--paginate", path]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
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
                "body": body,
            })
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
    if comments is None:
        print("::warning ::gh api unreachable -- verdict UNKNOWN (never a red)")
        if args.json:
            print(json.dumps({"verdict": "UNKNOWN", "trapped": []}))
        return 0

    trapped = scan(comments)
    remediation = (
        "  fix: gh api repos/{repo}/issues/comments/<id> -X PATCH "
        "-F body=@<real-file.md>".format(repo=args.repo)
    )
    if args.json:
        print(json.dumps({
            "verdict": "TRAPPED" if trapped else "CLEAN",
            "scanned": len(comments),
            "window_hours": args.hours,
            "trapped": trapped,
        }, indent=2))
    else:
        print(f"scanned {len(comments)} comments over the last {args.hours}h")
        for t in trapped:
            print(f"TRAPPED c.{t['id']} by {t['user']} at {t['created_at']}: {t['body']!r}")
            print(f"  {t['url']}")
            print(remediation)
        if not trapped:
            print("CLEAN -- no literal @<path> body in the window")

    return 1 if trapped else 0


if __name__ == "__main__":
    sys.exit(main())
