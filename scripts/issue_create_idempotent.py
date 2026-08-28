#!/usr/bin/env python3
"""Idempotence guard for `gh issue create`.

Why this exists
---------------
GitHub's REST/GraphQL `createIssue` mutation exposes **no idempotency key**.
A retry that lost its HTTP response (timeout, 502, dropped connection) will
silently produce a *second* issue with byte-identical body. Over 2026-08-23
through 2026-08-26, this produced **10 byte-identical pairs** in
`jsboige/CoursIA`, all created within 1-8 s of each other
(see issue #13208), leading to 2 confirmed double-livraisons (#13074/#13156
Lean-2, #13077/#13154 PyMC-16). The API doesn't fix this; we do.

What it does
------------
`create_issue_idempotent(title, body, label, ...)` first asks `gh issue list`
for any issue whose title matches within the last `--window-minutes` (default
10 min). If a match is found, the call is **aborted** and the existing issue
number is returned -- the caller can either accept the existing issue or
escalate. Otherwise, `gh issue create` is invoked as usual.

Three reasons this is the right shape:
1. **Title collision in the window is the actual signal.** Two issues
   created with the same title in 10 minutes from the same caller are
   overwhelmingly retries. (Verified in #13208: delta median 2 s, max 8 s.)
2. **The window must be tunable.** 10 min catches retries but tolerates
   legitimate re-creations (e.g. re-opening an old closed issue under a
   fresh title). The default is conservative; CI/cron callers can tighten.
3. **Cross-callers still collide.** Two agents running concurrently would
   each miss the other's pre-check. We accept this race for now: GitHub's
   rate-limiter will surface the duplicate within seconds, and the
   retroactive scanner `detect_duplicate_issues.py` is the backstop.

Out of scope:
- Body byte-equality check. Title is the stable key in the issue list,
  and identical bodies are usually (not always) retries of the same title.
  Body-equality would block legitimate follow-ups on different topics.
- Closing the older of two duplicates. The retroactive scanner reports
  them; an explicit human/coord closes. Auto-closing a "less complete"
  duplicate requires reading diffs we cannot afford on every create.

Usage
-----
Replace existing `subprocess.run(["gh", "issue", "create", ...])` calls with::

    from scripts.issue_create_idempotent import create_issue_idempotent

    n, existing = create_issue_idempotent(
        title=..., body=..., label=...,
        window_minutes=10,
        dry_run=False,
    )
    if existing:
        # An issue with this title exists; n is its number.
        # Caller decides: skip / link / comment.
        ...
    else:
        # Freshly created, n is the new issue number.

CLI shim is also exposed::

    python scripts/issue_create_idempotent.py --check-only --title "foo"
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timedelta, timezone


def _gh_issue_list_by_title(
    title: str,
    *,
    limit: int = 10,
) -> list[dict]:
    """Return issues whose title equals `title` exactly (case-sensitive).

    GitHub's `gh issue list --search "<title> in:title"` is fuzzy by default;
    we want exact match on title to avoid false positives (e.g. "fix: foo"
    matching "fix: foo (retry)"). We use `--state all` so closed duplicates
    surface too -- the retroactive scanner consumes those.
    """
    proc = subprocess.run(
        [
            "gh", "issue", "list",
            "--search", f"{title} in:title",
            "--state", "all",
            "--limit", str(limit),
            "--json", "number,title,createdAt,state",
        ],
        capture_output=True, text=True, timeout=30,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"`gh issue list --search` failed: {proc.stderr.strip()}"
        )
    rows = json.loads(proc.stdout)
    # Strict equality -- strip surrounding whitespace that gh may echo.
    needle = title.strip()
    return [r for r in rows if (r.get("title") or "").strip() == needle]


def find_recent_duplicate(
    title: str,
    *,
    window_minutes: int = 10,
    now: datetime | None = None,
) -> dict | None:
    """Return the most recent issue with `title` created within window.

    `now` is injectable for unit tests. None means "use UTC now".
    Returns the dict (number/title/createdAt/state) or None.
    """
    now = now or datetime.now(timezone.utc)
    rows = _gh_issue_list_by_title(title)
    if not rows:
        return None
    threshold = now - timedelta(minutes=window_minutes)
    candidates = []
    for r in rows:
        # gh returns ISO 8601 with 'Z' suffix; fromisoformat needs offset.
        ts = r["createdAt"].replace("Z", "+00:00")
        created = datetime.fromisoformat(ts)
        if created >= threshold:
            candidates.append((created, r))
    if not candidates:
        return None
    # Return the most recent.
    candidates.sort(key=lambda x: x[0], reverse=True)
    return candidates[0][1]


def create_issue_idempotent(
    title: str,
    body: str,
    label: str | None = None,
    *,
    window_minutes: int = 10,
    dry_run: bool = False,
    now: datetime | None = None,
) -> tuple[int | None, dict | None]:
    """Create an issue, unless one with the same title exists in window.

    Returns `(new_number, existing)`:
      - `new_number`: int if a new issue was created, None otherwise.
      - `existing`:   dict of the existing issue (number/title/createdAt/state)
                      if one was found in the window; None otherwise.

    Exactly one of the two is non-None on success. If both are None, the
    caller hit a gh error (raised via RuntimeError by `_gh_issue_list_by_title`).
    """
    existing = find_recent_duplicate(
        title, window_minutes=window_minutes, now=now,
    )
    if existing is not None:
        return (None, existing)

    if dry_run:
        return (None, None)  # caller can detect: dry-run with no dup

    args = ["gh", "issue", "create", "--title", title]
    if body:
        args += ["--body", body]
    if label:
        args += ["--label", label]
    proc = subprocess.run(
        args, capture_output=True, text=True, timeout=60,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"`gh issue create` failed: {proc.stderr.strip() or proc.stdout.strip()}"
        )
    out = proc.stdout.strip()
    # gh prints e.g. https://github.com/owner/repo/issues/123
    import re
    m = re.search(r"/issues/(\d+)$", out)
    if not m:
        raise RuntimeError(
            f"gh issue create: cannot parse issue number from {out!r}"
        )
    return (int(m.group(1)), None)


def _cli(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Idempotence guard for `gh issue create`.",
    )
    ap.add_argument("--check-only", action="store_true",
                    help="only check for an existing duplicate; do not create")
    ap.add_argument("--dry-run", action="store_true",
                    help="act as if creating, but skip the actual `gh issue create`")
    ap.add_argument("--title", required=True)
    ap.add_argument("--body", default="")
    ap.add_argument("--label", default=None)
    ap.add_argument("--window-minutes", type=int, default=10)
    args = ap.parse_args(argv)

    if args.check_only:
        existing = find_recent_duplicate(args.title,
                                         window_minutes=args.window_minutes)
        if existing is None:
            print("no-recent-duplicate")
            return 0
        print(f"existing: {existing['number']} "
              f"({existing['state']}, {existing['createdAt']})")
        return 1

    new_number, existing = create_issue_idempotent(
        title=args.title, body=args.body, label=args.label,
        window_minutes=args.window_minutes, dry_run=args.dry_run,
    )
    if existing is not None:
        print(f"SKIP existing={existing['number']} "
              f"createdAt={existing['createdAt']}", file=sys.stderr)
        return 1
    if args.dry_run:
        print("DRY-RUN (no recent duplicate, no issue created)")
        return 0
    print(new_number)
    return 0


if __name__ == "__main__":
    sys.exit(_cli())
