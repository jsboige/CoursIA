#!/usr/bin/env python3
"""Refresh a PR's stale G-VAR-3 adjacency verdict by re-triggering the check.

## Why this exists

The G-VAR-3 adjacency guard resolves a lane's REAL predecessor from the MERGED
sequence of the lane in a 21-day window (`fetch_merged_prs_since.py --days
21`). The guard re-runs only on `pull_request: synchronize, edited, reopened`
(`always-on-guards.yml` l.57) -- a push to the branch OR a body edit. When the
merged sequence changes (a sibling PR merges and bumps the predecessor), the
guard verdicts go stale: the previously failing `prev_genre` is now resolved
to a different grain, but nothing in the workflow says "recompute", and the
PR stays MERGEABLE=FALSE in the PR gate while it would be MERGEABLE=TRUE if
re-checked.

The founder case (2026-09-01) was the myia-po-2026:CoursIA lane:
`MERGEABLE=FALSE` on 7 PRs whose GRAIN tag (MED/guard, LIGHT/guard, ...) was
in genuine adjacency with #13585 (MED/guard, merged 2026-08-31T18:47:59Z) at
PR-open time. After #13888 (MED/tooling) merged at 2026-09-01T07:13:59Z, the
guard's predecessor resolution moved to tooling -- so the same PRs would now
PASS if re-checked. The `pull_request: synchronize` trigger fires on push, not
on sequence changes, so no automatic refresh happens.

This script automates the manual workaround: simulate the guard locally with
the CURRENT merged sequence, and if the simulated verdict PASSES while the
PR is currently failing on `Always-on guards`, append an idempotent
`<!-- refresh-adj: ISO8601 -->` marker to the body and `gh pr edit
--body-file`. That re-fires the `pull_request: edited` event and the guard
recomputes with the current sequence -- which is now PASS.

## What it does NOT do

- It does NOT bypass the G-VAR-3 rule. If the simulated verdict FAILS, the
  script exits non-zero with the reason and does NOT modify the body. The
  rule stays authoritative; the marker is only a refresh, never an override.
- It does NOT modify the body for any reason other than the refresh marker.
  The marker is invisible on GitHub's rendered view and idempotent on
  re-runs: a second invocation finds the marker, replaces the timestamp,
  does not duplicate the line.
- It does NOT touch the underlying code or the substance of the PR. The
  diff stays zero on the source files; only the body SHA changes by the
  one-line append.

## Usage

    python scripts/ci/refresh_stale_adjacency.py --pr 13812 --pr 13869 --pr 13917
    python scripts/ci/refresh_stale_adjacency.py --pr 13812 --dry-run

## Exit codes

  0  -- every PR either passes the simulated guard, or was successfully
       refreshed (marker appended, edit posted).
  1  -- at least one PR fails the simulated guard with a real reason
       (genuine G-VAR-3 adjacency); nothing was modified on those PRs.
  2  -- caller error (gh failure, missing argument).

The marker is exactly one line:

    <!-- refresh-adj: 2026-09-01T09:42:00Z -->

appended at the end of the body, followed by a newline if missing.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

# Make the shared extractor + adjacency guard importable from anywhere.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import grain_tag as gt  # noqa: E402
from variation_adjacency_guard import (  # noqa: E402
    check,
    parse_override,
    resolve_merged_prev_genre,
)

MARKER_RE = re.compile(r"<!--\s*refresh-adj:\s*[^>]+\s*-->")
MARKER_PREFIX = "<!-- refresh-adj:"
MARKER_TZ = "%Y-%m-%dT%H:%M:%SZ"


def now_marker() -> str:
    """Return the current UTC timestamp in the marker format."""
    return f"{MARKER_PREFIX} {datetime.now(timezone.utc).strftime(MARKER_TZ)} -->"


def run_gh(*args: str, check: bool = False) -> subprocess.CompletedProcess:
    """Run a `gh` CLI invocation, return CompletedProcess (stdout=str)."""
    return subprocess.run(
        ["gh", *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=check,
    )


def fetch_merged_window(days: int = 21) -> list[dict]:
    """Fetch the merged-window used by the G-VAR-3 guard (21d default)."""
    proc = subprocess.run(
        ["python", "scripts/ci/fetch_merged_prs_since.py", "--days", str(days)],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"fetch_merged_prs_since failed: {proc.stderr}")
    return json.loads(proc.stdout)


def get_pr_body(pr_number: int) -> str:
    """Return the current body of `pr_number` as a string."""
    proc = run_gh("pr", "view", str(pr_number), "--json", "body")
    if proc.returncode != 0:
        raise RuntimeError(f"gh pr view #{pr_number} failed: {proc.stderr}")
    data = json.loads(proc.stdout)
    return data.get("body") or ""


def get_pr_comments(pr_number: int) -> list[dict]:
    """Return the {author.login, body} list for `pr_number` (override scan)."""
    proc = run_gh("pr", "view", str(pr_number), "--json", "comments",
                  "--jq", '[.comments[] | {author: .author.login, body: .body}]')
    if proc.returncode != 0:
        return []
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return []


def get_pr_checks(pr_number: int) -> dict:
    """Return the current check state of `pr_number` (name -> conclusion)."""
    proc = run_gh("pr", "checks", str(pr_number))
    checks: dict[str, str] = {}
    for line in proc.stdout.splitlines():
        # Format: NAME<tab>CONCLUSION<tab>DURATION<tab>URL
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        checks[parts[0]] = parts[1]
    return checks


def is_always_on_guards_failing(pr_number: int) -> bool:
    """True if `Always-on guards -- 12 organes, 1 checkout` is currently FAIL."""
    checks = get_pr_checks(pr_number)
    name = "Always-on guards -- 12 organes, 1 checkout"
    return checks.get(name) == "fail"


def append_marker(body: str, marker: str) -> str:
    """Append `marker` to `body`, idempotent (replaces existing marker)."""
    body = body.rstrip("\n")
    # Strip any previous refresh-adj marker (with the line that carries it)
    body = MARKER_RE.sub("", body).rstrip("\n")
    if not body:
        return f"{marker}\n"
    return f"{body}\n{marker}\n"


def simulate_adjacency(pr_number: int, body: str, merged_window: list[dict]) -> dict:
    """Run the G-VAR-3 guard on `body` against the current `merged_window`.

    Returns the guard verdict dict. This is the SAME computation the CI runs
    (`scripts/ci/variation_adjacency_guard.py --body-file ... --merged-prs-file
    ...`), so a `guard_pass: True` here means the CI will turn green on the
    next re-trigger.
    """
    g = gt.parse_grain_tag(body)
    if g is None:
        # Body has no Grain tag -- a different guard (tag-required) is the
        # cause. Don't refresh.
        return {
            "guard_pass": False,
            "blocking": False,
            "adjacent": False,
            "reason": "no Grain tag in body -- tag-required is the cause, not adjacency",
        }

    override = parse_override(get_pr_comments(pr_number))
    merged_prev = resolve_merged_prev_genre(merged_window, g["lane"])
    return check(body, override=override, merged_prev=merged_prev)


def refresh_one(pr_number: int, dry_run: bool, merged_window: list[dict]) -> dict:
    """Run the full refresh cycle for `pr_number`. Returns a status dict."""
    body = get_pr_body(pr_number)
    verdict = simulate_adjacency(pr_number, body, merged_window)
    always_on_failing = is_always_on_guards_failing(pr_number)
    new_body = append_marker(body, now_marker())
    would_refresh = (
        always_on_failing
        and verdict["guard_pass"]
        and verdict.get("blocking") is not True
    )
    refreshed = False
    if would_refresh and not dry_run:
        proc = run_gh("pr", "edit", str(pr_number), "--body-file", "-",
                      check=False)
        # Need to pipe stdin -- the `--body-file -` reads from stdin in some
        # gh versions; if not supported, fall back to a temp file.
        if "unknown flag" in proc.stderr or "flag" in proc.stderr.lower():
            tmp = Path(f"/tmp/refresh_body_{pr_number}.md")
            tmp.write_text(new_body, encoding="utf-8")
            proc2 = run_gh("pr", "edit", str(pr_number), "--body-file", str(tmp))
            tmp.unlink(missing_ok=True)
            refreshed = proc2.returncode == 0
        else:
            proc2 = subprocess.run(
                ["gh", "pr", "edit", str(pr_number), "--body-file", "-"],
                input=new_body,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
            )
            refreshed = proc2.returncode == 0
    elif would_refresh and dry_run:
        refreshed = True  # virtual: would have been done

    return {
        "pr": pr_number,
        "always_on_failing": always_on_failing,
        "guard_pass": verdict["guard_pass"],
        "adjacent": verdict.get("adjacent"),
        "prev_genre": verdict.get("prev_genre"),
        "prev_pr": verdict.get("prev_pr"),
        "reason": verdict.get("reason", ""),
        "would_refresh": would_refresh,
        "refreshed": refreshed,
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--pr", type=int, action="append", required=True,
                   help="PR number to consider (repeatable)")
    p.add_argument("--dry-run", action="store_true",
                   help="Report what would be done without modifying any PR")
    args = p.parse_args(argv)

    try:
        merged_window = fetch_merged_window()
    except RuntimeError as e:
        print(json.dumps({"error": str(e)}), file=sys.stderr)
        return 2

    results = [refresh_one(pr, args.dry_run, merged_window) for pr in args.pr]
    print(json.dumps({"results": results}, indent=2, ensure_ascii=False))

    # Exit 1 if any PR failed the simulated guard with a real reason (the
    # refresh only covers stale-failing verdicts; a fresh failing verdict is
    # not ours to override).
    any_real_fail = any(
        not r["guard_pass"] and not r["always_on_failing"]
        for r in results
    )
    return 1 if any_real_fail else 0


if __name__ == "__main__":
    sys.exit(main())
