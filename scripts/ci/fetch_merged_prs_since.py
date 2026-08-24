#!/usr/bin/env python3
r"""fetch_merged_prs_since.py -- fetch merged PRs merged since a date (paginated).

## Why

The G-VAR-3 adjacency guard resolves a lane's REAL predecessor from the merged
sequence (`variation_adjacency_guard.py --merged-prs-file`). The workflow used
to fetch it with `gh pr list --state merged --limit 100`, which GitHub orders
by CREATION date: with a fleet merging ~100 PRs/day, `--limit 100` covers
roughly ONE DAY of creations, so a low-activity lane's grain merged a few days
ago falls out of the batch and the guard silently falls back to the frozen
`prev:` field -- the exact post-#12095 regression (#12636).

Fetching with the `merged:>=` qualifier (merge-time, not creation) and
paginating the window guarantees any lane that merged since the cutoff appears,
whatever its creation date. The guard still sorts by mergedAt itself. A fetch
failure emits nothing and exits nonzero, so the caller's `|| rm -f` degrades to
the declared `prev:` (never a crash, never a silent pass).

## Output

A single JSON array on stdout:

    [{"number": 123, "body": "...", "mergedAt": "2026-08-24T09:32:39Z"}, ...]

## Usage

    python3 scripts/ci/fetch_merged_prs_since.py --days 21 > /tmp/merged_prs.json
    python3 scripts/ci/fetch_merged_prs_since.py --since 2026-08-01 > /tmp/merged_prs.json
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import date, timedelta

# Default page cap: 40 pages x 100 = 4000 PRs, ~40 days at the observed ~100
# merges/day. A lane merged within the window is captured; the guard sorts by
# mergedAt. Cap is a safety net, not the normal path.
MAX_PAGES = 40
PAGE_SIZE = 100

DEFAULT_DAYS = 21


def since_date(days: int) -> str:
    """Return the ISO cutoff ``today - days``."""
    return (date.today() - timedelta(days=days)).isoformat()


def run_gh(page: int, since: str) -> list[dict]:
    """One page of merged PRs: ``gh pr list --state merged --search merged:>=since``.

    Reached externally so tests can inject a fake ``gh``.
    """
    out = subprocess.run(
        [
            "gh", "pr", "list",
            "--state", "merged",
            "--search", f"merged:>={since}",
            "--limit", str(PAGE_SIZE),
            "--page", str(page),
            "--json", "number,body,mergedAt",
        ],
        capture_output=True, text=True, check=True,
    )
    return json.loads(out.stdout)


def fetch(since: str, run=run_gh, max_pages: int = MAX_PAGES) -> list[dict]:
    """Paginate the merged window ``[since, now]`` into a single PR list.

    ``run`` is dependency-injected for tests; the default shells out to ``gh``.
    Stops early on a short page (< PAGE_SIZE) or at ``max_pages``.
    """
    acc: list[dict] = []
    seen: set[int] = set()
    for page in range(1, max_pages + 1):
        batch = run(page, since)
        for pr in batch:
            n = pr.get("number")
            if n is not None and n not in seen:
                seen.add(n)
                acc.append(pr)
        if len(batch) < PAGE_SIZE:
            break
    return acc


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--days", type=int, default=None,
                   help=f"fetch PRs merged within the last N days (default {DEFAULT_DAYS})")
    p.add_argument("--since", metavar="YYYY-MM-DD", default=None,
                   help="fetch PRs merged on or after this date (overrides --days)")
    args = p.parse_args(argv)

    if args.since:
        since = args.since
    else:
        since = since_date(args.days if args.days is not None else DEFAULT_DAYS)

    try:
        prs = fetch(since)
    except (subprocess.CalledProcessError, json.JSONDecodeError, OSError) as e:
        print(f"fetch_merged_prs_since: {e}", file=sys.stderr)
        return 1

    json.dump(prs, sys.stdout, ensure_ascii=False)
    print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
