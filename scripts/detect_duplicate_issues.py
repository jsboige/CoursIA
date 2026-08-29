#!/usr/bin/env python3
"""Retroactive scanner for duplicate issues.

Why this exists
---------------
Issue #13208 documents **10 byte-identical pairs** of issues created in
`jsboige/CoursIA` between 2026-08-23 and 2026-08-26, all within 1-8 seconds
of each other, with byte-identical bodies. The root cause was the lack of
an idempotency key on `gh issue create` (now patched in
`issue_create_idempotent.py`); the *retroactive* clean-up lives here.

What it does
------------
Pulls the recent issue list (`gh issue list --limit N --state all`) and
groups issues by **exact title match**. Within each group, any pair whose
`createdAt` is within `--window-seconds` (default 60 s) is reported as a
"burst pair". The output is JSON-stable (machine-readable) plus a
human summary on stderr.

A **positive control** is mandatory: the well-known pair `#13050` / `#13051`
(2026-08-26T01:39:14Z, delta 1 s, byte-identical body, source
`jsboigeEpita`) **must** appear in any healthy run, otherwise the scanner
is broken and we'd be silencing the very signal it was built for. See
`--self-test` and the unit tests in
`scripts/tests/test_detect_duplicate_issues.py`.

What it does NOT do
-------------------
- It does NOT close duplicates. Closing is a human/coord decision because
  each pair needs to be triaged (which side has the live PR? which has the
  richer history?). This script only **reports**.
- It does NOT compare bodies. Title equality is the strong signal; bodies
  add noise (Markdown reformatting, label edits between creations).

Usage
-----
::

    # Scan the last 600 issues (default), 60 s window (default):
    python scripts/detect_duplicate_issues.py

    # Tighten the window (10 s) and the lookback (2000 issues):
    python scripts/detect_duplicate_issues.py --window-seconds 10 --limit 2000

    # Self-test (must include the #13050/#13051 pair, otherwise exit 2):
    python scripts/detect_duplicate_issues.py --self-test

    # The live self-test is wired daily (network trigger) by
    # .github/workflows/detect-dup-selftest.yml -- DETECT_DUP_NETWORK gates
    # only the pytest live test, so offline `python -m pytest` still passes
    # (#13331).

Exit codes:
  0 -- no duplicates found, OR scan completed cleanly under --self-test.
  1 -- duplicates found (non-zero pair count).
  2 -- self-test FAILED (positive control missing -- scanner is broken).

CLI flags
---------
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import defaultdict
from dataclasses import asdict, dataclass, field
from datetime import datetime
from itertools import combinations
from typing import Iterable


# Positive control: a known duplicate pair from #13208. The scanner MUST
# find it under --self-test, otherwise the output of the scanner is
# suspect. If the pair is closed in the future, update this list --
# the test will then be moot and should be retired.
KNOWN_POSITIVE_CONTROLS: list[tuple[int, int]] = [
    (13050, 13051),  # 2026-08-26T01:39:14Z, delta 1 s, body byte-identical
]


@dataclass(frozen=True)
class IssueRow:
    """Minimal issue record we read from `gh issue list`."""
    number: int
    title: str
    createdAt: str
    state: str

    @classmethod
    def from_gh_dict(cls, d: dict) -> "IssueRow":
        return cls(
            number=int(d["number"]),
            title=(d.get("title") or "").strip(),
            createdAt=d["createdAt"],
            state=d.get("state", "OPEN"),
        )


@dataclass(frozen=True)
class BurstPair:
    """A pair of issues with identical title, created within window."""
    title: str
    a_number: int
    a_createdAt: str
    b_number: int
    b_createdAt: str
    delta_seconds: float
    a_state: str
    b_state: str

    def as_dict(self) -> dict:
        return asdict(self)


@dataclass
class ScanResult:
    """Aggregate output of one scan run."""
    total_issues_scanned: int = 0
    distinct_titles: int = 0
    pairs: list[BurstPair] = field(default_factory=list)
    positive_controls_found: list[tuple[int, int]] = field(default_factory=list)
    positive_controls_missing: list[tuple[int, int]] = field(default_factory=list)

    @property
    def n_pairs(self) -> int:
        return len(self.pairs)

    def as_dict(self) -> dict:
        return {
            "total_issues_scanned": self.total_issues_scanned,
            "distinct_titles": self.distinct_titles,
            "n_pairs": self.n_pairs,
            "pairs": [p.as_dict() for p in self.pairs],
            "positive_controls_found": [
                list(t) for t in self.positive_controls_found
            ],
            "positive_controls_missing": [
                list(t) for t in self.positive_controls_missing
            ],
        }


def _gh_issue_list(limit: int, state: str = "all") -> list[dict]:
    """Fetch issues via gh CLI. state='all' includes closed."""
    proc = subprocess.run(
        [
            "gh", "issue", "list",
            "--limit", str(limit),
            "--state", state,
            "--json", "number,title,createdAt,state",
        ],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        timeout=120,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"`gh issue list` failed: {proc.stderr.strip()}"
        )
    return json.loads(proc.stdout)


def _parse_iso(ts: str) -> datetime:
    """Parse ISO 8601 returned by gh (Z-suffix) into aware datetime."""
    return datetime.fromisoformat(ts.replace("Z", "+00:00"))


def detect_burst_pairs(
    issues: Iterable[IssueRow],
    *,
    window_seconds: int = 60,
    known_positive_controls: Iterable[tuple[int, int]] = KNOWN_POSITIVE_CONTROLS,
) -> ScanResult:
    """Group issues by title; report any intra-title pair in window.

    `issues` is consumed once. `window_seconds` is the maximum allowed delta
    between the two issues' `createdAt` for them to count as a burst pair.
    Pairs are emitted in order of (delta ascending, lowest-number ascending)
    so the most-tightly-bunched pairs surface first.

    Positive controls (passed in `known_positive_controls`) are matched
    by **either side** of the pair appearing in the controls.
    """
    result = ScanResult()
    rows = list(issues)
    result.total_issues_scanned = len(rows)

    by_title: dict[str, list[IssueRow]] = defaultdict(list)
    for r in rows:
        if r.title:
            by_title[r.title].append(r)
    result.distinct_titles = len(by_title)

    raw_pairs: list[BurstPair] = []
    seen_pairs: set[tuple[int, int]] = set()
    for title, group in by_title.items():
        if len(group) < 2:
            continue
        group_sorted = sorted(group, key=lambda r: _parse_iso(r.createdAt))
        for a, b in combinations(group_sorted, 2):
            da = _parse_iso(a.createdAt)
            db = _parse_iso(b.createdAt)
            delta = (db - da).total_seconds()
            if 0 <= delta <= window_seconds:
                pair_key = (a.number, b.number)
                if pair_key in seen_pairs:
                    continue
                seen_pairs.add(pair_key)
                raw_pairs.append(BurstPair(
                    title=title,
                    a_number=a.number,
                    a_createdAt=a.createdAt,
                    b_number=b.number,
                    b_createdAt=b.createdAt,
                    delta_seconds=delta,
                    a_state=a.state,
                    b_state=b.state,
                ))

    raw_pairs.sort(key=lambda p: (p.delta_seconds, p.a_number))
    result.pairs = raw_pairs

    pair_numbers = {(p.a_number, p.b_number) for p in raw_pairs}
    for ctrl in known_positive_controls:
        a, b = ctrl
        # Accept either ordering.
        if (a, b) in pair_numbers or (b, a) in pair_numbers:
            result.positive_controls_found.append(ctrl)
        else:
            result.positive_controls_missing.append(ctrl)

    return result


def _format_human_summary(result: ScanResult) -> str:
    lines = []
    lines.append(
        f"scanned={result.total_issues_scanned} "
        f"distinct_titles={result.distinct_titles} "
        f"pairs={result.n_pairs}"
    )
    for p in result.pairs[:20]:
        lines.append(
            f"  pair #{p.a_number}/{p.b_number} "
            f"delta={p.delta_seconds:.1f}s "
            f"states={p.a_state}/{p.b_state} "
            f"title={p.title[:80]!r}"
        )
    if result.n_pairs > 20:
        lines.append(f"  ... and {result.n_pairs - 20} more (see JSON)")
    if result.positive_controls_missing:
        lines.append(
            "  WARNING: positive controls MISSING -- "
            + ", ".join(f"#{a}/{b}" for a, b in result.positive_controls_missing)
        )
    return "\n".join(lines)


def _cli(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description=(
            "Scan recent issues for byte-title bursts within a time window. "
            "Reports duplicates; does NOT close them."
        ),
    )
    ap.add_argument("--limit", type=int, default=600,
                    help="issues to scan via `gh issue list` (default 600)")
    ap.add_argument("--window-seconds", type=int, default=60,
                    help="intra-title delta threshold (default 60)")
    ap.add_argument("--state", default="all",
                    choices=["open", "closed", "all"],
                    help="issues to scan (default 'all' -- closed included)")
    ap.add_argument("--self-test", action="store_true",
                    help="require the #13050/#13051 pair to be found; "
                         "exit 2 if not. Use in CI.")
    ap.add_argument("--json", action="store_true",
                    help="emit machine-readable JSON on stdout (always)")
    args = ap.parse_args(argv)

    try:
        rows_raw = _gh_issue_list(args.limit, state=args.state)
    except RuntimeError as e:
        print(str(e), file=sys.stderr)
        return 1
    rows = [IssueRow.from_gh_dict(d) for d in rows_raw]
    result = detect_burst_pairs(rows, window_seconds=args.window_seconds)

    print(json.dumps(result.as_dict(), ensure_ascii=False, indent=2))
    print(_format_human_summary(result), file=sys.stderr)

    if args.self_test and result.positive_controls_missing:
        return 2
    return 1 if result.n_pairs > 0 else 0


if __name__ == "__main__":
    sys.exit(_cli())
