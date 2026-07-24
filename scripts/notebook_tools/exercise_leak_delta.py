#!/usr/bin/env python3
"""Exercise-leak HIGH delta guard — compare two ``detect_solution_leaks.py``
runs and fail if the PR introduces *new* HIGH-severity solution leaks.

Why a delta (not an absolute ``--check`` fail)
---------------------------------------------
``detect_solution_leaks.py --scan-all --check`` exits 1 on ANY HIGH. The repo
inherits 48 HIGH + 27 MEDIUM notebooks (cf the detector's audit-on-origin
baseline, exercise-leak-ci starter PR). An absolute gate would freeze the
cluster for any PR touching an inherited-leak notebook — the opposite of the
intended durable guard.

The durable, non-blocking transposition is a **delta guard**: count HIGH
occurrences on BASE (pull-request base ref) and HEAD (pull-request head), fail
only when HEAD > BASE, i.e. when the PR *introduces* new leaks. Existing leaks
are tolerated; regressions are not. Mirrors the ``pip-leak-guard`` pattern
that already covers ``!pip install`` regressions (#6314).

The detector does not yet expose a ``--json`` mode, so this guard parses the
line ``Results: X HIGH (leaks), Y MEDIUM (duplicates), Z errors`` that the
detector always prints. If the detector's output format ever drifts, this guard
will need to be updated.

Usage (CI)
----------
``exercise-leak-ci.yml`` produces the two ``--scan-all`` outputs and feeds
them to this guard. Standalone (local): run the detector twice on the base ref
and the head, capture stdout, redirect into the two text files passed here.

Exit codes: 0 = no new HIGH leaks ; 1 = HEAD introduces HIGH delta > 0 ;
2 = input files unreadable or unparsable.

See #8053 (the issue), #1214/#1336/#1339/#1344 (leak-scanner lineage),
``exercise-example-labeling.md`` (content-based labeling rule), and the
mirroring ``pip_leak_delta.py`` (the ``!pip install`` analogue).
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# Matches the detector's summary line exactly: "Results: 48 HIGH (leaks),
# 27 MEDIUM (duplicates), 0 errors". MULTILINE-tolerant, anchored on "Results:".
RESULTS_LINE_RE = re.compile(
    r"Results:\s*(?P<high>\d+)\s*HIGH\s*\(leaks\)\s*,\s*"
    r"(?P<medium>\d+)\s*MEDIUM\s*\(duplicates\)\s*,\s*"
    r"(?P<errors>\d+)\s*errors"
)


def _first_results_line(text: str) -> str | None:
    """Return the matching ``Results:`` line from the detector stdout, or None."""
    for line in text.splitlines():
        if line.startswith("Results:"):
            return line
    return None


def parse_counts(stdout_text: str) -> tuple[int, int, int]:
    """Parse (high, medium, errors) from a detector stdout capture."""
    line = _first_results_line(stdout_text)
    if line is None:
        raise ValueError(
            "could not find detector `Results:` line in input "
            "(the detector output format may have drifted)"
        )
    m = RESULTS_LINE_RE.search(line)
    if not m:
        raise ValueError(f"`Results:` line does not match expected schema: {line!r}")
    return int(m["high"]), int(m["medium"]), int(m["errors"])


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Fail if HEAD introduces new HIGH exercise-leak regressions vs BASE."
    )
    parser.add_argument("base", help="BASE stdout (redirect of detect_solution_leaks.py --scan-all)")
    parser.add_argument("head", help="HEAD stdout (redirect of detect_solution_leaks.py --scan-all)")
    args = parser.parse_args(argv)

    try:
        base_text = Path(args.base).read_text(encoding="utf-8", errors="replace")
        head_text = Path(args.head).read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        print(f"error: cannot read input files: {exc}", file=sys.stderr)
        return 2

    try:
        base_h, base_m, base_e = parse_counts(base_text)
        head_h, head_m, head_e = parse_counts(head_text)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    delta_h = head_h - base_h
    delta_m = head_m - base_m
    delta_e = head_e - base_e

    print(
        f"exercise-leak guard: BASE HIGH={base_h} MEDIUM={base_m} ERROR={base_e} | "
        f"HEAD HIGH={head_h} MEDIUM={head_m} ERROR={head_e} | "
        f"Δhigh={delta_h:+d} Δmedium={delta_m:+d} Δerror={delta_e:+d}"
    )

    if delta_h <= 0:
        print(
            "OK: no new HIGH solution leaks introduced "
            f"(inherited {head_h} tolerated, drained one-PR-per-notebook per #8053 acceptance)."
        )
        return 0

    print(
        f"FAIL: PR introduces {delta_h} new HIGH-severity exercise-leak(s). "
        "Content-based fix required: relabel the header to 'Exemple guide' (matched example "
        "intent, content retained) OR stub the code cell (matched exercise intent, content "
        "stripped). Cf .claude/rules/exercise-example-labeling.md (content-based rule) "
        "and PR #8074 (the originating detector PR).",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
