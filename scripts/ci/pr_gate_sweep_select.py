"""
PR gate stale-verdict sweep selector.

Extracted from `.github/workflows/pr-gate-stale-sweep.yml` heredoc so the
filter can be unit-tested (#11862) -- the heredoc body lived inline before,
which made it impossible to assert "the selector would have caught
PR #11852 on the 2026-08-19 cancelled state" without invoking a workflow
run.

The filter is intentionally narrow: it yields PRs whose `PR gate` leg is
RED (any conclusion in :data:`RED_GATE`) while every other check has
COMPLETED green. Two design choices matter:

1. `PR gate` legs are NOT folded by name (latest-wins is FALSE for the
   REQUIRED check). Two same-named required check-runs can coexist on
   one SHA in different suites, and GitHub AND-s them -- a newer
   SUCCESS does NOT clear an older FAILURE. Measured 2026-08-17 on
   #11532.
2. `cancelled` is treated as RED for `PR gate` ONLY (#11862). On the
   gate, `cancelled` means "verdict never rendered, re-aggregate to
   render it" -- the same shape as the other RED conclusions. On
   non-required checks, `cancelled` means supersession (already handled
   by the per-name fold) or a real interruption that must NOT be
   silently green-washed. Hence two separate sets: :data:`RED_GATE` and
   :data:`GREEN_OTHER`.

Run as a module:
    python -m ci.pr_gate_sweep_select < /tmp/runs.jsonl

`runs.jsonl` is one JSON object per line, each with keys ``number``,
``sha``, ``fork`` (bool), ``checks`` (list of {name, status, conclusion,
started_at}). Output is the same ``number sha fork`` triples the
workflow expects on stdout.
"""
from __future__ import annotations

import json
import sys
from typing import Iterable, Iterator

# Lowercase: REST /check-runs is lowercase where GraphQL's rollup is
# uppercase. Neutral / skipped are green for non-required checks: GitHub
# treats them as non-blocking, and a path-filtered guard that skipped
# must not keep a PR out of the pool.
GREEN_OTHER = frozenset({"success", "neutral", "skipped"})

# `PR gate` is the REQUIRED check, latest-wins is FALSE there. The
# `cancelled` member (#11862) is asymmetric: only a gate `cancelled`
# means "verdict never rendered, re-aggregate" -- the same shape as
# `failure` / `timed_out` / `action_required`. On a non-required
# check, `cancelled` is supersession (already folded) or a real
# interruption we do NOT want to silently green-wash.
RED_GATE = frozenset({"failure", "timed_out", "action_required", "cancelled"})


def _latest_by_name(checks: Iterable[dict]) -> dict[str, tuple[str, dict]]:
    """For NON-required checks: same-name reruns collapse to the most
    recent (latest ``started_at`` wins). Required check `PR gate` is
    handled separately -- it must NOT be folded.
    """
    latest: dict[str, tuple[str, dict]] = {}
    for c in checks:
        name = c.get("name") or "?"
        started = c.get("started_at") or ""
        if name not in latest or started >= latest[name][0]:
            latest[name] = (started, c)
    return latest


def is_stale_gate(pr: dict) -> bool:
    """Return True iff `pr` has a `PR gate` leg with a RED conclusion
    AND every other check has COMPLETED with a GREEN conclusion.

    `pr` shape: ``{number, sha, fork, checks: [{name, status, conclusion,
    started_at}, ...]}``.
    """
    checks = pr.get("checks") or []

    gate_legs = [c for c in checks if (c.get("name") or "") == "PR gate"]
    if not gate_legs:
        return False  # absent gate -> pr-gate-missing-advisory.yml's case
    if not any((c.get("conclusion") or "") in RED_GATE for c in gate_legs):
        return False

    latest = _latest_by_name(checks)
    others = [(n, c) for n, (_t, c) in latest.items() if n != "PR gate"]
    # An unfinished check means the gate may still be legitimately
    # waiting: re-aggregating then would just burn another verdict on
    # the same incomplete set.
    if not all((c.get("status") or "") == "completed" for _n, c in others):
        return False
    if not all((c.get("conclusion") or "") in GREEN_OTHER for _n, c in others):
        return False

    return True


def select_stale_gate_prs(runs_path: str) -> Iterator[dict]:
    """Yield PR dicts from `runs_path` whose `PR gate` leg is stale."""
    with open(runs_path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            pr = json.loads(line)
            if is_stale_gate(pr):
                yield pr


def _main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: python -m ci.pr_gate_sweep_select <runs.jsonl>",
              file=sys.stderr)
        return 2
    for pr in select_stale_gate_prs(argv[1]):
        print(f'{pr["number"]} {pr["sha"]} {str(pr.get("fork", False)).lower()}')
    return 0


if __name__ == "__main__":
    sys.exit(_main(sys.argv))
