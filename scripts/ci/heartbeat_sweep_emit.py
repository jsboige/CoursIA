#!/usr/bin/env python3
r"""heartbeat_sweep_emit.py -- emit a one-line dashboard heartbeat for the
``pr-gate-stale-sweep`` workflow.

## Why

Issue #11860 / #12588 framed the failure mode: ``#12547`` removed the
event-driven ``workflow_run`` path of ``pr-gate-rerun.yml``, so the cron-driven
``pr-gate-stale-sweep.yml`` is now the ONLY mechanism that re-aggregates a
stale ``PR gate`` verdict. If that sweep's scheduler stops -- saturated runners,
accidental disable, plan expiry on an inert repo -- nothing says so.

Form 1 of that alarm is ``.github/workflows/pr-gate-sweep-health-advisory.yml``
(cron-driven observer). It rougit non-blockingly when the last successful
sweep is older than ``STALE_AFTER_MINUTES=60`` (env knob).

Form 2 (the floor, immune to runner failure -- mandated by #12588) is a
dashboard heartbeat emitted by ai-01 each ``/coordinate`` cycle. This script
is the FORM-2 EMITTER: it asks ``gh run list`` for the last successful sweep
run, computes its age in seconds, and prints one line ready for an
``append`` to the workspace dashboard.

## Output

A single line on stdout, e.g.::

    [sweep-heartbeat] last successful pr-gate-stale-sweep run: 1234s ago (OK, <3600s)

If no successful run exists, prints a sentinel the dashboard layer can match
on (``NO_SUCCESS_IN_HISTORY``) and exits 1 so a CI step can rougir on the
absence itself -- the exact case the observer exists to catch.

Exit codes:
  0  -- last successful run younger than ``--stale-after-minutes`` (default 60)
  1  -- stale (older than threshold) OR no successful run found OR gh error
  2  -- usage error (bad args)

## Usage

::

    python3 scripts/ci/heartbeat_sweep_emit.py
    python3 scripts/ci/heartbeat_sweep_emit.py --workflow pr-gate-stale-sweep.yml \\
        --stale-after-minutes 60
    python3 scripts/ci/heartbeat_sweep_emit.py --json

The ``--json`` form emits ``{"workflow": "...", "age_s": int|None,
"stale": bool, "stale_after_s": int, "reason": "ok"|"no_success"|"error"}``
for programmatic consumers (e.g. an ai-01 dashboard appender that wants a
structured payload before formatting).
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone

DEFAULT_WORKFLOW = "pr-gate-stale-sweep.yml"
DEFAULT_STALE_AFTER_MINUTES = 60


def last_success_age_s(workflow: str, run=None) -> int | None:
    """Age in seconds of the most recent *successful* run of ``workflow``.

    Returns ``None`` when no successful run is found (this is the case the
    heartbeat exists to surface). ``run`` is dependency-injected for tests;
    the default shells out to ``gh``.
    """
    if run is None:
        def run(_workflow: str) -> list[dict]:
            out = subprocess.run(
                ["gh", "run", "list", "--workflow", _workflow,
                 "--status", "success", "--limit", "1",
                 "--json", "createdAt,conclusion"],
                capture_output=True, text=True, check=False,
            )
            if out.returncode != 0 or not out.stdout.strip():
                return []
            try:
                return json.loads(out.stdout)
            except json.JSONDecodeError:
                return []

    runs = run(workflow)
    if not runs:
        return None
    created = (runs[0].get("createdAt") or "").replace("Z", "+00:00")
    if not created:
        return None
    return int((datetime.now(timezone.utc)
                - datetime.fromisoformat(created)).total_seconds())


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--workflow", default=DEFAULT_WORKFLOW,
                   help=f"sweep workflow file (default {DEFAULT_WORKFLOW})")
    p.add_argument("--stale-after-minutes", type=int,
                   default=DEFAULT_STALE_AFTER_MINUTES,
                   help=f"threshold for the 'stale' verdict "
                        f"(default {DEFAULT_STALE_AFTER_MINUTES})")
    p.add_argument("--json", action="store_true",
                   help="emit structured JSON instead of the dashboard line")
    args = p.parse_args(argv)

    if args.stale_after_minutes <= 0:
        print(f"heartbeat_sweep_emit: --stale-after-minutes must be > 0 "
              f"(got {args.stale_after_minutes})", file=sys.stderr)
        return 2

    threshold_s = args.stale_after_minutes * 60
    try:
        age_s = last_success_age_s(args.workflow)
    except OSError as e:
        # gh missing / not authenticated / transient.
        if args.json:
            print(json.dumps({"workflow": args.workflow, "age_s": None,
                              "stale": True, "stale_after_s": threshold_s,
                              "reason": "error", "error": str(e)}))
        else:
            print(f"[sweep-heartbeat] gh unavailable: {e}", file=sys.stderr)
        return 1

    if age_s is None:
        if args.json:
            print(json.dumps({"workflow": args.workflow, "age_s": None,
                              "stale": True, "stale_after_s": threshold_s,
                              "reason": "no_success"}))
        else:
            print(f"[sweep-heartbeat] NO_SUCCESS_IN_HISTORY for "
                  f"{args.workflow} -- is its schedule alive? (#11860 / #12588)")
        return 1

    stale = age_s > threshold_s
    if args.json:
        print(json.dumps({"workflow": args.workflow, "age_s": age_s,
                          "stale": stale, "stale_after_s": threshold_s,
                          "reason": "ok"}))
    else:
        verdict = "STALE" if stale else "OK"
        print(f"[sweep-heartbeat] last successful {args.workflow} run: "
              f"{age_s}s ago ({verdict}, <{threshold_s}s)")

    return 1 if stale else 0


if __name__ == "__main__":
    sys.exit(main())