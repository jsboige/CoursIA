#!/usr/bin/env python3
"""pr_gate.py -- the single requerrable check for `main` (issue #9819).

## Why this exists

`main` has NO required status check. Measured firsthand 2026-08-07:

    gh api repos/jsboige/CoursIA/branches/main/protection   -> no required_status_checks
    gh api repos/jsboige/CoursIA/rulesets                   -> []

So a PR whose CI is red reports `UNSTABLE` (mergeable), never `BLOCKED`. The
only thing standing between a red build and `main` is a human reading
`gh pr checks` at ~180 merges/day. On 2026-08-07 that failed: #9762 was merged
with `ci / Lean CI (grothendieck_lean) -> fail` AND a body that declared its own
build gate as still running. `main` stayed red for ~5 hours.

## Why the obvious fix does not work

"Just mark `Lean CI (grothendieck_lean)` as required" DEADLOCKS the repository.
GitHub counts a check that never started as **pending, forever** -- there is no
`skipped` state for a workflow whose `paths:` filter did not match. Requiring a
path-filtered check makes every PR that does not touch that path unmergeable.

The only object that can be required without that trap is a check that runs on
**every** PR and always reaches a verdict. That is this one.

## What it does

Waits for every other check on the head SHA to settle, then fails if any of
them failed. One name to require; it covers whatever CI happens to exist,
now and later, with no per-workflow wiring to maintain.

## Design rules that matter

1. **Bias to fail.** Timeout, API error, or a check with no verdict => exit 1.
   A gate that passes when it does not know is not a gate. This is deliberate
   and is the single most important property of the file.
2. **Latest run per workflow wins.** GitHub's concurrency groups cancel
   superseded runs, and re-runs leave the old attempt visible. Without
   de-duplication, one benign `cancelled` from a superseded run would block a
   perfectly good PR (observed on `main`: `Quarto Pages Deploy` cancelled on
   401a68cd8 while the same SHA was otherwise green). We keep only the newest
   run per workflow name and judge that one.
3. **`cancelled` on the newest run fails.** After de-duplication, a cancelled
   run means no verdict was produced. Per rule 1 that is a failure, not a pass.
4. **Self-exclusion.** The gate never waits for itself.
5. **Legacy commit statuses count too.** Some integrations post statuses, not
   check runs; both are unioned.

Exit codes: 0 = every settled check is non-failing (or there are none).
            1 = at least one failure, or the state could not be established.

Run locally against any PR head:

    python scripts/pr_gate.py --repo jsboige/CoursIA --sha <head-sha> --timeout-min 1
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from typing import Iterable, Sequence

# A check that reached one of these has produced a verdict we accept.
CONCLUSION_OK = frozenset({"success", "neutral", "skipped"})

# A check that reached one of these has produced a verdict we reject.
# `cancelled` is here on purpose (see rule 3 in the module docstring): after
# de-duplication it can no longer mean "superseded", only "no verdict".
CONCLUSION_BAD = frozenset(
    {"failure", "timed_out", "cancelled", "action_required", "stale", "startup_failure"}
)

# GitHub check_run.status values that mean "not finished".
STATUS_PENDING = frozenset({"queued", "in_progress", "waiting", "pending", "requested"})

DEFAULT_SELF_NAME = "PR gate"


class GateError(RuntimeError):
    """Raised when the check state cannot be established. Always fatal."""


# --- pure decision layer (no network; this is what the unit tests pin) -------


def dedupe_latest(checks: Sequence[dict]) -> list[dict]:
    """Keep only the most recent entry per check name.

    GitHub leaves superseded and re-run attempts visible on the same SHA. Judging
    all of them makes a benign concurrency cancellation indistinguishable from a
    real failure. Ordering key is `started_at` then `id`, both monotonic per name;
    entries missing both keep their input order as a last resort.
    """
    best: dict[str, tuple[tuple, dict]] = {}
    for index, check in enumerate(checks):
        name = check.get("name") or ""
        key = (check.get("started_at") or "", check.get("id") or 0, index)
        current = best.get(name)
        if current is None or key >= current[0]:
            best[name] = (key, check)
    return [entry[1] for entry in best.values()]


def classify(
    checks: Sequence[dict], self_name: str = DEFAULT_SELF_NAME
) -> tuple[list[str], list[str], list[str]]:
    """Split settled checks into (pending, bad, ok) name lists.

    `self_name` is excluded so the gate never waits on itself. Matching is a
    prefix test because GitHub renders a job inside a workflow as
    "<workflow> / <job>", and the gate is required under its workflow name.
    """
    pending: list[str] = []
    bad: list[str] = []
    ok: list[str] = []

    for check in dedupe_latest(checks):
        name = check.get("name") or "<unnamed>"
        if name == self_name or name.startswith(f"{self_name} /"):
            continue

        status = (check.get("status") or "").lower()
        conclusion = (check.get("conclusion") or "").lower()

        if status in STATUS_PENDING or not conclusion:
            pending.append(name)
        elif conclusion in CONCLUSION_OK:
            ok.append(name)
        elif conclusion in CONCLUSION_BAD:
            bad.append(name)
        else:
            # Unknown conclusion: bias to fail (rule 1). A conclusion GitHub
            # adds later must not silently become a pass.
            bad.append(f"{name} (unknown conclusion '{conclusion}')")

    return sorted(pending), sorted(bad), sorted(ok)


def verdict(pending: Sequence[str], bad: Sequence[str], settled: bool) -> tuple[int, str]:
    """Final decision. Returns (exit_code, human message).

    `settled` is False when the wait loop ran out of time. Unsettled is a
    failure even with zero bad checks: we do not know, therefore we refuse.
    """
    if bad:
        return 1, "FAIL -- failing checks: " + ", ".join(bad)
    if not settled:
        listed = ", ".join(pending) if pending else "(none listed)"
        return 1, f"FAIL -- timed out waiting for: {listed}"
    if pending:
        return 1, "FAIL -- still pending at settle time: " + ", ".join(pending)
    return 0, "PASS -- no failing checks"


# --- network layer ----------------------------------------------------------


def _gh_api(path: str) -> object:
    """Call `gh api <path>` and parse JSON. Any failure is fatal (rule 1)."""
    try:
        completed = subprocess.run(
            ["gh", "api", path],
            capture_output=True,
            text=True,
            check=False,
        )
    except FileNotFoundError as exc:  # pragma: no cover - environment problem
        raise GateError(f"gh CLI not available: {exc}") from exc

    if completed.returncode != 0:
        raise GateError(
            f"gh api {path} failed (exit {completed.returncode}): "
            f"{completed.stderr.strip()[:400]}"
        )
    try:
        return json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise GateError(f"gh api {path} returned non-JSON: {exc}") from exc


def fetch_checks(repo: str, sha: str) -> list[dict]:
    """Union of check runs and legacy commit statuses for one SHA."""
    checks: list[dict] = []

    runs = _gh_api(f"repos/{repo}/commits/{sha}/check-runs?per_page=100")
    if isinstance(runs, dict):
        for run in runs.get("check_runs", []):
            checks.append(
                {
                    "name": run.get("name"),
                    "status": run.get("status"),
                    "conclusion": run.get("conclusion"),
                    "started_at": run.get("started_at"),
                    "id": run.get("id"),
                }
            )

    combined = _gh_api(f"repos/{repo}/commits/{sha}/status")
    if isinstance(combined, dict):
        for status in combined.get("statuses", []):
            state = (status.get("state") or "").lower()
            checks.append(
                {
                    "name": status.get("context"),
                    "status": "in_progress" if state == "pending" else "completed",
                    "conclusion": {
                        "success": "success",
                        "failure": "failure",
                        "error": "failure",
                    }.get(state, "" if state == "pending" else state),
                    "started_at": status.get("created_at"),
                    "id": status.get("id"),
                }
            )

    return checks


def wait_and_decide(
    repo: str,
    sha: str,
    self_name: str,
    timeout_min: float,
    poll_sec: float,
    settle_polls: int,
    sleep=time.sleep,
    fetch=fetch_checks,
    now=time.monotonic,
) -> tuple[int, str]:
    """Poll until the check set is stable, then decide.

    Stability is `settle_polls` consecutive polls with nothing pending -- a
    single quiet poll is not enough, because a workflow queued milliseconds ago
    has not surfaced yet and would be invisible.
    """
    deadline = now() + timeout_min * 60.0
    quiet_streak = 0
    pending: list[str] = []
    bad: list[str] = []

    while True:
        checks = fetch(repo, sha)
        pending, bad, ok = classify(checks, self_name)

        if bad:
            # Fail fast: a failure cannot be undone by waiting longer.
            return verdict(pending, bad, settled=True)

        if pending:
            quiet_streak = 0
        else:
            quiet_streak += 1
            if quiet_streak >= settle_polls:
                print(f"[pr-gate] settled: {len(ok)} check(s) green", flush=True)
                return verdict(pending, bad, settled=True)

        if now() >= deadline:
            return verdict(pending, bad, settled=False)

        print(
            f"[pr-gate] waiting on {len(pending)} check(s): "
            f"{', '.join(pending[:6])}{' ...' if len(pending) > 6 else ''}",
            flush=True,
        )
        sleep(poll_sec)


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--sha", required=True, help="head SHA of the PR")
    parser.add_argument("--self-name", default=DEFAULT_SELF_NAME)
    parser.add_argument("--timeout-min", type=float, default=90.0)
    parser.add_argument("--poll-sec", type=float, default=30.0)
    parser.add_argument("--settle-polls", type=int, default=2)
    args = parser.parse_args(list(argv) if argv is not None else None)

    try:
        code, message = wait_and_decide(
            args.repo,
            args.sha,
            args.self_name,
            args.timeout_min,
            args.poll_sec,
            args.settle_polls,
        )
    except GateError as exc:
        # Rule 1: an unreadable state is a failure, never a pass.
        print(f"[pr-gate] FAIL -- cannot establish check state: {exc}", file=sys.stderr)
        return 1

    print(f"[pr-gate] {message}", flush=True)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
