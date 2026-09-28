#!/usr/bin/env python3
"""Route decision for pr-gate-rerun.yml -- revive dead `queued` attempts (#17680).

Measured defect (2026-09-23/24): three rerun attempts stayed `queued` with an
empty job list for 19h30 (PR #17099 among them), while the queue served same-day
attempts in minutes. The resolve step read ANY `status != completed` as
"in flight -- it will see the fresh guard verdict, skip", so a queued attempt
GitHub has lost is indistinguishable from a healthy one by status alone. The PR
stays BLOCKED with zero red, and the stale-sweep's own `gh run rerun` is refused
by the API on a non-completed run -- a complete impasse.

The whole route is extracted here so it is unit-testable (the workflow step is
a thin call):

  no run found         -> a "PR gate" check-run already exists on the SHA ?
                            yes -> skip   (never POST beside it, #11519 twin)
                            no  -> aggregate_absent (#16624)
  status != completed  -> `queued` for longer than --stale-hours ?
                            yes -> cancel, wait for `completed` (bounded),
                                   then action=rerun
                            no  -> skip   (genuinely in flight)
  completed + success  -> skip
  completed + other    -> rerun

The stale threshold must sit above the measured queue latency
(scripts/ci/gh_queue_health.py); the default of 2 h follows the issue's
proposal (dead attempts measured at 19h30, healthy ones served in minutes).

Bias: an unreadable API on the twin-guard probe counts as "a check-run
exists" (skip) -- same fail-closed choice the inline bash made (`|| echo 1`).
A revive that cannot reach `completed` within --wait-max-sec downgrades to
skip with a loud reason (the attempt was NOT cancelled into a rerunnable
state; re-running would be refused anyway) -- the next sweep re-dispatches.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timedelta, timezone
from typing import Any, Callable

DEFAULT_STALE_HOURS = 2.0
DEFAULT_WAIT_MAX_SEC = 300
DEFAULT_POLL_SEC = 10
SELF_NAME = "PR gate"


class RouteError(RuntimeError):
    """Fatal route failure (unreadable API on the primary lookups)."""


def _run_gh(args: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(
        args, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )


def gh_api(path: str) -> Any:
    """GET `gh api <path>` and parse JSON. Any failure is fatal."""
    completed = _run_gh(["gh", "api", path])
    if completed.returncode != 0:
        raise RouteError(
            f"gh api {path} failed (exit {completed.returncode}): "
            f"{completed.stderr.strip()[:400]}"
        )
    try:
        return json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise RouteError(f"gh api {path} returned non-JSON: {exc}") from exc


def gh_api_lenient(path: str) -> Any:
    """GET that returns None on any failure (probes whose failure means
    "act as if the guard tripped", fail-closed)."""
    try:
        return gh_api(path)
    except RouteError:
        return None


def find_latest_pr_gate_run(repo: str, head_sha: str) -> dict | None:
    """Most recently CREATED `PR gate` run with event=pull_request for the SHA.

    Per #11519: a rerun replays the frozen payload of its original event, so an
    older run for the same SHA is fine but a run for an older SHA would
    re-aggregate a stale head.
    """
    payload = gh_api(
        f"repos/{repo}/actions/runs?head_sha={head_sha}"
        "&event=pull_request&per_page=100"
    )
    runs = [
        run
        for run in payload.get("workflow_runs", [])
        if run.get("name") == SELF_NAME
    ]
    if not runs:
        return None
    return max(runs, key=lambda run: run.get("created_at") or "")


def existing_self_check_runs(repo: str, head_sha: str) -> int:
    payload = gh_api_lenient(
        f"repos/{repo}/commits/{head_sha}/check-runs?per_page=100"
    )
    if payload is None:
        # Fail-closed: unreadable == "a check-run exists" -> skip.
        return 1
    return sum(
        1 for cr in payload.get("check_runs", []) if cr.get("name") == SELF_NAME
    )


def _parse_ts(value: str | None) -> datetime | None:
    if not value:
        return None
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return None


def attempt_started_at(run: dict) -> datetime | None:
    """When the current attempt last moved.

    A queued attempt GitHub has lost never started: `run_started_at` is null,
    so fall back to `updated_at` (bumped on the transition into queued), then
    `created_at`. This is the honest "how long has it sat like this" clock.
    """
    for key in ("run_started_at", "updated_at", "created_at"):
        stamp = _parse_ts(run.get(key))
        if stamp is not None:
            return stamp
    return None


def _now() -> datetime:
    """Injectable clock (unit tests pin it; #17680 verdicts are time-based)."""
    return datetime.now(timezone.utc)


def classify(run: dict, now: datetime, stale_after: timedelta) -> tuple[str, str]:
    """Pure decision for a FOUND run -> (action, reason).

    Actions: "rerun" (full re-run of the original), "cancel_rerun" (the
    attempt is dead -- cancel it, wait, then re-run), "skip".
    """
    status = run.get("status")
    conclusion = run.get("conclusion")
    if status != "completed":
        started = attempt_started_at(run)
        if (
            status == "queued"
            and started is not None
            and now - started > stale_after
        ):
            return (
                "cancel_rerun",
                f"queued since {started.isoformat()} (> {stale_after}) -- "
                "dead attempt, cancel then re-run (#17680)",
            )
        return "skip", f"run in flight ({status}) -- it will see the fresh guard verdict"
    if conclusion == "success":
        return "skip", "run already green -- nothing to rescue"
    return "rerun", f"completed with conclusion {conclusion}"


def cancel_run(repo: str, run_id: int) -> bool:
    completed = _run_gh(
        ["gh", "api", "-X", "POST", f"repos/{repo}/actions/runs/{run_id}/cancel"]
    )
    return completed.returncode == 0


def wait_completed(
    run_id: int,
    get_status: Callable[[int], str | None],
    max_sec: int,
    poll_sec: int,
) -> bool:
    """Poll until the run reports `completed`. False on timeout."""
    deadline = datetime.now(timezone.utc) + timedelta(seconds=max_sec)
    while datetime.now(timezone.utc) < deadline:
        status = get_status(run_id)
        if status == "completed":
            return True
        time.sleep(poll_sec)
    return False


def _status_of(repo: str, run_id: int) -> str | None:
    try:
        return gh_api(f"repos/{repo}/actions/runs/{run_id}").get("status")
    except RouteError:
        return None


def _emit(action: str, run_id: int | None = None) -> None:
    out = os.environ.get("GITHUB_OUTPUT")
    lines = [f"action={action}"]
    if run_id is not None:
        lines.append(f"run_id={run_id}")
    body = "\n".join(lines) + "\n"
    if out:
        with open(out, "a", encoding="utf-8") as handle:
            handle.write(body)
    else:
        sys.stdout.write(body)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True)
    parser.add_argument("--sha", required=True, help="PR head SHA to re-aggregate")
    parser.add_argument("--pr-number", default="", help="PR number (logs only)")
    parser.add_argument(
        "--stale-hours",
        type=float,
        default=DEFAULT_STALE_HOURS,
        help="A queued attempt older than this is dead (default: %(default)s)",
    )
    parser.add_argument(
        "--wait-max-sec",
        type=int,
        default=DEFAULT_WAIT_MAX_SEC,
        help="Bound on the cancel->completed wait (default: %(default)s)",
    )
    parser.add_argument("--poll-sec", type=int, default=DEFAULT_POLL_SEC)
    args = parser.parse_args(argv)

    tag = f"[pr-gate] #{args.pr_number} " if args.pr_number else "[pr-gate] "
    run = find_latest_pr_gate_run(args.repo, args.sha)
    if run is None:
        if existing_self_check_runs(args.repo, args.sha) != 0:
            print(
                f"{tag}a 'PR gate' check-run already exists on {args.sha} though no pull_request run does -- refusing to POST beside it (#11519 twin), skip"
            )
            _emit("skip")
            return 0
        print(
            f"{tag}no pull_request PR gate run and no 'PR gate' check-run for "
            f"{args.sha} -- gate ABSENT (#16624): aggregating the head and "
            "POSTing the verdict"
        )
        _emit("aggregate_absent")
        return 0

    run_id = int(run["id"])
    print(f"{tag}target run {run_id}: status={run.get('status')} "
          f"conclusion={run.get('conclusion')}")
    action, reason = classify(run, _now(), timedelta(hours=args.stale_hours))

    if action == "cancel_rerun":
        print(f"{tag}{reason}")
        if not cancel_run(args.repo, run_id):
            print(f"{tag}cancel refused for run {run_id} -- skip (next sweep retries)")
            _emit("skip", run_id)
            return 0
        if not wait_completed(
            run_id,
            lambda rid: _status_of(args.repo, rid),
            args.wait_max_sec,
            args.poll_sec,
        ):
            print(
                f"{tag}run {run_id} did not reach completed within "
                f"{args.wait_max_sec}s after cancel -- skip (next sweep retries)"
            )
            _emit("skip", run_id)
            return 0
        print(f"{tag}dead attempt cancelled and completed -- proceeding to re-run")
        action = "rerun"

    print(f"{tag}{reason} -> action={action}")
    _emit(action, run_id)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except RouteError as exc:
        print(f"[pr-gate] FATAL: {exc}", file=sys.stderr)
        sys.exit(1)
