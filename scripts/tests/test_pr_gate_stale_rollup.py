"""Regression tests for the stale-rollup bug (#10433).

The PR gate (`scripts/pr_gate.py`) aggregates all check verdicts for a SHA.
A stale FAILURE became permanent when a required check (the Variation Tag Guard)
turned green AFTER the gate had already aggregated -- because the gate triggers
on `pull_request` (no `edited`), and its fail-fast path returns on the first poll
that sees a `bad` conclusion, before a newer run can supersede it.

The fix re-triggers the rollup via `workflow_run` on the guard's completion, so
the gate only ever aggregates a state where the guard has already settled. These
tests pin the classify/wait_and_decide behaviour the fix relies on, so the
trigger change cannot silently regress them:

  1. wait_then_pass -- a check pending on poll 1, ok on poll 2 -> PASS. This is
     the path the workflow_run re-trigger takes: by the time it fires, the guard
     has completed, so the gate observes it settled-green and passes.
  2. fail_fast_on_bad -- a genuinely-failed check -> FAIL on poll 1 (no wait).
     Pins that the fail-fast is not weakened by the workflow_run change.
  3. stale_bad_then_ok_currently_fails -- the `edited`-race limitation the
     workflow_run approach exists to avoid: a `bad` conclusion on poll 1 fails
     fast even when poll 2 would supersede it. Documents WHY the fix chose
     `workflow_run` (post-completion) over `edited` (parallel, races the stale
     conclusion). If this ever starts PASS-ing, revisit whether `edited` alone
     would then suffice -- do not let it flip silently.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pr_gate import wait_and_decide  # noqa: E402


def _check(name, status, conclusion):
    """Minimal check-run dict (the keys classify()/dedupe_latest() read)."""
    return {
        "name": name,
        "status": status,
        "conclusion": conclusion,
        "started_at": "2026-08-11T00:00:00Z",
    }


def _run(fetch_sequence, *, settle_polls=2, timeout_min=90):
    """Drive wait_and_decide over a scripted sequence of fetch results.

    fetch_sequence: list of check-lists, one per poll. The last entry repeats for
    any extra polls the gate requests (a stable terminal state), so the test
    terminates even when the gate needs settle_polls quiet polls to converge.
    Returns (exit_code, message, polls_consumed).
    """
    calls = {"i": 0}

    def fetch(_repo, _sha):
        i = calls["i"]
        calls["i"] = i + 1
        return fetch_sequence[min(i, len(fetch_sequence) - 1)]

    clock = {"t": 0.0}

    def now():
        # Advance 30 s per poll; stays well under the timeout_min*60 deadline so
        # the timeout path (settled=False) never fires in these scenarios.
        clock["t"] += 30.0
        return clock["t"]

    code, msg = wait_and_decide(
        repo="jsboige/CoursIA",
        sha="deadbeef",
        self_name="PR gate",
        timeout_min=timeout_min,
        poll_sec=30.0,
        settle_polls=settle_polls,
        sleep=lambda _s: None,
        fetch=fetch,
        now=now,
    )
    return code, msg, calls["i"]


def test_wait_then_pass():
    """Required check pending on poll 1, ok on poll 2 -> PASS (workflow_run path)."""
    guard = "Variation Tag Guard"
    code, msg, polls = _run(
        [
            [_check(guard, "in_progress", None)],  # poll 1: guard still running
            [_check(guard, "completed", "success")],  # poll 2: guard green
        ]
    )
    assert code == 0, f"expected PASS, got {code}: {msg}"
    assert polls >= 2  # did not fail-fast; waited for the guard to settle


def test_fail_fast_on_bad():
    """A genuinely-failed check -> FAIL on poll 1, no waiting (regression pin)."""
    code, msg, polls = _run(
        [
            [_check("CI Build", "completed", "failure")],
            [_check("CI Build", "completed", "success")],  # never reached
        ]
    )
    assert code == 1
    assert polls == 1  # fail-fast: did not wait for the would-be-green poll 2


def test_stale_bad_then_ok_currently_fails():
    """The edited-race limitation: bad on poll 1 fails fast even if poll 2 ok.

    This is the documented reason the fix uses `workflow_run` (fires after the
    guard completes, so it never observes a stale-then-superseded `bad`) rather
    than `edited` (which triggers the rollup in parallel with the new guard run,
    racing the stale conclusion). See #10433 acceptance item 1.
    """
    guard = "Variation Tag Guard"
    code, msg, polls = _run(
        [
            [_check(guard, "completed", "failure")],  # stale failed guard
            [_check(guard, "completed", "success")],  # new run supersedes (never reached)
        ]
    )
    assert code == 1  # current behaviour: fail-fast on poll 1
    assert polls == 1
