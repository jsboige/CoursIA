#!/usr/bin/env python3
"""#17262 -- a transient API error must not cost the merge gate its budget.

The defect, measured on 2026-09-21. `wait_and_decide` is built entirely around
NOT concluding too early: 90 polls of 30 s, a delivery canary, and even a
re-read at the deadline added by #11751 precisely because a timeout falling
between two polls fabricated a false FAIL. Yet a SINGLE transient API error
abandoned all 90 polls, because `fetch_checks` calls `_gh_api` once per page
plus once for `/status`, neither retries, and the loop's fetch carried no
`try`. Four PRs (#17224, #17228, #17246, #17260) carried the resulting red with
no content defect, all with the same signature:

    [pr-gate] FAIL -- cannot establish check state: gh api
      repos/jsboige/CoursIA/commits/<sha>/check-runs?per_page=100&page=1
      failed (exit 1): gh: API rate limit exceeded ...

The asymmetry in one sentence: the gate grants 90 polls to a workflow that has
not started yet, and zero to an instant of network noise.

This file pins the four acceptance criteria of the issue, plus the two
invariants the fix must not break.

**Criterion 2 is the one that matters.** Rule 1 -- "an unreadable state is a
failure, never a pass" -- is not relaxed here: when the state stays unreadable,
the gate still ends in FAIL with the cause named. The control that distinguishes
this fix from a loosening of the gate is
``test_acceptance_2_*``: without it, a change that simply swallowed the error
would pass every other test in this file.

The final FAIL rendering is exercised by ``test_pr_gate.py`` (it monkeypatches
``wait_and_decide`` to raise ``GateError`` and asserts ``code == 1``); this file
therefore asserts at the ``wait_and_decide`` boundary and names the cause, and
does not duplicate that composition.

Run: python -m pytest scripts/tests/test_pr_gate_transient_retry.py
"""
import itertools
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pr_gate  # noqa: E402
from pr_gate import GateError  # noqa: E402

# Verbatim shape of the four production failures (see issue #17262).
RATE_LIMIT = (
    "gh api repos/o/r/commits/sha/check-runs?per_page=100&page=1 failed "
    "(exit 1): gh: API rate limit exceeded for installation. (HTTP 403)"
)
NOT_FOUND = (
    "gh api repos/o/r/commits/deadbeef/check-runs failed (exit 1): "
    "gh: Not Found (HTTP 404)"
)


def run(name, conclusion, status="completed", rid=1):
    return {
        "name": name,
        "status": status,
        "conclusion": conclusion,
        "started_at": "2026-09-21T00:00:00Z",
        "id": rid,
    }


def _clock(step=10):
    """A monotonic clock that advances on every reading, as the loop reads it."""
    counter = itertools.count(0, step)
    return lambda: next(counter)


def _wait(fetch, timeout_min=45, settle_polls=2, poll_sec=0):
    return pr_gate.wait_and_decide(
        "o/r", "sha", "PR gate", timeout_min=timeout_min, poll_sec=poll_sec,
        settle_polls=settle_polls, sleep=lambda _s: None, fetch=fetch, now=_clock(),
    )


# --- classification ---------------------------------------------------------
#
# The direction of the default is the design decision worth pinning: only a
# RECOGNISED transient signature is retried, so an unknown error stays fatal.


@pytest.mark.parametrize(
    "text,expected,why",
    [
        (RATE_LIMIT, True, "the measured production signature"),
        ("gh api /x failed (exit 1): (HTTP 403)", True, "bare 403"),
        ("gh api /x failed (exit 1): (HTTP 429)", True, "throttled"),
        ("gh api /x failed (exit 1): (HTTP 503)", True, "upstream 5xx"),
        ("gh api /x returned non-JSON: Expecting value", True, "truncated body"),
        ("gh api /x failed (exit 1): operation timed out", True, "socket timeout"),
        (NOT_FOUND, False, "a gone SHA cannot be fixed by re-reading"),
        (
            "gh api /x failed (exit 1): rate limit exceeded (HTTP 404)",
            False,
            "permanent wins when both signatures are present",
        ),
        (
            "gh api /x failed (exit 1): something never seen before",
            False,
            "unknown errors keep the historical fatal behaviour",
        ),
    ],
)
def test_classification_is_asymmetric_and_defaults_to_fatal(text, expected, why):
    assert pr_gate._is_transient_api_error(GateError(text)) is expected, why


# --- criterion 1: transient, then success, reaches the TRUE verdict ---------


def test_acceptance_1_a_hickup_still_reaches_the_true_verdict(capsys):
    """Today this case returns `cannot establish check state` instead."""
    calls = []

    def fetch(_repo, _sha):
        calls.append(1)
        if len(calls) == 1:
            raise GateError(RATE_LIMIT)
        return [run("Lean CI", "success")]

    code, msg = _wait(fetch)
    assert code == 0, msg
    assert "cannot establish" not in msg
    # 1 failed read + 2 quiet polls (settle_polls) -- the failed read neither
    # advanced nor reset the quiet streak.
    assert len(calls) == 3
    # A retry must be VISIBLE. Every defect in this family was a silence that
    # read like a verdict; a retry reported only in a green PR's logs is still
    # a retry nobody can audit.
    out = capsys.readouterr().out
    assert "transient API error" in out
    assert "rate limit exceeded" in out


# --- criterion 2: the control -- rule 1 is untouched ------------------------


def test_acceptance_2_an_unreadable_state_still_fails_naming_the_cause():
    """THE control test. A fix that swallowed the error would fail here."""
    calls = []

    def fetch(_repo, _sha):
        calls.append(1)
        raise GateError(RATE_LIMIT)

    with pytest.raises(GateError) as excinfo:
        _wait(fetch)
    message = str(excinfo.value)
    assert "rate limit exceeded" in message, "the cause must still be named"
    assert "transient read failure" in message, (
        "the verdict must say the state stayed unreadable, not blame the PR"
    )
    assert len(calls) == pr_gate.MAX_CONSECUTIVE_TRANSIENT_RETRIES + 1


# --- criterion 3: bounded in attempts AND in deadline -----------------------


def test_acceptance_3_the_deadline_bounds_the_retry_not_only_the_cap():
    """With no budget left, not even the first retry may be spent.

    `timeout_min=0` puts the deadline at the first clock reading, so the very
    first transient failure is already out of budget.
    """
    calls = []

    def fetch(_repo, _sha):
        calls.append(1)
        raise GateError(RATE_LIMIT)

    with pytest.raises(GateError):
        _wait(fetch, timeout_min=0)
    assert len(calls) == 1, (
        "a retry here would extend --timeout-min, which criterion 3 forbids"
    )


def test_acceptance_3_the_retry_does_not_extend_the_declared_budget():
    """The absolute deadline is read, never recomputed by the retry path."""
    readings = []

    def fetch(_repo, _sha):
        raise GateError(RATE_LIMIT)

    code_clock = _clock()
    seen = []

    def now():
        value = code_clock()
        seen.append(value)
        return value

    with pytest.raises(GateError):
        pr_gate.wait_and_decide(
            "o/r", "sha", "PR gate", timeout_min=45, poll_sec=0,
            settle_polls=2, sleep=lambda _s: None, fetch=fetch, now=now,
        )
    readings.extend(seen)
    # deadline = first reading + 45*60; the retry path compares against it and
    # never moves it. Every comparison is `>=`, so the loop stops the moment
    # the clock passes the SAME value it started from.
    deadline = readings[0] + 45 * 60
    assert max(readings) <= deadline + 10, (
        f"the retry path let the clock run past the declared deadline: {readings}"
    )


# --- criterion 4: only transient errors are retried ------------------------


@pytest.mark.parametrize(
    "text,why",
    [
        (NOT_FOUND, "a PR or SHA that disappeared is not a hiccup"),
        (
            "gh api /x failed (exit 1): an error we have never seen",
            "unknown errors stay fatal",
        ),
    ],
)
def test_acceptance_4_permanent_and_unknown_errors_are_not_retried(text, why):
    calls = []

    def fetch(_repo, _sha):
        calls.append(1)
        raise GateError(text)

    with pytest.raises(GateError):
        _wait(fetch)
    assert len(calls) == 1, why


# --- invariants the fix must not break --------------------------------------


def test_a_failed_read_is_not_counted_as_a_quiet_poll():
    """Counting an outage as quiet would let it settle the wait into a PASS.

    Without this invariant the sequence below settles at poll 2 -- a PASS
    produced by a read that never happened, which is the one direction rule 1
    forbids.
    """
    calls = []

    def fetch(_repo, _sha):
        calls.append(1)
        if len(calls) == 2:
            raise GateError(RATE_LIMIT)
        return [run("Lean CI", "success")]

    code, msg = _wait(fetch)
    assert code == 0, msg
    assert len(calls) == 3, (
        "the failed read must neither advance the quiet streak (settling at "
        "poll 2) nor be retried into a different poll count"
    )


def test_the_cap_counts_consecutive_failures_not_a_lifetime_total():
    """A flapping API must not be mistaken for one that spent its budget.

    Six transient failures are injected, more than the cap, but never two in a
    row: a cumulative counter would raise, a consecutive one settles.
    """
    calls = []

    def fetch(_repo, _sha):
        calls.append(1)
        if len(calls) % 2 == 1:
            raise GateError(RATE_LIMIT)
        return [run("Lean CI", "success")]

    code, msg = _wait(fetch, settle_polls=6)
    assert code == 0, msg
    assert calls.count(1) > pr_gate.MAX_CONSECUTIVE_TRANSIENT_RETRIES, (
        "the scenario must actually exceed the cap in total"
    )
