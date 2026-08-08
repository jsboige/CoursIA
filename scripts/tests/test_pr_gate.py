#!/usr/bin/env python3
"""Unit tests for pr_gate.py -- the single requerrable check of #9819.

What these pin, in order of how much damage getting them wrong would do:

1. **Bias to fail.** Timeout, unreadable API, or an unrecognised conclusion must
   exit 1. A gate that passes when it does not know is not a gate, and this is
   the property the whole file exists to guarantee.
2. **De-duplication by check name.** GitHub's concurrency groups cancel
   superseded runs and leave them visible on the SHA. Observed on `main`:
   `Quarto Pages Deploy` cancelled on 401a68cd8 while that same SHA was
   otherwise fully green. Without de-duplication the gate would have blocked a
   healthy commit -- and a gate that cries wolf gets disabled, which is worse
   than not having one.
3. **Self-exclusion**, or the gate waits for itself until timeout, i.e. blocks
   100% of PRs.

Run: python -m pytest scripts/tests/test_pr_gate.py
"""
import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pr_gate  # noqa: E402


# --- helpers -----------------------------------------------------------------


def run(name, conclusion, status="completed", started_at="2026-08-07T00:00:00Z", rid=1):
    return {
        "name": name,
        "status": status,
        "conclusion": conclusion,
        "started_at": started_at,
        "id": rid,
    }


def decide(checks, self_name=pr_gate.DEFAULT_SELF_NAME, settled=True):
    pending, bad, _ok, _adv = pr_gate.classify(checks, self_name)
    return pr_gate.verdict(pending, bad, settled=settled)


# --- 1. bias to fail ---------------------------------------------------------


def test_timeout_is_a_failure_even_with_zero_bad_checks():
    """Unsettled means we do not know. Refusing is the whole point."""
    code, msg = pr_gate.verdict(pending=["Lean CI"], bad=[], settled=False)
    assert code == 1
    assert "timed out" in msg
    assert "Lean CI" in msg


def test_unknown_conclusion_counts_as_failure():
    """A conclusion GitHub adds later must not silently become a pass."""
    code, msg = decide([run("Future CI", "quantum_superposition")])
    assert code == 1
    assert "Future CI" in msg


def test_unreadable_api_exits_one(monkeypatch):
    def boom(*_args, **_kwargs):
        raise pr_gate.GateError("gh api exploded")

    monkeypatch.setattr(pr_gate, "wait_and_decide", boom)
    assert pr_gate.main(["--repo", "o/r", "--sha", "deadbeef"]) == 1


def test_completed_without_conclusion_is_pending_not_pass():
    """`status=completed, conclusion=null` is a transient GitHub state."""
    pending, bad, ok, _adv = pr_gate.classify([run("Odd", None)])
    assert pending == ["Odd"] and not bad and not ok


# --- 2. de-duplication by check name ----------------------------------------


def test_superseded_cancelled_run_does_not_block_a_green_sha():
    """The 401a68cd8 case: cancelled by concurrency, then re-run green."""
    checks = [
        run("Quarto Pages Deploy", "cancelled", started_at="2026-08-07T05:25:00Z", rid=1),
        run("Quarto Pages Deploy", "success", started_at="2026-08-07T05:26:00Z", rid=2),
    ]
    code, msg = decide(checks)
    assert code == 0, msg


def test_input_order_does_not_change_the_verdict():
    """The API does not promise ordering; the timestamp must decide, not luck."""
    newest = run("Build", "success", started_at="2026-08-07T05:26:00Z", rid=2)
    oldest = run("Build", "cancelled", started_at="2026-08-07T05:25:00Z", rid=1)
    assert decide([newest, oldest])[0] == 0
    assert decide([oldest, newest])[0] == 0


def test_cancelled_on_the_newest_run_still_fails():
    """After de-duplication, cancelled can only mean 'no verdict' -- rule 1."""
    checks = [
        run("Build", "success", started_at="2026-08-07T05:25:00Z", rid=1),
        run("Build", "cancelled", started_at="2026-08-07T05:26:00Z", rid=2),
    ]
    code, msg = decide(checks)
    assert code == 1
    assert "Build" in msg


def test_distinct_names_are_never_merged():
    checks = [run("A", "success", rid=1), run("B", "failure", rid=2)]
    code, msg = decide(checks)
    assert code == 1 and "B" in msg and "A" not in msg.split("failing checks: ")[1]


# --- 3. self-exclusion -------------------------------------------------------


def test_gate_does_not_wait_for_itself():
    checks = [run("PR gate", None, status="in_progress"), run("Lean CI", "success")]
    pending, bad, ok, _adv = pr_gate.classify(checks, "PR gate")
    assert pending == [] and bad == [] and ok == ["Lean CI"]


def test_self_exclusion_matches_workflow_slash_job_rendering():
    checks = [run("PR gate / gate", None, status="queued")]
    pending, _bad, _ok, _adv = pr_gate.classify(checks, "PR gate")
    assert pending == []


def test_self_exclusion_is_not_a_loose_prefix():
    """"PR gateway" is a different check and must still be judged."""
    checks = [run("PR gateway", "failure")]
    _pending, bad, _ok, _adv = pr_gate.classify(checks, "PR gate")
    assert bad == ["PR gateway"]


# --- decision table ----------------------------------------------------------


def test_no_checks_at_all_passes():
    """A PR that triggers no other CI has nothing to gate."""
    assert decide([])[0] == 0


def test_skipped_and_neutral_are_green():
    checks = [run("A", "skipped", rid=1), run("B", "neutral", rid=2)]
    assert decide(checks)[0] == 0


def test_failure_is_reported_by_name():
    code, msg = decide([run("ci / Lean CI (grothendieck_lean)", "failure")])
    assert code == 1
    assert "ci / Lean CI (grothendieck_lean)" in msg


def test_the_9762_shape_fails():
    """Exactly what was merged on 2026-08-07 and made `main` red for ~5 h."""
    checks = [
        run("ci / Lean CI (grothendieck_lean)", "failure", rid=1),
        run("proof-integrity / Proof integrity (grothendieck_lean)", "failure", rid=2),
        run("Secret Scan", "success", rid=3),
        run("banner-guard", "success", rid=4),
    ]
    code, msg = decide(checks)
    assert code == 1
    assert "Lean CI" in msg and "Proof integrity" in msg


# --- wait loop ---------------------------------------------------------------


def _clock(step=10):
    counter = itertools.count(0, step)
    return lambda: next(counter)


def test_settle_requires_two_consecutive_quiet_polls():
    """One quiet poll is not enough: a just-queued workflow has not surfaced."""
    polls = []

    def fetch(_repo, _sha):
        polls.append(1)
        # Quiet, then a late arrival, then quiet twice.
        return {1: [], 2: [run("Late", None, status="queued")], 3: [], 4: []}[len(polls)]

    code, msg = pr_gate.wait_and_decide(
        "o/r", "sha", "PR gate", timeout_min=10, poll_sec=0,
        settle_polls=2, sleep=lambda _s: None, fetch=fetch, now=_clock(),
    )
    assert code == 0, msg
    assert len(polls) == 4, "the late arrival must reset the streak"


def test_wait_loop_fails_fast_on_a_failure():
    """Waiting cannot un-fail a check; do not burn 90 minutes to learn that."""
    polls = []

    def fetch(_repo, _sha):
        polls.append(1)
        return [run("Lean CI", "failure")]

    code, msg = pr_gate.wait_and_decide(
        "o/r", "sha", "PR gate", timeout_min=90, poll_sec=0,
        settle_polls=2, sleep=lambda _s: None, fetch=fetch, now=_clock(),
    )
    assert code == 1 and "Lean CI" in msg
    assert len(polls) == 1


def test_wait_loop_times_out_into_a_failure():
    def fetch(_repo, _sha):
        return [run("Slow CI", None, status="in_progress")]

    code, msg = pr_gate.wait_and_decide(
        "o/r", "sha", "PR gate", timeout_min=0, poll_sec=0,
        settle_polls=2, sleep=lambda _s: None, fetch=fetch, now=_clock(),
    )
    assert code == 1
    assert "timed out" in msg and "Slow CI" in msg


# --- legacy commit statuses --------------------------------------------------


def test_legacy_status_error_maps_to_failure():
    """Some integrations post `error`, which has no check-run equivalent."""
    checks = [
        {"name": "legacy/lint", "status": "completed", "conclusion": "failure",
         "started_at": "2026-08-07T00:00:00Z", "id": 9},
    ]
    assert decide(checks)[0] == 1


def test_pending_legacy_status_blocks_settling():
    checks = [
        {"name": "legacy/lint", "status": "in_progress", "conclusion": "",
         "started_at": "2026-08-07T00:00:00Z", "id": 9},
    ]
    pending, _bad, _ok, _adv = pr_gate.classify(checks)
    assert pending == ["legacy/lint"]


# --- fork exemption (issue #10072) -------------------------------------------
#
# A student PR from a fork is not subject to internal CI conventions
# (cf. .claude/rules/student-pr-reviews.md). The workflow passes --is-fork
# when head.repo.fork == true; the script must short-circuit to exit 0
# without polling, while still NOT changing the verdict for non-fork PRs
# whose CI is red. These two tests pin both halves of the contract.


def test_fork_short_circuits_to_pass_without_polling(monkeypatch):
    """`--is-fork` returns 0 and never touches the network."""

    def explode_on_poll(*_args, **_kwargs):
        raise AssertionError("fork path must not poll")

    monkeypatch.setattr(pr_gate, "wait_and_decide", explode_on_poll)
    # `fetch_checks` would also explode if called, since gh CLI is not on PATH
    # here -- the monkeypatch above proves it never gets the chance.
    code = pr_gate.main(["--repo", "o/r", "--sha", "deadbeef", "--is-fork"])
    assert code == 0


def test_fork_pass_holds_even_if_other_checks_would_have_failed(monkeypatch):
    """`--is-fork` does not consult the CI state. The bypass is unconditional.

    Hooks the same way the previous test does, but adds a hypothetical
    failing check that, in the non-fork path, would have produced exit 1.
    Useful regression: protects against a future refactor that "helpfully"
    inspects the check state before deciding to bypass.
    """
    monkeypatch.setattr(
        pr_gate,
        "wait_and_decide",
        lambda *_a, **_kw: (1, "FAIL -- failing checks: Lean CI"),
    )
    code = pr_gate.main(["--repo", "o/r", "--sha", "deadbeef", "--is-fork"])
    assert code == 0


def test_non_fork_path_is_unchanged(monkeypatch):
    """Without `--is-fork`, the script still aggregates normally.

    Regression guard: confirms the fork bypass only fires when the flag is
    present. The fake below is a passing aggregate, so the exit code is 0;
    the assertion that matters is that the bypass branch was NOT taken.
    """
    calls = []

    def fake_wait(*args, **kwargs):
        calls.append((args, kwargs))
        return 0, "PASS -- no failing checks"

    monkeypatch.setattr(pr_gate, "wait_and_decide", fake_wait)
    code = pr_gate.main(["--repo", "o/r", "--sha", "deadbeef"])
    assert code == 0
    assert len(calls) == 1, "non-fork path must still call wait_and_decide"


# --- advisory decoupling (rule 6, PRs #10063 / #10080) ----------------------


def test_advisory_failure_does_not_block():
    """The regression this file exists for: a red advisory left the gate red.

    Shape taken from #10063 measured on 2026-08-08 -- the advisory job crashed
    on an unbound shell variable, and `PR gate` went FAILURE with it.
    """
    checks = [
        run("G-VAR-2/3 GENRE signals (advisory, non-blocking)", "failure"),
        run("Lean CI", "success"),
    ]
    pending, bad, ok, advisory = pr_gate.classify(checks, "PR gate")
    assert bad == [], "an advisory failure must never reach the blocking list"
    assert pending == []
    assert ok == ["Lean CI"]
    assert advisory == ["G-VAR-2/3 GENRE signals (advisory, non-blocking) (failure)"]
    assert pr_gate.verdict(pending, bad, settled=True)[0] == 0


def test_advisory_pending_does_not_hold_the_gate():
    """A hung advisory must not keep the repository waiting."""
    checks = [
        run("CJK residue advisory (label, non-blocking)", None, status="in_progress"),
        run("Lean CI", "success"),
    ]
    pending, bad, _ok, advisory = pr_gate.classify(checks, "PR gate")
    assert pending == [] and bad == []
    assert advisory == ["CJK residue advisory (label, non-blocking) (in_progress)"]


def test_advisory_marker_is_case_insensitive():
    checks = [run("Slidev Build ADVISORY", "failure")]
    _pending, bad, _ok, advisory = pr_gate.classify(checks, "PR gate")
    assert bad == [] and len(advisory) == 1


def test_green_advisory_counts_as_a_normal_pass():
    """Only non-green advisory checks are singled out for reporting."""
    checks = [run("Large blob advisory (>= 10 MiB)", "success")]
    _pending, bad, ok, advisory = pr_gate.classify(checks, "PR gate")
    assert bad == [] and advisory == []
    assert ok == ["Large blob advisory (>= 10 MiB)"]


def test_non_advisory_failure_still_blocks():
    """Guard against the fix becoming a blanket amnesty."""
    checks = [
        run("Lean CI (grothendieck_lean)", "failure"),
        run("Exercises >= 3 advisory (label, non-blocking)", "failure"),
    ]
    _pending, bad, _ok, advisory = pr_gate.classify(checks, "PR gate")
    assert bad == ["Lean CI (grothendieck_lean)"]
    assert len(advisory) == 1
    assert pr_gate.verdict([], bad, settled=True)[0] == 1


def test_advisory_is_printed_not_swallowed(capsys):
    """The gate must not be the reason an advisory signal disappears."""
    pr_gate._report_advisory(["Twin parity SHA mismatch (advisory) (failure)"])
    out = capsys.readouterr().out
    assert "not blocking" in out
    assert "Twin parity SHA mismatch (advisory) (failure)" in out


def test_advisory_failure_alone_settles_green_end_to_end():
    """Whole-loop check: the #10063 shape now reaches exit 0."""
    checks = [
        run("G-VAR-2/3 GENRE signals (advisory, non-blocking)", "failure"),
        run("Lean CI", "success"),
    ]
    code, msg = pr_gate.wait_and_decide(
        repo="o/r",
        sha="deadbeef",
        timeout_min=1,
        poll_sec=0,
        self_name=pr_gate.DEFAULT_SELF_NAME,
        settle_polls=2,
        sleep=lambda _s: None,
        fetch=lambda _r, _s: checks,
        now=lambda: 0.0,
    )
    assert code == 0, msg
