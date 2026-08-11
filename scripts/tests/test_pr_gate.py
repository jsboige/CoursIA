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


def test_skipped_and_neutral_are_green():
    checks = [run("A", "skipped", rid=1), run("B", "neutral", rid=2)]
    assert decide(checks)[0] == 0


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


def test_the_9858_outage_shape_fails():
    """Replay of the #9858 outage (Actions 2026-08-06): 175 PRs merged while
    the per-PR gates never ran -- check-runs sat at `queued`/`in_progress` with
    no conclusion, or reported `completed` with a null conclusion (runner died).

    A gate that verdicts PASS on this shape is the exact failure mode that let
    175 PRs through unpoliced. Both sub-cases must land in `pending` (classify:
    `status in STATUS_PENDING or not conclusion`) and the verdict must FAIL --
    the bias-to-fail rule (rule 1) applied to the outage, parallel to the #9762
    replay above (which pins the failure-side, this pins the no-verdict-side).
    """
    # Sub-case 1: runner never picked the check up (queued / in_progress, null).
    queued = [
        run("ci / Lean CI (grothendieck_lean)", None, status="queued", rid=1),
        run("proof-integrity / Proof integrity", None, status="in_progress", rid=2),
        run("CodeQL", "success", rid=3),
    ]
    code, msg = decide(queued)
    assert code == 1, "queued/null checks (outage) must block, not pass"
    assert "Lean CI" in msg

    # Sub-case 2: runner died mid-run -- `completed` with a null conclusion.
    died = [
        run("ci / Lean CI (grothendieck_lean)", None, status="completed", rid=4),
        run("proof-integrity / Proof integrity", "success", rid=5),
    ]
    code, msg = decide(died)
    assert code == 1, "completed/null-conclusion (runner died) must block"
    assert "Lean CI" in msg


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


def test_short_header_trio_job_was_retired_by_c10330():
    """Incident #10104 -- the short-header trio job was advisory by design
    (exit 0, label-only, see variation-tag-guard.yml comment) but its job name
    originally lacked the `advisory` marker. A lingering in_progress check-run
    then made pr_gate.py wait on it until the 90-min timeout, blocking every PR
    whose body lacked the Quoi/Preuve/Perimetre trio (e.g. #10104 itself).

    c.10330 / PR retired the job entirely: the convention was voluntarily not
    promulgated (cf. issue title "pas une nouvelle regle"), so the label
    `variation-short-header-missing` flagged 69 % of PRs without ever
    discriminating anything. The marker invariant from #10104 is no longer
    load-bearing (no job means no risk of a stuck gate), but the contract on
    `is_advisory` is preserved: if someone re-cables a job with the same name
    pattern, the marker MUST come back with it, otherwise #10104 resurrects.
    """
    # The retired job name still routes through is_advisory() if ever seen on a
    # check-run (e.g. from a stale in-progress hung-run). Pin the marker:
    job_name = "Check short-header trio (advisory, label, non-blocking, #9861)"
    assert pr_gate.is_advisory(job_name), (
        "if the short-header job is ever re-cabled, its name MUST carry the "
        "advisory marker to prevent a recurrence of the #10104 stuck-gate"
    )
    # And the resulting pending check must not hold the gate:
    checks = [run(job_name, None, status="in_progress"), run("Lean CI", "success")]
    pending, bad, _ok, advisory = pr_gate.classify(checks, "PR gate")
    assert pending == [] and bad == [], "a hung short-header advisory must not hold the gate"
    assert advisory == [f"{job_name} (in_progress)"]


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


# --- delivery canary (rule 8, PR #10036 / #9858) -----------------------------
#
# A settled set containing NONE of the always-on workflows means CI was never
# created for the PR -- the 2026-08-06 (#9858) partial-delivery failure mode,
# where pr-gate ran and stabilised on a near-empty bouquet while the rest of CI
# sat uncreated (175 PRs merged unpoliced). The canary refuses to pass on that
# shape. The always-on roster is DERIVED from .github/workflows (jobs whose
# workflow fires on pull_request with no paths: filter); judging on observed
# NAMES (not the ok bucket) so advisory always-on jobs still count as delivered.

# A small, stable roster for the pure-logic tests (independent of the live
# workflows dir, which drifts as workflows are added -- exactly why the real
# gate derives it rather than baking it in).
_CANARY = frozenset(
    {"No catalog changes on feature branch", "Gitleaks secret scanner"}
)


def test_empty_set_means_platform_did_not_deliver():
    """Replaces the old `test_no_checks_at_all_passes`.

    An empty settled set is indistinguishable from a partial delivery, so rule 1
    (bias to fail) says refuse rather than pass. The pure `verdict`/`decide`
    layer still returns PASS on empty (delivery is a wait-loop concern), but the
    armed canary makes the *gate* exit 1 -- which is what closes the #9858 hole.
    """
    code, msg = pr_gate.wait_and_decide(
        "o/r", "sha", "PR gate", timeout_min=1, poll_sec=0, settle_polls=1,
        always_on_jobs=_CANARY,
        sleep=lambda _s: None, fetch=lambda _r, _s: [], now=lambda: 0.0,
    )
    assert code == 1, msg
    assert "did not deliver" in msg


def test_canary_passes_when_an_always_on_is_present():
    """A healthy PR surfaces at least one always-on check -> delivered."""
    checks = [
        run("No catalog changes on feature branch", "success", rid=1),
        run("Lean CI", "success", rid=2),
    ]
    code, msg = pr_gate.wait_and_decide(
        "o/r", "sha", "PR gate", timeout_min=1, poll_sec=0, settle_polls=1,
        always_on_jobs=_CANARY,
        sleep=lambda _s: None, fetch=lambda _r, _s: checks, now=lambda: 0.0,
    )
    assert code == 0, msg


def test_canary_counts_a_red_advisory_always_on_as_delivered():
    """The trap (acceptance criterion 2): an advisory always-on diverted out of
    `ok` by rule 6 must STILL count as delivered. Judging on `ok` would falsely
    flag a healthy PR whose only always-on happened to be a red advisory.
    """
    assert pr_gate.platform_delivered(
        [run("Gitleaks secret scanner", "success")], _CANARY
    ) is True
    # Same job, failing -- still present by NAME, so still delivered.
    assert pr_gate.platform_delivered(
        [run("Gitleaks secret scanner", "failure")], _CANARY
    ) is True


def test_canary_fires_on_partial_delivery_pr_gate_only():
    """The #9858 partial-delivery hole: pr-gate ran, nothing else did.

    pr-gate is excluded from the roster (the gate never canaries itself), so a
    bouquet of only the gate's own check is an undelivered PR.
    """
    checks = [run("PR gate", "success", rid=1)]
    assert pr_gate.platform_delivered(checks, _CANARY) is False
    code, msg = pr_gate.wait_and_decide(
        "o/r", "sha", "PR gate", timeout_min=1, poll_sec=0, settle_polls=1,
        always_on_jobs=_CANARY,
        sleep=lambda _s: None, fetch=lambda _r, _s: checks, now=lambda: 0.0,
    )
    assert code == 1 and "did not deliver" in msg


def test_canary_fires_when_only_non_always_on_checks_ran():
    """Path-filtered checks ran but no always-on did -> platform degraded."""
    checks = [run("ci / Lean CI (grothendieck_lean)", "success", rid=1)]
    assert pr_gate.platform_delivered(checks, _CANARY) is False


def test_canary_is_disabled_when_roster_is_empty():
    """An unreadable/empty roster must not block every PR (safe-open).

    derive_always_on_jobs returns empty when the dir is missing or YAML fails;
    the gate then behaves exactly as before rule 8. Confirming that contract
    here, against the real repo so the derivation itself is exercised.
    """
    jobs = pr_gate.derive_always_on_jobs(
        "this/does/not/exist", pr_gate.DEFAULT_SELF_NAME
    )
    assert jobs == frozenset()
    code, msg = pr_gate.wait_and_decide(
        "o/r", "sha", "PR gate", timeout_min=1, poll_sec=0, settle_polls=1,
        always_on_jobs=None,
        sleep=lambda _s: None, fetch=lambda _r, _s: [], now=lambda: 0.0,
    )
    assert code == 0, "disabled canary must not turn an empty set into a failure"


def test_derive_always_on_reads_real_workflows_and_excludes_self():
    """Acceptance criterion 1: the roster is derived, not hardcoded, and never
    includes the gate's own job. Run against the live .github/workflows.
    """
    jobs = pr_gate.derive_always_on_jobs()
    assert len(jobs) >= 6, "expected at least the catalog/secret/regression/" \
        "stale-base/variation always-on jobs from the real repo"
    assert all(pr_gate.DEFAULT_SELF_NAME not in j for j in jobs), \
        "the gate must never canary itself"
    # A job known to be always-on (catalog-guard, no paths filter) is present.
    assert "No catalog changes on feature branch" in jobs


def test_fork_short_circuit_skips_the_canary(monkeypatch):
    """Acceptance criterion 4: a fork PR never reaches the canary.

    Forks short-circuit in main() before wait_and_decide is ever called, so even
    a would-be-firing canary cannot touch a student PR.
    """
    def explode(*_a, **_kw):
        raise AssertionError("fork path must not poll or canary")
    monkeypatch.setattr(pr_gate, "wait_and_decide", explode)
    monkeypatch.setattr(pr_gate, "derive_always_on_jobs", explode)
    code = pr_gate.main(["--repo", "o/r", "--sha", "deadbeef", "--is-fork"])
    assert code == 0


# --- stale rollup recovery (issue #10435, acceptance 3) ----------------------
#
# The defect #10435 documents is structural at the *workflow trigger* level
# (pr-gate.yml never re-aggregates after a guard it depends on flips green, so
# a PR stays BLOCKED until a manual `gh run rerun`). But the recovery mechanism
# a rerun exploits is a PROPERTY of classify/verdict that must not silently
# change: a required check that was in flight (pending) on the first rollup
# must, on the re-rollup, be seen as settled-green and flip the verdict from
# FAIL (timed out) to PASS -- WITHOUT a new commit push. This pins exactly that
# scenario, which is what makes the manual rerun (and any future workflow_run
# trigger) sufficient to unblock the PR.


def test_inflight_required_check_settles_to_pass_on_reroll():
    """A required check pending on rollup 1 settles green on rollup 2 -> PASS.

    Mirrors the #10435 scenario: `Require Grain tag` (a required, non-advisory
    guard) was IN_PROGRESS when the first PR-gate run aggregated, so the run
    either timed out on it or (more commonly, since the tag was genuinely
    missing) saw it fail. After the tag is edited into the body, the guard
    re-runs and completes `success`. A `gh run rerun` of PR gate re-aggregates
    the CURRENT check set: the same guard name now reports conclusion=success,
    and classify must route it to `ok`, yielding verdict PASS -- no commit push
    intervening.
    """
    name = "Require Grain tag (block on absent, ..."
    inflight = run(name, conclusion=None, status="in_progress", rid=10)
    settled_green = run(name, conclusion="success", status="completed", rid=11)

    # Rollup 1: guard still in flight -> pending -> verdict timed out (FAIL).
    pending1, bad1, ok1, _adv = pr_gate.classify([inflight], pr_gate.DEFAULT_SELF_NAME)
    assert pending1 == [name] and not bad1 and not ok1
    code1, _msg1 = pr_gate.verdict(pending1, bad1, settled=False)
    assert code1 == 1

    # Rollup 2 (rerun, no new commit): same guard now completed+success -> ok.
    pending2, bad2, ok2, _adv = pr_gate.classify([settled_green], pr_gate.DEFAULT_SELF_NAME)
    assert not pending2 and not bad2 and ok2 == [name]
    code2, _msg2 = pr_gate.verdict(pending2, bad2, settled=True)
    assert code2 == 0
