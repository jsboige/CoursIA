#!/usr/bin/env python3
"""pr_gate.py -- the single requerrable check for `main` (issue #9819).

## Why this exists

`main` REQUIRES exactly one status check, and it is this one. Measured
firsthand 2026-08-25 (as `jsboige` -- the read returns 404 under `myia-ai-01`,
which is a question, not an absence):

    gh api repos/jsboige/CoursIA/branches/main/protection
        required_status_checks.contexts -> ["PR gate"]   strict -> false
        enforce_admins                  -> false
    gh api repos/jsboige/CoursIA/rulesets                   -> []

The paragraph below describes the state BEFORE this check was wired, and is
kept because it is the reason the design is what it is. It is no longer a
description of `main`: since #9819 landed, a PR whose `PR gate` is red reports
`BLOCKED`, not `UNSTABLE`.

Two consequences the wiring makes load-bearing, both measured under a deep
queue on 2026-08-25:

  - `PR gate` being required means that when it cannot render a verdict --
    queued behind ~2450 runs, or timed out at its 12-minute bound -- NOTHING
    merges, including PRs whose every other check is green. That is a
    deadlock, not slowness.
  - `enforce_admins: false` is the release valve: an admin can `gh pr merge
    --admin` when the verdict is unobtainable. It is the only one.

## The state this check was built for (2026-08-07)

At the time, a PR whose CI was red reported `UNSTABLE` (mergeable), never
`BLOCKED`. The
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

## Publication (#15693)

A verdict this script computes is worthless if only the job log carries it:
the surface a lane reads on a red PR is the required check's
`output.summary`, which measured `null` while the cause (`pr_gate.py`'s own
verdict string) lived only in the log -- 5/5 red PRs in the issue, plus a
re-measurement of #15724, #15720, #15718.

**The obvious mechanism does not work, and that is measured, not assumed.**
Writing `$GITHUB_STEP_SUMMARY` renders a summary on the run page but does
NOT populate the auto check-run's `output.summary`: on this file's own red
gate (run 34681884304) the step summary renders while
`gh api .../check-runs/<id> --jq .output.summary` returns `null`; the
SUCCESSFUL sweep job (103506691766) writes the same organ and is null too;
and a scan of 1098 `github-actions` check-runs over 40 main commits finds
ZERO with a non-null summary. Every check-run that does carry one was
created by the Checks API (POST) -- e.g. the shadow aggregator's
`fast-lane (ombre): *`. POSTing a twin bearing THIS required name is not an
option either: it lands in a foreign suite and GitHub ANDs the two, which is
why the stale-sweep re-runs the original run instead of posting beside it
(78 PRs blocked, #11519).

So the verdict is published on two surfaces: the step summary
(`write_step_summary`, the run page) and, for the check-run itself,
:func:`publish_check_run_output`, which PATCHes our own check-run's
`output` in place -- the only write that reaches the required leg, and one
that needs a GitHub App token (a PAT is refused), hence the job's own.

The FAIL message separates three states with opposite repairs: real reds
("failing checks"), checks that never concluded (cancelled/timed_out/stale/
startup_failure -- nothing was measured about the code, so rerun), and the
DWELL floor (head timestamp + earliest lift time, no action). Advisory
non-green checks are listed as not blocking. The fail-closed RULES are
untouched: an unconcluded check still fails the gate (rule 1/3), only the
message stops misattributing the repair. The `workflow_run` sweep path keeps
POSTing its own check-run with its output fields (`--post-check-run`),
exactly as before.

## Design rules that matter

1. **Bias to fail.** Timeout, API error, or a check with no verdict => exit 1.
   A gate that passes when it does not know is not a gate. This is deliberate
   and is the single most important property of the file. #13510 refines the
   RENDERING, not the rule: a timeout with nothing red (starvation, not
   failure) still exits 1 but cancels its own run, so the leg concludes
   CANCELLED -- the PR stays BLOCKED (never passes on unknown), yet the log
   does not claim a failure that never happened and the stale-sweep re-drives
   it like any other cancelled gate leg (#11862).
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
6. **Advisory checks are reported, never blocking.** A job whose name says
   `advisory` is by construction a signal-carrier: its verdict belongs in a
   label, not in a merge decision (7 of the 53 jobs in `.github/workflows`
   are named that way, 5 of them spelling out "label, non-blocking"). Because
   this gate aggregates *whatever CI exists*, letting an advisory failure
   through would silently promote every advisory guard into a hard gate --
   the exact opposite of what its author declared. Measured on 2026-08-08:
   #10063 and #10080 were both `BLOCKED` with `PR gate -> FAILURE`, and in
   #10063's case the advisory job had merely crashed on an unbound shell
   variable before emitting any verdict at all. An advisory check therefore
   never enters `pending` (a hung one must not hold the repo) nor `bad`; it
   is listed separately and printed, so the signal stays visible in the log
   while the decision stays clean.
7. **Fork PRs short-circuit to PASS.** Issue #10072 -- student PRs from a
   fork have no internal convention to police, and `.claude/rules/student-pr-
   reviews.md` explicitly allows admin merges on red CI for that class of PR.
   The workflow passes `--is-fork` for `head.repo.fork == true`; the script
   then skips polling entirely and reports PASS. The "verdict on every PR"
   invariant is preserved (GitHub sees a real success line) without ever
   deciding the student's CI.
8. **Delivery canary.** A settled check set containing NONE of the always-on
   workflows means CI was never created for the PR -- the 2026-08-06 (#9858)
   partial-delivery failure mode, where `pr-gate` ran and stabilised on a near-
   empty bouquet while the rest of CI sat uncreated. The always-on roster is
   DERIVED from `.github/workflows` (jobs whose workflow fires on `pull_request`
   with no `paths:` filter), never hardcoded; the canary fires only at settle
   time and judges on observed NAMES so advisory always-on jobs (diverted out of
   `ok` by rule 6) still count as delivered. An empty set is no longer a pass:
   it is indistinguishable from a partial delivery, and rule 1 says refuse.

Exit codes: 0 = every settled check is non-failing AND the platform delivered
            its always-on bouquet (or the PR is from a fork, out-of-scope per
            #10072).
            1 = at least one failure, the state could not be established, or the
            platform never delivered the PR (#9858 canary).

Run locally against any PR head:

    python scripts/pr_gate.py --repo jsboige/CoursIA --sha <head-sha> --timeout-min 1
    python scripts/pr_gate.py --repo jsboige/CoursIA --sha <head-sha> --is-fork
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Iterable, Sequence

try:  # Used only by the rule-8 delivery canary (derive_always_on_jobs).
    import yaml  # type: ignore
except ImportError:  # pragma: no cover - environment problem, canary self-disables
    yaml = None  # type: ignore

# A check that reached one of these has produced a verdict we accept.
CONCLUSION_OK = frozenset({"success", "neutral", "skipped"})

# A check that reached one of these has produced a verdict we reject.
# `cancelled` is here on purpose (see rule 3 in the module docstring): after
# de-duplication it can no longer mean "superseded", only "no verdict".
CONCLUSION_BAD = frozenset(
    {"failure", "timed_out", "cancelled", "action_required", "stale", "startup_failure"}
)

# Four of the six CONCLUSION_BAD members mean the check MEASURED NOTHING about
# the code (cancelled by runner famine, timed out, stale, never started). The
# other two (failure, action_required) are real reds. #15693: the published
# verdict separates the two -- "failing checks: X" on a cancelled X asserts
# something false about the code and invites fixing what is not broken
# (measured on #15548: the lane investigated an infra famine while its real
# blocker, already repaired 18 min earlier, went unread). The fail-closed RULE
# is untouched: an unconcluded check still fails the gate (rule 1/3); only the
# MESSAGE stops lying about which gesture repairs it (rerun, not a code fix).
CONCLUSION_UNCONCLUDED = frozenset(
    {"cancelled", "timed_out", "stale", "startup_failure"}
)

DEFAULT_SELF_NAME = "PR gate"

# Substring that marks a check as advisory (see rule 6). Matched
# case-insensitively anywhere in the check name, because GitHub renders a job as
# "<workflow> / <job>" and the marker sits in the job half. This is the
# convention already in use across `.github/workflows` -- e.g. "CJK residue
# advisory (label, non-blocking)" -- so no separate registry has to be kept in
# sync with the workflows.
ADVISORY_MARKER = "advisory"


def is_advisory(name: str, workflow_name: str = "") -> bool:
    """True when the check declares itself non-blocking by name (rule 6).

    Two signals, both case-insensitive substring matches against the
    ADVISORY_MARKER:

    - the *job* name (`name`) -- the conventional path; ~30 of the
      repository's advisory workflows carry ``advisory`` in the job name;
    - the *workflow* name (`workflow_name`) -- catches the three workflows
      whose workflow name carries the marker but whose job name does not
      (measured 2026-08-25: ``Bash Syntax Advisory`` / ``syntax-check``,
      ``machine-dep-timing-advisory`` / ``machine-dep-timing``,
      ``Translation parity gate (advisory)`` / ``parity``). Without this
      second path, the gate misclassifies these as blocking on every PR
      -- PRs #12524 and #12783 were stuck open 44h/9h on this defect
      before the fix.

    The REST check-runs API does not surface ``workflow_name``; the script
    therefore derives it from the on-disk workflow YAMLs (see
    ``derive_advisory_jobs``). The fallback to ``name`` alone is preserved
    so unit tests that pass only ``name`` keep working.
    """
    low = (name or "").lower()
    if ADVISORY_MARKER in low:
        return True
    return ADVISORY_MARKER in (workflow_name or "").lower()


# Where the always-on workflow jobs are derived from (rule 8 canary). Resolved
# relative to the repo root: this script lives in scripts/, so its parent is the
# repository root that holds .github/workflows.
DEFAULT_WORKFLOWS_DIR = str(Path(__file__).resolve().parent.parent / ".github" / "workflows")

# Plancher de temps entre le dernier commit de tete et le merge (mandat user
# 2026-09-07). Importe tard et de facon defensive : `pr_gate.py` est le seul
# check requis de `main`, et une ImportError ici bloquerait 100 % des PRs.
# Absent -> le plancher est simplement inapplicable, jamais un refus.
try:  # pragma: no cover - chemin d'import
    from ci import merge_dwell as _merge_dwell
except ImportError:  # pragma: no cover
    try:
        from scripts.ci import merge_dwell as _merge_dwell  # type: ignore
    except ImportError:
        _merge_dwell = None  # type: ignore


def _norm(name: str) -> str:
    """Normalise a check/job name for the delivery canary: lowercase, collapse
    whitespace. Matching is on observed NAMES (the input to `classify`), never on
    the bucket a check landed in, because some always-on jobs are themselves
    advisory (rule 6) and would be diverted out of `ok`.
    """
    return " ".join((name or "").lower().split())


def derive_always_on_jobs(
    workflows_dir: str = DEFAULT_WORKFLOWS_DIR, self_name: str = DEFAULT_SELF_NAME
) -> frozenset[str]:
    """Job names produced by workflows that run on EVERY pull_request (no
    `paths:` filter), excluding this gate's own job.

    These are the canary: a healthy PR always surfaces at least one of them, so
    a settled check set containing NONE means the platform never delivered the
    PR -- the 2026-08-06 (#9858) partial-delivery failure mode, where `pr-gate`
    ran and stabilised while the rest of CI was never created.

    The list is DERIVED, never hardcoded (rule 8 / acceptance criterion 1): a
    baked-in list rots the moment a workflow is added, and a rotten canary is
    worse than none because it blocks with false confidence. Reading the trigger
    from the workflows themselves is what keeps it honest.

    Returns an empty set when the directory is missing, YAML is unavailable, or a
    file fails to parse -- the caller treats an empty set as "canary disabled"
    rather than "nothing is ever-on", because weaponising an unreadable state
    against every PR would deadlock the repository (rule 1's bias-to-fail applies
    to an unreadable VERDICT, not to an unreadable canary roster).
    """
    if yaml is None:
        return frozenset()
    root = Path(workflows_dir)
    if not root.is_dir():
        return frozenset()

    self_norm = _norm(self_name)
    jobs: set[str] = set()
    for yml in sorted(root.glob("*.yml")):
        try:
            data = yaml.safe_load(yml.read_text(encoding="utf-8"))
        except (OSError, yaml.YAMLError):
            continue
        if not isinstance(data, dict):
            continue

        triggers = data.get("on", data.get(True))  # PyYAML may parse `on:` as True
        pr = _pull_request_trigger(triggers)
        if pr is None:
            continue
        # `pr` is truthy when pull_request fires; a dict with `paths`/`paths-ignore`
        # means the workflow is path-filtered and does NOT run on every PR.
        if isinstance(pr, dict) and ("paths" in pr or "paths-ignore" in pr):
            continue

        for jname in _workflow_job_names(data):
            if _norm(jname) == self_norm:
                continue  # never let the gate canary itself
            jobs.add(jname)

    return frozenset(jobs)


def derive_advisory_jobs(workflows_dir: str = DEFAULT_WORKFLOWS_DIR) -> frozenset[str]:
    """Job names produced by workflows whose workflow-level ``name:`` carries
    the ADVISORY_MARKER (case-insensitive). Scans every workflow in the
    directory regardless of trigger or ``paths:`` filter, so a path-filtered
    advisory (rare but legal -- e.g. ``machine-dep-timing-advisory`` only
    runs on notebook-touched PRs) is still picked up.

    Used by ``is_advisory`` to recover the three workflows whose *job* name
    does not carry the marker even though the *workflow* does (the case
    measured on 2026-08-25 that left PRs #12524 and #12783 BLOCKED on the
    PR gate 44h/9h).

    Same robustness contract as ``derive_always_on_jobs``: an unreadable
    state returns an empty set rather than weaponising the gate against
    every PR.
    """
    if yaml is None:
        return frozenset()
    root = Path(workflows_dir)
    if not root.is_dir():
        return frozenset()
    jobs: set[str] = set()
    for yml in sorted(root.glob("*.yml")):
        try:
            data = yaml.safe_load(yml.read_text(encoding="utf-8"))
        except (OSError, yaml.YAMLError):
            continue
        if not isinstance(data, dict):
            continue
        wf_name = (data.get("name") or "").lower()
        if ADVISORY_MARKER not in wf_name:
            continue
        jobs.update(_workflow_job_names(data))
    return frozenset(jobs)


def _pull_request_trigger(triggers: object) -> object:
    """Extract the `pull_request` trigger value from a workflow `on:` field.

    Returns None when pull_request is absent, otherwise the trigger's value
    (True/a list/a dict). Shields `derive_always_on_jobs` from the three YAML
    shapes `on:` can take (scalar, sequence, mapping).
    """
    if isinstance(triggers, str):
        return True if triggers == "pull_request" else None
    if isinstance(triggers, list):
        return "pull_request" if "pull_request" in triggers else None
    if isinstance(triggers, dict):
        return triggers.get("pull_request")
    return None


def _workflow_job_names(data: dict) -> list[str]:
    """The check-run names a workflow produces: each job's `name:` or its key.

    GitHub renders an Actions job's check-run `name` as the job's own `name`
    field (or the job key when `name:` is absent). Workflows with a top-level
    `name:` and a single job render as that job name; matrix/reusable jobs keep
    the job name verbatim. Matching on these derived names is therefore faithful
    to what the API returns under `check-runs[].name`.
    """
    names: list[str] = []
    for jkey, jval in (data.get("jobs") or {}).items():
        if isinstance(jval, dict):
            names.append(jval.get("name") or jkey)
    return names


def platform_delivered(checks: Sequence[dict], always_on_jobs: frozenset[str]) -> bool:
    """True when at least one always-on job is represented among observed checks.

    The delivery canary (rule 8). Judges on observed NAMES -- the raw input to
    `classify` -- and deliberately NOT on the `ok` bucket: at least two
    always-on jobs are themselves advisory (e.g. the repo-size advisory and
    former short-header trio, both advisory-diverted) and `classify` diverts a
    non-green advisory out of `ok` into `advisory`. Judging `ok` would therefore
    flag a healthy PR whose only always-on happened to be a red advisory.
    Judging names sidesteps the trap: a delivered advisory job is still present
    by name. The short-header job was retired by c.10330 / PR and is no longer
    part of the always-on set; this comment is kept as a trace for reviewers.

    A check matches an always-on job when the normalised names are equal, or when
    the observed name ends with " / <job>" (GitHub's "<workflow> / <job>"
    rendering for multi-job workflows).
    """
    observed = {_norm(c.get("name") or "") for c in checks}
    for job in always_on_jobs:
        target = _norm(job)
        if not target:
            continue
        for name in observed:
            if name == target or name.endswith(" / " + target):
                return True
    return False


def _canary_verdict(
    checks: Sequence[dict], always_on_jobs: frozenset[str]
) -> tuple[int, str] | None:
    """Rule 8: refuse to PASS when the platform did not deliver.

    Returns (1, message) when the canary fires, None when it is disabled (empty
    roster) or satisfied (delivery observed). Only consulted at settle time by
    `wait_and_decide`, so it inherits the `settle_polls` grace period -- a
    freshly-opened PR has that many consecutive quiet polls worth of runway for
    Actions to create its check-runs before the canary draws a conclusion.
    """
    if not always_on_jobs:
        return None
    if platform_delivered(checks, always_on_jobs):
        return None
    sample = ", ".join(sorted(always_on_jobs)[:3])
    tail = " ..." if len(always_on_jobs) > 3 else ""
    return 1, (
        "FAIL -- platform did not deliver: no always-on check observed "
        f"(expected one of: {sample}{tail}). A settled set with none of the "
        "always-on workflows means CI was never created for this PR (#9858)."
    )


class GateError(RuntimeError):
    """Raised when the check state cannot be established. Always fatal."""


# --- pure decision layer (no network; this is what the unit tests pin) -------


def dedupe_latest(checks: Sequence[dict]) -> list[dict]:
    """Keep only the most recent entry per check name.

    GitHub leaves superseded and re-run attempts visible on the same SHA. Judging
    all of them makes a benign concurrency cancellation indistinguishable from a
    real failure. Ordering key is `started_at` then `id`, both monotonic per name;
    entries missing both keep their input order as a last resort.

    PREMISE -- the rendered check-run `name` identifies the job uniquely. This
    premise is enforced by `scripts/ci/check_unique_check_run_names.py` and its
    CI guard (workflow `unique-check-run-names-guard.yml`). When the premise
    fails, the fold collapses two distinct workflows' verdicts onto the same
    bucket and the most-recent wins regardless of consequence: a real FAIL
    can be swallowed under a sibling SUCCESS that started later (#11869,
    measured on `cf968dcf`: `notebook-papermill-ratchet` FAILed at 22:12:53Z
    under two sibling successes at 22:08:46Z and 22:13:25Z -- PR gate
    reported PASS). Do NOT extend this function to dedupe by (workflow, name)
    as a substitute for fixing the name collision -- the unit of judgement
    is the JOB, and the job's name must identify it on its own.

    NOTE: the monotonicity premise holds at the check-run level
    (`commits/<sha>/check-runs` — a rerun creates a fresh entry, larger id AND
    started_at), NOT at the `actions/runs` level, where an attempt=2 of an old
    run keeps a smaller id while starting later. dedupe_latest is only fed by
    the former (#11416).
    """
    best: dict[str, tuple[tuple, dict]] = {}
    for index, check in enumerate(checks):
        name = check.get("name") or ""
        key = (check.get("started_at") or "", check.get("id") or 0, index)
        current = best.get(name)
        if current is None or key >= current[0]:
            best[name] = (key, check)
    return [entry[1] for entry in best.values()]


def _pending_label(name: str, status: str, conclusion: str) -> str:
    """Render a pending constituent with its observed status/conclusion couple.

    #14976 acceptance 3: a STARVED message that names `X` without saying what X
    actually reported is indistinguishable from a real wedge. The frozen record
    that cost the 90-minute diagnosis on #14967 (`Detect notebook changes`
    [`in_progress/success`]) looked identical to a slow-but-alive check until
    the couple was printed.
    """
    return f"{name} [{status or 'none'}/{conclusion or 'none'}]"


def classify(
    checks: Sequence[dict],
    self_name: str = DEFAULT_SELF_NAME,
    advisory_jobs: frozenset[str] = frozenset(),
) -> tuple[list[str], list[str], list[str], list[str]]:
    """Split settled checks into (pending, bad, ok, advisory) name lists.

    `self_name` is excluded so the gate never waits on itself. Matching is a
    prefix test because GitHub renders a job inside a workflow as
    "<workflow> / <job>", and the gate is required under its workflow name.

    Advisory checks (rule 6) are diverted into their own list -- annotated with
    what they actually reported -- and never reach `pending` or `bad`. They are
    kept separate rather than merged into `ok` so a caller can print "advisory
    X failed" instead of silently rewriting a failure into a pass.

    `bad` entries carry their conclusion as a suffix ("name (conclusion)",
    #15693) so `verdict` can separate real reds from checks that never
    concluded without re-reading the check set.

    `advisory_jobs` is the roster of job names whose parent workflow carries
    the advisory marker but the job itself does not (e.g.
    ``machine-dep-timing`` -> ``machine-dep-timing-advisory``); the gate would
    otherwise misclassify them as blocking on every PR. Derived from the
    on-disk workflow YAMLs via ``derive_advisory_jobs``; tests that do not care
    pass the empty frozenset, which is the historical behaviour.

    Treatment of an IN_PROGRESS / QUEUED check (issue #10435, acceptance 2) --
    a *required* check still in flight is treated exactly like an advisory in
    flight: it lands in ``pending`` and the wait loop in ``wait_and_decide``
    keeps polling until it reaches a terminal conclusion. The verdict returned
    before the wait budget runs out is therefore "timed out waiting for
    <name>", not "FAIL -- failing checks" (see ``verdict``). This choice --
    bounded wait rather than re-queue or deferred verdict -- is what makes a
    stale rollup recoverable by a plain ``gh run rerun``: the next run re-polls,
    sees the now-terminal check, and settles. The defect #10435 documents is
    NOT that classify mishandles in-flight checks (it waits on them correctly)
    but that the *workflow trigger* never asks it to look again -- that trigger
    fix lives in pr-gate.yml, not here.

    #14976 nuance: `conclusion` is authoritative. A check-run can carry a
    terminal conclusion while `status` is still `in_progress` (frozen record,
    measured on #14967). Such a check is SETTLED by its conclusion -- never
    held in `pending` because of a stale status. `status` only decides when
    `conclusion` is null, and then the check is pending regardless (see
    ``_pending_label`` for why the observed couple is carried into the wait
    log and the starvation message).
    """
    pending: list[str] = []
    bad: list[str] = []
    ok: list[str] = []
    advisory: list[str] = []

    for check in dedupe_latest(checks):
        name = check.get("name") or "<unnamed>"
        if name == self_name or name.startswith(f"{self_name} /"):
            continue

        status = (check.get("status") or "").lower()
        conclusion = (check.get("conclusion") or "").lower()

        # `is_advisory` consults the job name (conventional path) AND, when the
        # job name alone does not match, the workflow-name roster (recover the
        # three workflows whose job name does not carry the marker even though
        # the workflow does). Both signals are substring checks against the
        # ADVISORY_MARKER -- case-insensitive.
        workflow_label = ""
        if name in advisory_jobs:
            workflow_label = "advisory"
        if is_advisory(name, workflow_label) or workflow_label:
            if conclusion not in CONCLUSION_OK:
                state = conclusion or status or "no verdict"
                advisory.append(f"{name} ({state})")
            else:
                ok.append(name)
            continue

        # #14976: conclusion is authoritative. A check-run can freeze at
        # `status=in_progress` while already carrying a terminal conclusion --
        # measured on #14967, `Detect notebook changes` sat at
        # `in_progress/success` 90 min past its own job's `completed_at`,
        # confirmed on two endpoints. The old status-first test (status
        # pending OR no conclusion) polled that green job until the budget
        # burned and verdicted STARVED on a PR where nothing was red. Status
        # only speaks when conclusion is null -- and then the check is pending
        # regardless of what `status` claims.
        if not conclusion:
            pending.append(_pending_label(name, status, conclusion))
        elif conclusion in CONCLUSION_OK:
            ok.append(name)
        elif conclusion in CONCLUSION_BAD:
            # #15693: carry the conclusion so `verdict` can separate real
            # reds from checks that never concluded (same annotation style
            # as the advisory list below -- the bare name loses exactly the
            # information the published message needs).
            bad.append(f"{name} ({conclusion})")
        else:
            # Unknown conclusion: bias to fail (rule 1). A conclusion GitHub
            # adds later must not silently become a pass.
            bad.append(f"{name} (unknown conclusion '{conclusion}')")

    return sorted(pending), sorted(bad), sorted(ok), sorted(advisory)


def _report_advisory(advisory: Sequence[str]) -> None:
    """Print non-green advisory checks. Never affects the exit code (rule 6).

    Printing is the whole point: the gate must not be the reason an advisory
    signal disappears. The label posted by the advisory workflow itself remains
    the durable carrier -- this line only keeps it visible in the gate's own log.
    """
    for entry in advisory:
        print(f"[pr-gate] advisory (not blocking): {entry}", flush=True)


# Suffix added by `classify` to every CONCLUSION_BAD entry ("name
# (conclusion)"). Used by `_split_bad` to route each entry to its clause
# without re-reading the check set; anchored at end-of-string because the
# annotation is always the LAST parenthesised group of the entry.
_UNCONCLUDED_SUFFIX_RE = re.compile(
    r" \((?:cancelled|timed_out|stale|startup_failure)\)$"
)


def _split_bad(bad: Sequence[str]) -> tuple[list[str], list[str]]:
    """Split annotated `bad` entries into (real reds, never-concluded).

    Real reds are `failure`/`action_required` (and unknown conclusions, which
    rule 1 refuses) -- the lane has code work. Never-concluded are the four
    CONCLUSION_UNCONCLUDED members -- nothing was measured about the code and
    the repair is a rerun (#15693 three-state refinement).
    """
    failed: list[str] = []
    unconcluded: list[str] = []
    for entry in bad:
        if _UNCONCLUDED_SUFFIX_RE.search(entry):
            unconcluded.append(entry)
        else:
            failed.append(entry)
    return failed, unconcluded


def verdict(pending: Sequence[str], bad: Sequence[str], settled: bool) -> tuple[int, str]:
    """Final decision. Returns (exit_code, human message).

    `settled` is False when the wait loop ran out of time. Unsettled is a
    failure even with zero bad checks: we do not know, therefore we refuse.

    #13510: a starvation (still-pending constituents, nothing red) is marked
    `STARVED` in the message -- the exit code stays 1 (rule 1: never pass on
    unknown), but the driver renders it as CANCELLED, not FAILURE, so the
    stale-sweep re-drives the leg instead of a human reading a red lie.

    #14976 acceptance 4: each pending constituent renders as ``name [status/
    conclusion]`` (see ``_pending_label``), so a green-but-wedged record
    (`Detect notebook changes [in_progress/success]`) is distinguishable from
    a slow-but-alive one. The message also names the repair gesture -- rerun
    the CHILD run carrying the frozen check-run, never the aggregator gate --
    because that is what actually clears the wedge (#14967 measured it).

    Note (#11751): the wait loop now re-reads the check set one last time at
    the deadline; an empty `pending` AND empty `bad` at that point is treated
    as `settled=True` BEFORE this function is reached, so this `not settled`
    branch with an empty `pending` should be unreachable in practice. The
    diagnostic message no longer prints `(none listed)` -- it now states the
    case explicitly, so a regression that re-introduces the phantom FAIL does
    not look like a benign display issue.
    """
    if bad:
        # #15693: one FAIL prefix, two clauses with OPPOSITE repairs. A real
        # red names the check under "failing checks" (the historical phrase --
        # greppable, and what the log annotation has carried since #15472).
        # A check that never concluded is named separately with its repair
        # gesture: "failing checks: X" on a cancelled X told #15548's lane
        # its code was broken when the runner famine had eaten the verdict.
        failed, unconcluded = _split_bad(bad)
        parts = []
        if failed:
            parts.append("failing checks: " + ", ".join(failed))
        if unconcluded:
            parts.append(
                "checks that never concluded (rerun the run -- this is not "
                "a code failure): " + ", ".join(unconcluded)
            )
        return 1, "FAIL -- " + "; ".join(parts)
    if not settled:
        if pending:
            return 1, (
                "STARVED -- timed out waiting for: " + ", ".join(pending)
                + " -- a constituent showing a terminal conclusion above is "
                "wedged, not slow: rerun its CHILD run (gh run rerun <id>), "
                "never the gate (#14976)"
            )
        return 1, (
            "FAIL -- timed out with empty wait set (gate bug, see #11751)"
        )
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
            text=True, encoding="utf-8", errors="replace",
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


def _gh_api_post(path: str, fields: dict[str, str]) -> dict:
    """Call `gh api -X POST <path>` with one `-f key=value` per field.

    Mirror of :func:`_gh_api` for the Checks-API writes the re-aggregation path
    needs (#10433 item-1). Any failure is fatal to the caller (rule 1); the
    orchestrator wraps it so a POST failure never flips a verdict.
    """
    cmd = ["gh", "api", "-X", "POST", path]
    for key, value in fields.items():
        cmd += ["-f", f"{key}={value}"]
    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True, encoding="utf-8", errors="replace",
            check=False,
        )
    except FileNotFoundError as exc:  # pragma: no cover - environment problem
        raise GateError(f"gh CLI not available: {exc}") from exc

    if completed.returncode != 0:
        raise GateError(
            f"gh api -X POST {path} failed (exit {completed.returncode}): "
            f"{completed.stderr.strip()[:400]}"
        )
    body = completed.stdout.strip()
    if not body:
        return {}
    try:
        return json.loads(body)
    except json.JSONDecodeError as exc:
        raise GateError(f"gh api -X POST {path} returned non-JSON: {exc}") from exc


def _gh_api_patch(path: str, fields: dict[str, str]) -> dict:
    """Call `gh api -X PATCH <path>` with one `-f key=value` per field.

    Same contract as :func:`_gh_api_post`: raises `GateError` on any failure,
    so the caller decides whether that is fatal (rule 1) or a degradation.
    """
    cmd = ["gh", "api", "-X", "PATCH", path]
    for key, value in fields.items():
        cmd += ["-f", f"{key}={value}"]
    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True, encoding="utf-8", errors="replace",
            check=False,
        )
    except FileNotFoundError as exc:  # pragma: no cover - environment problem
        raise GateError(f"gh CLI not available: {exc}") from exc

    if completed.returncode != 0:
        raise GateError(
            f"gh api -X PATCH {path} failed (exit {completed.returncode}): "
            f"{completed.stderr.strip()[:400]}"
        )
    body = completed.stdout.strip()
    if not body:
        return {}
    try:
        return json.loads(body)
    except json.JSONDecodeError as exc:
        raise GateError(f"gh api -X PATCH {path} returned non-JSON: {exc}") from exc


def own_job_id(
    repo: str,
    run_id: str,
    job_name: str,
    run_attempt: "str | None" = None,
    *,
    fetch=None,
) -> "int | None":
    """The check-run id of OUR OWN job, or None when it cannot be resolved.

    A job IS a check-run: `GET /actions/runs/<id>/jobs` reports `id`, and the
    Checks API serves that same number (`/check-runs/<id>`) -- measured on
    job 103506691766, whose `check_run_url` ends in its own job id.

    `run_attempt` filters out the superseded attempts a re-run leaves in the
    same listing; without it the first name match could be a previous
    attempt's check-run, whose output nothing will ever read again.
    """
    api = fetch if fetch is not None else _gh_api
    payload = api(f"repos/{repo}/actions/runs/{run_id}/jobs?per_page=100")
    if not isinstance(payload, dict):
        raise GateError(f"unexpected jobs payload for run {run_id}")
    for job in payload.get("jobs") or []:
        if not isinstance(job, dict):
            continue
        if run_attempt is not None and str(job.get("run_attempt")) != str(run_attempt):
            continue
        if job.get("name") == job_name:
            return job.get("id")
    return None


def publish_check_run_output(
    repo: str,
    run_id: str,
    job_name: str,
    code: int,
    message: str,
    advisory: Sequence[str] = (),
    run_attempt: "str | None" = None,
    *,
    fetch=None,
    patch=None,
) -> bool:
    """PATCH the verdict onto the AUTO check-run's `output` (acceptance 1).

    Why PATCH and not POST. A second check-run bearing the required name
    lands in a FOREIGN check suite and GitHub ANDs the two, so a posted
    verdict never replaces a stale one -- the measurement that removed
    POSTing from pr-gate-stale-sweep.yml (78 PRs blocked, #11519) and the
    reason `pr-gate-rerun.yml` re-runs the original run instead of posting
    beside it. PATCH edits the check-run IN PLACE, in its own suite, which is
    what `gh run rerun` does for the conclusion -- and what the conclusion's
    MOTIVE needs just as much.

    The PATCH must be authenticated by a GitHub App: a PAT is refused with
    "You must authenticate via a GitHub App" (measured 2026-09-12). The job's
    own `GITHUB_TOKEN` is an installation token of the app that owns this
    check-run, which is why the call is made from inside the job and with
    that token.

    Returns True when the output was written. Every other outcome -- no job
    id resolvable, token refused, fork PR (read-only token), network -- is
    False plus a warning to the log. Publication must never flip a verdict:
    the exit code and the log line stay the source of truth.
    """
    try:
        job_id = own_job_id(
            repo, run_id, job_name, run_attempt, fetch=fetch
        )
    except GateError as exc:
        print(f"[pr-gate] WARN -- check-run id unresolved: {exc}", flush=True)
        return False
    if not job_id:
        print(
            f"[pr-gate] WARN -- no job named {job_name!r} in run {run_id}; "
            "check-run output not published",
            flush=True,
        )
        return False

    title = message.splitlines()[0] if message else job_name
    writer = patch if patch is not None else _gh_api_patch
    try:
        writer(
            f"repos/{repo}/check-runs/{job_id}",
            {
                "output[title]": f"{job_name}: {title}"[:255],
                "output[summary]": verdict_body(message, advisory),
            },
        )
    except GateError as exc:
        print(f"[pr-gate] WARN -- check-run output not published: {exc}", flush=True)
        return False
    return True


# Seconds to hold the step open after a successful self-cancel POST, so the
# cancellation signal reaches the runner BEFORE this process exits. Exiting
# first would complete the run as FAILURE and make the cancel a no-op -- the
# exact red lie #13510 removes. The signal lands in ~1-5 s; 15 s bounds the
# wait well above that while staying far under any job budget.
CANCEL_GRACE_SEC = 15.0


def cancel_own_run(repo: str, run_id: str) -> bool:
    """POST the Actions cancel endpoint for OUR OWN run (#13510).

    Boolean by design, unlike the GateError-raising neighbours: a refused
    cancel (run already completing, permissions hiccup, gh absent) is a
    degraded rendering, not an unknown state -- the caller keeps exit 1
    (rule 1) and the leg concludes FAILURE exactly as before this change.
    """
    try:
        completed = subprocess.run(
            ["gh", "api", "-X", "POST",
             f"repos/{repo}/actions/runs/{run_id}/cancel"],
            capture_output=True,
            text=True, encoding="utf-8", errors="replace",
            check=False,
        )
    except FileNotFoundError:
        print("[pr-gate] WARN -- gh CLI not available for self-cancel", flush=True)
        return False
    if completed.returncode != 0:
        print(
            f"[pr-gate] WARN -- self-cancel refused (exit "
            f"{completed.returncode}): {completed.stderr.strip()[:300]}",
            flush=True,
        )
        return False
    return True


def post_check_run(
    repo: str,
    sha: str,
    name: str,
    code: int,
    message: str,
    *,
    poster=None,
) -> dict:
    """POST a completed check-run onto ``sha`` via the Checks API.

    The ``workflow_run`` re-aggregation job (#10433 item-1) re-runs the verdict
    but cannot rely on the job's auto check-run: for ``workflow_run``,
    ``GITHUB_SHA`` is the *default-branch* commit, so the auto check-run lands
    there and is invisible to the PR head's ``mergeState``. This POSTs a fresh
    check-run onto the PR head SHA (``head_sha``) so the re-aggregated
    conclusion surfaces on the PR.

    ``code`` follows :func:`main`'s convention: 0 = success, 1 = failure.
    ``poster`` is injectable so unit tests can assert the payload without the
    network. Resolved at call time (not bound at definition) so monkeypatching
    ``pr_gate._gh_api_post`` is seen by the default path.
    """
    if poster is None:
        poster = _gh_api_post
    title = message.splitlines()[0] if message else name
    fields = {
        "name": name,
        "head_sha": sha,
        "status": "completed",
        "conclusion": "success" if code == 0 else "failure",
        "output[title]": f"{name}: {title}"[:255],
        "output[summary]": message or title,
    }
    return poster(f"repos/{repo}/check-runs", fields)


def fetch_checks(repo: str, sha: str) -> list[dict]:
    """Union of check runs and legacy commit statuses for one SHA."""
    checks: list[dict] = []

    # Paginate check-runs (per_page=100 cap): judging a subset of the runs on a
    # busy SHA would silently drop verdicts. total_count is the authoritative
    # stop condition; an empty page is the defensive fallback.
    page = 1
    while True:
        runs = _gh_api(
            f"repos/{repo}/commits/{sha}/check-runs?per_page=100&page={page}"
        )
        if not isinstance(runs, dict):
            break
        page_runs = runs.get("check_runs", [])
        for run in page_runs:
            checks.append(
                {
                    "name": run.get("name"),
                    "status": run.get("status"),
                    "conclusion": run.get("conclusion"),
                    "started_at": run.get("started_at"),
                    "id": run.get("id"),
                }
            )
        if not page_runs:
            break
        total = runs.get("total_count")
        if total is not None and len(checks) >= total:
            break
        page += 1

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
    always_on_jobs: "frozenset[str] | None" = None,
    advisory_jobs: "frozenset[str] | None" = None,
    sleep=time.sleep,
    fetch=fetch_checks,
    now=time.monotonic,
    detail: "dict | None" = None,
) -> tuple[int, str]:
    """Poll until the check set is stable, then decide.

    Stability is `settle_polls` consecutive polls with nothing pending -- a
    single quiet poll is not enough, because a workflow queued milliseconds ago
    has not surfaced yet and would be invisible.

    `always_on_jobs` arms the delivery canary (rule 8). None or empty disables
    it (the gate then behaves exactly as before this rule). Only consulted at
    settle time, so a freshly-opened PR keeps the `settle_polls` grace period for
    Actions to create its check-runs.

    `advisory_jobs` is the roster of jobs whose parent workflow is advisory but
    whose own name does not carry the marker. Empty frozenset (default) disables
    the workflow-name side of `is_advisory` -- the historical behaviour, kept
    for tests that do not care.

    `detail`, when a dict is given, is filled with the advisory list of the
    LAST classification before the verdict (`detail["advisory"]`) so `main`
    can publish it in the step summary (#15693) without changing this
    function's 2-tuple return. The last classify is authoritative: the
    deadline path re-classifies into `final_*` and overwrites the entry.
    """
    deadline = now() + timeout_min * 60.0
    quiet_streak = 0
    pending: list[str] = []
    bad: list[str] = []
    adv_jobs = advisory_jobs or frozenset()

    while True:
        checks = fetch(repo, sha)
        pending, bad, ok, advisory = classify(checks, self_name, adv_jobs)
        if detail is not None:
            detail["advisory"] = list(advisory)

        if bad:
            # Fail fast: a failure cannot be undone by waiting longer.
            _report_advisory(advisory)
            return verdict(pending, bad, settled=True)

        if pending:
            quiet_streak = 0
        else:
            quiet_streak += 1
            if quiet_streak >= settle_polls:
                # Rule 8 canary: refuse to pass when the platform never
                # delivered the always-on bouquet (#9858 partial-delivery hole).
                # `checks` is the raw observation (names, pre-bucket) so advisory
                # always-on jobs still count as delivered.
                canary = _canary_verdict(checks, always_on_jobs or frozenset())
                if canary is not None:
                    _report_advisory(advisory)
                    print(f"[pr-gate] {canary[1]}", flush=True)
                    return canary
                _report_advisory(advisory)
                print(f"[pr-gate] settled: {len(ok)} check(s) green", flush=True)
                return verdict(pending, bad, settled=True)

        if now() >= deadline:
            # Issue #11751 -- phantom FAIL when the deadline fires BETWEEN the
            # last poll and the last constituent's completion. The classic case:
            # poll N reports 1 pending (say `Analyze (actions)`); the deadline
            # fires before poll N+1; `Analyze (actions)` finishes in the gap;
            # the gate announces `FAIL -- timed out waiting for: (none listed)`
            # even though the set is fully green. Re-read the state once more
            # before deciding -- a timeout is a signal to look again, not a
            # verdict in itself (same shape as `select()` with a deadline).
            final_checks = fetch(repo, sha)
            final_pending, final_bad, final_ok, final_advisory = classify(
                final_checks, self_name, adv_jobs
            )
            if detail is not None:
                detail["advisory"] = list(final_advisory)
            if not final_pending and not final_bad:
                # Everything settled in the gap: treat as a clean settle.
                # Still consult the delivery canary (rule 8) so an empty
                # bouquet is not silently flipped to PASS by the timeout itself.
                final_canary = _canary_verdict(
                    final_checks, always_on_jobs or frozenset()
                )
                if final_canary is not None:
                    _report_advisory(final_advisory)
                    print(f"[pr-gate] {final_canary[1]}", flush=True)
                    return final_canary
                _report_advisory(final_advisory)
                print(
                    f"[pr-gate] settled at deadline: {len(final_ok)} check(s) "
                    "green (phantom-FAIL recovered, #11751)",
                    flush=True,
                )
                return verdict(final_pending, final_bad, settled=True)
            # Genuine still-pending (or a red we just observed): fail with a
            # message that names the constituents. Empty list here would mean
            # the rule-1 invariant broke -- say so explicitly instead of the
            # former `(none listed)` placeholder that read like a degradation.
            if final_bad:
                _report_advisory(final_advisory)
                return verdict(final_pending, final_bad, settled=True)
            if not final_pending:
                # Defensive: settle_polls path did not fire (timeout) and the
                # re-read is also empty -- this is unreachable under current
                # `classify` (an empty set routes to `pending == []`), and we
                # want a loud diagnostic if it ever stops being unreachable.
                _report_advisory(final_advisory)
                print(
                    "[pr-gate] FAIL -- timed out with empty wait set (gate bug, "
                    "see #11751): this should be unreachable; the constituent "
                    "set is empty AND the deadline fired without settle.",
                    flush=True,
                )
                return 1, (
                    "FAIL -- timed out with empty wait set (gate bug, see #11751)"
                )
            _report_advisory(final_advisory)
            return verdict(final_pending, final_bad, settled=False)

        print(
            f"[pr-gate] waiting on {len(pending)} check(s): "
            f"{', '.join(pending[:6])}{' ...' if len(pending) > 6 else ''}",
            flush=True,
        )
        sleep(poll_sec)


def _workflow_command_escape(text: str) -> str:
    """Escape text for a GitHub workflow-command (`::error::`) annotation.

    A raw LF would end the annotation (truncating the reason), a raw CR
    mangles it, and a raw `%` swallows the following bytes as a bogus
    escape. Order is load-bearing: `%` must be escaped FIRST -- doing CR/LF
    first would re-escape the `%` those substitutions introduce (%250D).
    """
    return text.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def verdict_body(message: str, advisory: Sequence[str] = ()) -> str:
    """The published text of a verdict -- ONE builder, two surfaces (#15693).

    Both the step summary and the check-run `output.summary` are rendered
    from this string, so the two can never drift: acceptance 1 asks the
    summary to name the cause "the same as the log", and the only way to
    keep that true over time is to have a single source.

    The DWELL floor gets its do-not-repush guidance (a reaction push resets
    the 120-min floor from the new head); advisory checks are listed as
    non-blocking (#15548: a cancelled advisory read as the blocker while the
    real one was already repaired 18 min earlier).
    """
    lines = [message]
    if message.startswith("DWELL"):
        lines += [
            "",
            "Plancher mecanique -- rien a reparer dans la PR, et rien "
            "a attendre : enchainer un autre grain, c'est la candidate "
            "qui attend, pas la lane. Ne pas re-pusher (un re-push "
            "remet le plancher a zero depuis la nouvelle tete). Une "
            "fois le plancher ecoule, rejouer cette jambe "
            "(`gh run rerun <run_id> --job <job_id>`) ou laisser le "
            "balayage la reprendre -- sa cadence mesuree est de 2 h 33 "
            "a 5 h 18, pas horaire (#15197).",
        ]
    if advisory:
        lines += ["", "Advisory (not blocking):"]
        lines += [f"- {entry}" for entry in advisory]
    return "\n".join(lines)


def write_step_summary(
    code: int, message: str, advisory: Sequence[str] = ()
) -> None:
    """Publish the verdict to the job's STEP SUMMARY (#15693).

    This is the surface GitHub renders at the top of the run page -- the page
    a human opens from the red check. It is NOT the check-run's
    `output.summary`, and the difference is measured, not assumed:

        run 34681884304 (this file's own red gate, 2026-09-12): the step
        summary IS rendered on the run page -- `curl .../actions/runs/
        34681884304 | grep 'failing checks'` returns the verdict -- while
        `gh api .../check-runs/103521890556 --jq .output.summary` returns
        null. Same for the SUCCESSFUL sweep job 103506691766 (its log writes
        `$GITHUB_STEP_SUMMARY`; its check-run summary is null), and a scan of
        1098 `github-actions` check-runs over 40 main commits finds ZERO with
        a non-null summary. Every check-run that does carry one is created by
        the Checks API (POST), e.g. the shadow aggregator's
        `fast-lane (ombre): *`.

    So the issue's premise -- "$GITHUB_STEP_SUMMARY feeds the auto
    check-run's output.summary" -- is false on this repository, and this
    function alone would not satisfy acceptance 1. It is kept because the
    run-page rendering is real and useful; the check-run surface is served
    separately by :func:`publish_check_run_output`.

    No-op when `GITHUB_STEP_SUMMARY` is unset (local runs). A write failure
    degrades to a warning: publication must never flip a verdict -- the
    exit code and the log line remain the source of truth.
    """
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    if not path:
        return
    lines = [
        f"## PR gate: {'PASS' if code == 0 else 'FAIL'}",
        "",
        "```",
        verdict_body(message, advisory),
        "```",
    ]
    try:
        with open(path, "a", encoding="utf-8") as handle:
            handle.write("\n".join(lines) + "\n")
    except OSError as exc:
        print(f"[pr-gate] WARN -- step summary not written: {exc}", flush=True)


def _optional_int(raw: str) -> "int | None":
    """`--pr ""` vaut « pas de PR », pas une erreur d'argparse.

    Le workflow passe `--pr "${{ github.event.pull_request.number }}"` sans
    condition ; sur un `workflow_dispatch` cette expression rend la chaine
    vide. Un `type=int` y leverait SystemExit et rendrait le gate rouge pour
    une raison qui n'a rien a voir avec la PR -- exactement la classe de
    defaut que l'ancien input `sha` de ce workflow avait deja produite.
    """
    text = (raw or "").strip()
    if not text:
        return None
    return int(text)


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--sha", required=True, help="head SHA of the PR")
    parser.add_argument("--self-name", default=DEFAULT_SELF_NAME)
    parser.add_argument("--timeout-min", type=float, default=90.0)
    parser.add_argument("--poll-sec", type=float, default=30.0)
    parser.add_argument("--settle-polls", type=int, default=2)
    # Issue #10072 -- fork PRs short-circuit to PASS. Student PRs come from a
    # fork and have no internal convention to police; `enforce_admins: true` on
    # main's required checks would otherwise deadlock their admin merge. This
    # flag is the orchestrator's signal that "this PR is a fork; do not judge
    # its CI, only produce a verdict". The script still reports PASS so GitHub
    # can transition the check from pending to success (the workflow's own
    # invariant: "verdict on every PR").
    parser.add_argument(
        "--is-fork",
        action="store_true",
        help="PR comes from a fork (student work). Short-circuit to PASS.",
    )
    parser.add_argument(
        "--workflows-dir",
        default=DEFAULT_WORKFLOWS_DIR,
        help="Directory of GitHub workflow YAMLs for the rule-8 delivery canary.",
    )
    parser.add_argument(
        "--no-canary",
        action="store_true",
        help="Disable the rule-8 delivery canary (escape hatch only).",
    )
    parser.add_argument(
        "--post-check-run",
        action="store_true",
        help=(
            "POST the verdict as a completed check-run onto --sha via the "
            "Checks API. Used by the workflow_run re-aggregation job (#10433 "
            "item-1): that job's auto check-run lands on the default-branch "
            "commit, not the PR head, so without this POST the re-aggregated "
            "verdict is invisible to the PR's mergeState."
        ),
    )
    parser.add_argument(
        "--run-id",
        default=None,
        help=(
            "Workflow run id used to self-cancel on starvation (#13510) and "
            "to locate our own check-run for publication (#15693); defaults "
            "to $GITHUB_RUN_ID when the script runs inside Actions."
        ),
    )
    parser.add_argument(
        "--no-check-run-output",
        action="store_true",
        help=(
            "Ne pas publier le verdict dans l'`output` de notre propre "
            "check-run (#15693). Le resume du run (step summary) reste "
            "ecrit. Utile si un leg doit rester muet sur cette surface."
        ),
    )
    parser.add_argument(
        "--pr",
        type=_optional_int,
        default=None,
        help=(
            "Numero de la PR agregee. Requis pour appliquer le plancher de "
            "merge (--dwell-min) : sans lui le gate ne tourne pas dans un "
            "contexte de PR et son verdict ne peut pas bouger de mergeState."
        ),
    )
    parser.add_argument(
        "--dwell-min",
        type=float,
        default=0.0,
        help=(
            "Plancher, en minutes, entre le dernier commit de tete et le "
            "merge (mandat user 2026-09-07 : 120). 0 = desactive. Evalue "
            "APRES que les constituants ont conclu verts, hors de la boucle "
            "d'attente : aucun runner n'est tenu a dormir. Le rouge se leve "
            "seul au balayage periodique de pr-gate-stale-sweep.yml "
            "(cadence mesuree 2 h 33 - 5 h 18, pas horaire -- #15197), "
            "ou en rejouant la jambe. Une lane n'attend jamais ce "
            "balayage : elle enchaine un autre grain (#15726). Voir "
            "scripts/ci/merge_dwell.py."
        ),
    )
    parser.add_argument(
        "--no-self-cancel",
        action="store_true",
        help=(
            "On starvation, exit FAIL without cancelling the own run "
            "(escape hatch; also the implicit behaviour when no run id "
            "is resolvable, e.g. a local run)."
        ),
    )
    args = parser.parse_args(list(argv) if argv is not None else None)

    if args.is_fork:
        # Rule 1 ("bias to fail") does not apply here: the workflow deliberately
        # chose to opt out. Document the bypass in the log so a reader of the
        # CI log sees why no aggregation happened.
        print(
            "[pr-gate] fork PR -- out of scope (issue #10072); "
            "reporting PASS without polling.",
            flush=True,
        )
        # #15693: even the fork short-circuit publishes -- a student PR's
        # check-run should not be the only one whose summary stays null.
        write_step_summary(0, "PASS -- fork PR short-circuit (issue #10072)")
        # The workflow_run re-aggregation path runs on the default branch, so it
        # cannot read the fork flag from the pull_request payload. It still POSTs
        # here: a fork PR must surface `success` on its head SHA to match the
        # --is-fork short-circuit (#10072), not a stale aggregated FAIL.
        _maybe_post_check_run(
            args, 0, "PASS -- fork PR short-circuit (issue #10072)"
        )
        return 0

    always_on_jobs: "frozenset[str] | None" = None
    if not args.no_canary:
        always_on_jobs = derive_always_on_jobs(args.workflows_dir, args.self_name)
        if not always_on_jobs:
            # Disabled, not fatal (see derive_always_on_jobs): an unreadable
            # canary roster must not block every PR.
            print(
                f"[pr-gate] delivery canary disabled: no always-on jobs derived "
                f"from {args.workflows_dir}",
                flush=True,
            )

    # Roster of jobs whose parent workflow is advisory but whose own name does
    # not carry the marker (e.g. ``machine-dep-timing`` from
    # ``machine-dep-timing-advisory``). Without this, the gate misroutes them
    # into ``bad`` on every PR -- the failure mode that left #12524 and #12783
    # blocked 44h/9h before the fix landed.
    advisory_jobs = derive_advisory_jobs(args.workflows_dir)

    detail: dict = {}
    try:
        code, message = wait_and_decide(
            args.repo,
            args.sha,
            args.self_name,
            args.timeout_min,
            args.poll_sec,
            args.settle_polls,
            always_on_jobs,
            advisory_jobs,
            detail=detail,
        )
    except GateError as exc:
        # Rule 1: an unreadable state is a failure, never a pass. Fall
        # through to the single emission tail instead of returning here: the
        # old early return exited BEFORE the ::error:: point, leaving the
        # most opaque failure mode (API unreadable at all) mute in the UI
        # (#15472). Verdict semantics unchanged: code 1, same message.
        code, message = 1, f"FAIL -- cannot establish check state: {exc}"

    # --- plancher de merge (mandat user 2026-09-07) ---------------------
    #
    # Evalue APRES l'agregation, et seulement si elle est verte : un rouge
    # de CI est une information plus utile qu'un « attends 2 h », et la
    # remplacer ferait disparaitre la cause reelle du log.
    #
    # Le plancher n'entre PAS dans la boucle d'attente. `wait_and_decide`
    # tient un slot de runner tant qu'il poll ; l'y faire dormir 120 min
    # tiendrait ce slot 120 min par PR. Le rouge rendu ici est rejoue par
    # pr-gate-stale-sweep.yml des que le plancher est ecoule -- a une
    # cadence mesuree de 2 h 33 a 5 h 18, pas horaire malgre son cron
    # (#15197) : la lane rejoue la jambe elle-meme si elle veut merger.
    if code == 0 and args.dwell_min > 0:
        if _merge_dwell is None:
            # Rule 1 ne s'applique pas a une capacite absente : le module
            # manquant n'est pas un etat de PR inconnu, c'est un depot mal
            # deploye. Le dire fort, et ne pas bloquer 100 % des PRs.
            print(
                "[pr-gate] plancher de merge demande mais "
                "scripts/ci/merge_dwell.py est introuvable -- plancher NON "
                "applique (ceci est un defaut de deploiement, pas un vert).",
                flush=True,
            )
        else:
            try:
                dwell_ok, dwell_msg = _merge_dwell.check(
                    args.repo, args.sha, args.pr, args.dwell_min
                )
            except _merge_dwell.DwellError as exc:
                # Ici rule 1 s'applique : l'age de la tete est lisible en
                # principe, donc ne pas l'avoir lu est un etat inconnu.
                code, message = 1, (
                    "FAIL -- plancher de merge illisible: {}".format(exc)
                )
            else:
                if dwell_ok:
                    print("[pr-gate] {}".format(dwell_msg), flush=True)
                else:
                    code, message = 1, "DWELL -- {}".format(dwell_msg)

    # --- #15693: publish the verdict BEFORE the #13510 self-cancel --------
    #
    # The dwell block above has already applied the final message rewrite
    # (dwell only fires on code==0; the self-cancel below only on code==1 +
    # STARVED -- the two rewrites are mutually exclusive, so the summary
    # written here is final). Writing BEFORE the self-cancel matters: a
    # cancelled job can be torn down before this process reaches its
    # emission tail, and a STARVED leg still owes the lane its named
    # constituents. The fork short-circuit publishes at its own early
    # return; local runs (no GITHUB_STEP_SUMMARY) no-op inside.
    advisory = detail.get("advisory", ())
    write_step_summary(code, message, advisory)
    # The check-run surface, which the step summary does NOT reach (measured;
    # see `write_step_summary`). This is the one acceptance 1 names: the
    # required check itself must carry its motive. Skipped on the operator
    # harness (`--post-check-run`), whose contract is to POST its verdict on
    # the PR head -- its own auto check-run sits on the default branch and is
    # not the PR's gate leg.
    run_id = args.run_id or os.environ.get("GITHUB_RUN_ID")
    if run_id and not args.no_check_run_output and not args.post_check_run:
        publish_check_run_output(
            args.repo,
            run_id,
            args.self_name,
            code,
            message,
            advisory,
            os.environ.get("GITHUB_RUN_ATTEMPT"),
        )

    # #13510: render a starvation as CANCELLED, not FAILURE. The PR stays
    # BLOCKED (a cancelled required check is not success), but the leg no
    # longer claims a failure that never happened, and pr-gate-stale-sweep
    # already treats a cancelled gate leg as a re-run candidate (#11862) --
    # the same recovery channel as a supersession-cancel. Workflow-run mode
    # only: --post-check-run runs on the default branch as an operator
    # harness whose own run is NOT the PR's gate leg, so it keeps POSTing
    # the verdict instead of cancelling itself.
    if (
        code == 1
        and message.startswith("STARVED")
        and not args.no_self_cancel
        and not args.post_check_run
    ):
        run_id = args.run_id or os.environ.get("GITHUB_RUN_ID")
        if run_id:
            print(
                f"[pr-gate] STARVED -- constituents still pending, nothing "
                f"red; cancelling own run {run_id} so the leg concludes "
                "CANCELLED, not FAILURE (#13510). The PR stays blocked; "
                "pr-gate-stale-sweep will re-aggregate.",
                flush=True,
            )
            if cancel_own_run(args.repo, run_id):
                # Hold the step open so the cancel signal lands before we
                # exit (see CANCEL_GRACE_SEC). Exit code stays 1: if the
                # cancel lost the race, rule 1 still holds.
                time.sleep(CANCEL_GRACE_SEC)
        else:
            print(
                "[pr-gate] STARVED but no run id resolvable (local run) -- "
                "FAIL per rule 1",
                flush=True,
            )

    print(f"[pr-gate] {message}", flush=True)
    _maybe_post_check_run(args, code, message)
    if code != 0:
        # Le check-run derive du job ne porte qu'« Process completed with exit
        # code 1 » sur un rouge : seul l'annotation donne la RAISON du verdict
        # dans l'UI. Legs DWELL rendus muets mesures sur #15472 (2026-09-10) :
        # 8 PR gates rouges sans cause organique, tous des DWELL (plancher de
        # merge, mandat 07/09) dont la re-agregation ne rend jamais compte.
        # Le message peut porter %, CR ou LF (stderr gh multi-ligne) : un LF
        # brut tronque l'annotation, un % brut avale les octets suivants --
        # echappement protocolaire workflow-command, % EN PREMIER (#15472).
        print(
            f"::error::[pr-gate] {_workflow_command_escape(message)}",
            file=sys.stderr,
            flush=True,
        )
    return code


def _maybe_post_check_run(args, code: int, message: str) -> None:
    """POST the verdict as a check-run if ``--post-check-run`` was given.

    The wrapper around :func:`post_check_run` that makes a POST failure
    non-fatal: a failed POST leaves the stale check in place (the status quo
    before #10433 item-1), never a false PASS. The exit code already reflects
    the verdict; this only concerns whether the fresh verdict *surfaces* on the
    PR head.
    """
    if not args.post_check_run:
        return
    try:
        post_check_run(args.repo, args.sha, args.self_name, code, message)
    except GateError as exc:
        print(
            f"[pr-gate] WARN -- check-run POST failed, stale check stays: {exc}",
            file=sys.stderr,
        )
        return
    conclusion = "success" if code == 0 else "failure"
    print(
        f"[pr-gate] posted check-run on {args.sha[:7]} (conclusion={conclusion})",
        flush=True,
    )


if __name__ == "__main__":
    raise SystemExit(main())
