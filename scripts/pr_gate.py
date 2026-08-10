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

# GitHub check_run.status values that mean "not finished".
STATUS_PENDING = frozenset({"queued", "in_progress", "waiting", "pending", "requested"})

DEFAULT_SELF_NAME = "PR gate"

# Substring that marks a check as advisory (see rule 6). Matched
# case-insensitively anywhere in the check name, because GitHub renders a job as
# "<workflow> / <job>" and the marker sits in the job half. This is the
# convention already in use across `.github/workflows` -- e.g. "CJK residue
# advisory (label, non-blocking)" -- so no separate registry has to be kept in
# sync with the workflows.
ADVISORY_MARKER = "advisory"


def is_advisory(name: str) -> bool:
    """True when the check declares itself non-blocking by name (rule 6)."""
    return ADVISORY_MARKER in (name or "").lower()


# Where the always-on workflow jobs are derived from (rule 8 canary). Resolved
# relative to the repo root: this script lives in scripts/, so its parent is the
# repository root that holds .github/workflows.
DEFAULT_WORKFLOWS_DIR = str(Path(__file__).resolve().parent.parent / ".github" / "workflows")


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
) -> tuple[list[str], list[str], list[str], list[str]]:
    """Split settled checks into (pending, bad, ok, advisory) name lists.

    `self_name` is excluded so the gate never waits on itself. Matching is a
    prefix test because GitHub renders a job inside a workflow as
    "<workflow> / <job>", and the gate is required under its workflow name.

    Advisory checks (rule 6) are diverted into their own list -- annotated with
    what they actually reported -- and never reach `pending` or `bad`. They are
    kept separate rather than merged into `ok` so a caller can print "advisory
    X failed" instead of silently rewriting a failure into a pass.
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

        if is_advisory(name):
            if conclusion not in CONCLUSION_OK:
                state = conclusion or status or "no verdict"
                advisory.append(f"{name} ({state})")
            else:
                ok.append(name)
            continue

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

    return sorted(pending), sorted(bad), sorted(ok), sorted(advisory)


def _report_advisory(advisory: Sequence[str]) -> None:
    """Print non-green advisory checks. Never affects the exit code (rule 6).

    Printing is the whole point: the gate must not be the reason an advisory
    signal disappears. The label posted by the advisory workflow itself remains
    the durable carrier -- this line only keeps it visible in the gate's own log.
    """
    for entry in advisory:
        print(f"[pr-gate] advisory (not blocking): {entry}", flush=True)


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
    always_on_jobs: "frozenset[str] | None" = None,
    sleep=time.sleep,
    fetch=fetch_checks,
    now=time.monotonic,
) -> tuple[int, str]:
    """Poll until the check set is stable, then decide.

    Stability is `settle_polls` consecutive polls with nothing pending -- a
    single quiet poll is not enough, because a workflow queued milliseconds ago
    has not surfaced yet and would be invisible.

    `always_on_jobs` arms the delivery canary (rule 8). None or empty disables
    it (the gate then behaves exactly as before this rule). Only consulted at
    settle time, so a freshly-opened PR keeps the `settle_polls` grace period for
    Actions to create its check-runs.
    """
    deadline = now() + timeout_min * 60.0
    quiet_streak = 0
    pending: list[str] = []
    bad: list[str] = []

    while True:
        checks = fetch(repo, sha)
        pending, bad, ok, advisory = classify(checks, self_name)

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
            _report_advisory(advisory)
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

    try:
        code, message = wait_and_decide(
            args.repo,
            args.sha,
            args.self_name,
            args.timeout_min,
            args.poll_sec,
            args.settle_polls,
            always_on_jobs,
        )
    except GateError as exc:
        # Rule 1: an unreadable state is a failure, never a pass.
        print(f"[pr-gate] FAIL -- cannot establish check state: {exc}", file=sys.stderr)
        return 1

    print(f"[pr-gate] {message}", flush=True)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
