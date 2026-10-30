#!/usr/bin/env python3
"""Measure GitHub Actions queued-run health, isolating known ghost classes.

The CoursIA repo carries unpurgeable ghost runs in its queued list from two
measured incidents, both refusing every API mutation (cancel = 409/422,
delete = 403, rerun = "already running"):

* 2026-08-19 03:03-05:15Z : 18 runs stranded by server-side state-machine
  corruption (#13579). Isolated by the original workaround: a `created_at`
  cutoff date (default 2026-08-20) -- ghost class "pre-cutoff".
* 2026-09-13 : 37 runs (35 on wt/vibe-g2-quantconnect, PR #15946 closed
  18:05Z the same day) stuck in pre-admission limbo -- the API reports
  status=queued forever, and cancel answers "Cannot cancel a workflow run
  that has not been queued yet" (#18215). Isolated structurally: a queued
  run whose pull request is closed can never be admitted -- ghost class
  "pr-closed", regardless of age.

Both classes are reported as ghosts with a `reason` field, so the live count
stays unbiased and the ghost floor is auditable. A queued run that is
neither pre-cutoff nor pr-closed stays live: a live queue that never drains
is the drift signal the watch exists to surface.

Examples:
  python scripts/ci/gh_queue_health.py --repo jsboige/CoursIA
  python scripts/ci/gh_queue_health.py --repo jsboige/CoursIA \
      --cutoff 2026-08-25 --output queue-health.json
  python scripts/ci/gh_queue_health.py --input queue-health.json
"""
from __future__ import annotations

import argparse
import base64
import concurrent.futures
import json
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import yaml

EXIT_OK = 0
EXIT_GHOST = 1
EXIT_BROKEN = 2

PER_PAGE = 100

# Second incident (#18131): 37 runs created 2026-09-13 08:46-09:10Z (36 on
# branch wt/vibe-g2-quantconnect, PR #15946 merged, + 1 Variation Tag Guard on
# main) stuck in `queued` with the same server-side corruption -- cancel and
# force-cancel both answer 409 "has not been queued yet". They sit after the
# 2026-08-20 cutoff, so the date filter counts them as live. The watch mode
# recognises them by IDENTITY, not by count: a new zombie is a run outside this
# set, stuck longer than the stale threshold.
KNOWN_ZOMBIE_RUN_IDS = frozenset({
    34748469766, 34749036033, 34749036037, 34749036038, 34749036040,
    34749036047, 34749036048, 34749036050, 34749036051, 34749036060,
    34749036061, 34749036064, 34749036069, 34749036070, 34749036074,
    34749036077, 34749036085, 34749036088, 34749036097, 34749036099,
    34749036100, 34749036102, 34749036103, 34749036104, 34749036108,
    34749036111, 34749036113, 34749036117, 34749036119, 34749036127,
    34749036141, 34749036144, 34749036149, 34749036157, 34749036169,
    34749036262, 34749066861,
})
# A live run queued longer than this is no longer backlog: it is a candidate
# zombie. Below it, a queued run is ordinary pool saturation, not drift.
DEFAULT_STALE_HOURS = 24.0

# Third permanent class (issue #20249): runs of an event that carries no PR
# by construction, wedged in `queued`, so the pr-closed class can never
# claim them. Measured shape: 4 "Linux runner starvation advisory" runs
# created 2026-10-07 15:08-15:11Z, identical across 4 consecutive daily
# snapshots (~12 days queued) -- the same day the coursia-linux labels
# were re-posed (08:04Z), i.e. the pre-labelling admission limbo. The live
# API measures their `event` as `workflow_run` (NOT `schedule` -- the
# workflow NAME says "advisory", the chaining event does not), so the
# event set below covers both chained and cron-triggered runs. A fifth run
# of the same workflow drained in the meantime, so the class is defined
# *structurally* (event set + age), never by run IDs: a run of such an
# event stuck past 7 days is treated as an explained ghost; below it stays
# live and the watch alarms on it as a candidate new zombie.
SCHEDULED_ORPHAN_EVENTS = frozenset({"schedule", "workflow_run"})
SCHEDULED_ORPHAN_HOURS = 168.0


class InstrumentError(RuntimeError):
    """The instrument cannot prove that its result is complete or coherent."""


def parse_date(value: str) -> datetime:
    """Parse a YYYY-MM-DD date into a UTC midnight datetime."""
    try:
        parsed = datetime.strptime(value, "%Y-%m-%d")
    except ValueError as exc:
        raise InstrumentError(f"invalid date (expected YYYY-MM-DD): {value!r}") from exc
    return parsed.replace(tzinfo=timezone.utc)


def _gh_api_json(endpoint: str, *, attempts: int = 2, backoff: float = 5.0):
    """Call `gh api <endpoint>` and return the parsed JSON payload.

    Shared transport for the queued-runs listing and the PR-state lookups,
    so both fail through the same InstrumentError channel.

    A single bounded retry (``attempts`` total, ``backoff`` seconds apart)
    absorbs a *transient* API hiccup -- a 429 rate-limit, a 5xx, a momentary
    gh failure -- that would otherwise declare the whole watch BROKEN for the
    day (the failure mode that opened #22186). A *structural* failure is not
    retried: ``gh`` missing from PATH and a non-JSON body both fail on the
    first attempt. A failure that persists after the retry still raises
    InstrumentError, so the watch degrades to BROKEN exactly as before.
    """
    last_error = "gh api failed (no attempt ran)"
    for attempt in range(max(1, attempts)):
        if attempt:
            time.sleep(backoff)
        try:
            proc = subprocess.run(
                ["gh", "api", endpoint],
                capture_output=True, text=True, encoding="utf-8",
                check=False,
            )
        except FileNotFoundError as exc:
            # `gh` not on PATH is not transient -- fail immediately.
            raise InstrumentError("gh CLI not on PATH") from exc
        if proc.returncode == 0:
            try:
                return json.loads(proc.stdout)
            except json.JSONDecodeError as exc:
                # A non-JSON body is a structural failure, not transient.
                raise InstrumentError(
                    f"non-JSON response: {proc.stdout[:200]!r}") from exc
        last_error = (
            f"gh api failed (rc={proc.returncode}) "
            f"after {attempt + 1} attempt(s): {proc.stderr.strip()}"
        )
    raise InstrumentError(last_error)


def fetch_queued_runs(repo: str) -> list[dict]:
    """Page through `GET /repos/{repo}/actions/runs?status=queued` until empty.

    Returns the raw `workflow_runs` array. We cannot use the gh CLI `--created`
    filter here because the gh run list interface does not expose it on
    `status=queued` directly (and even if it did, server-side filtering would
    be preferable but is not required for a small N like the 18 ghosts).
    """
    runs: list[dict] = []
    page = 1
    while True:
        endpoint = f"repos/{repo}/actions/runs?status=queued&per_page={PER_PAGE}&page={page}"
        payload = _gh_api_json(endpoint)
        if not isinstance(payload, dict) or "workflow_runs" not in payload:
            raise InstrumentError(f"unexpected payload shape: keys={list(payload)[:5]}")
        batch = payload["workflow_runs"]
        if not isinstance(batch, list):
            raise InstrumentError(f"workflow_runs is not a list: {type(batch).__name__}")
        runs.extend(batch)
        if len(batch) < PER_PAGE:
            break
        page += 1
        if page > 50:  # safety cap: 5000 ghost runs is implausible
            raise InstrumentError(f"pagination exceeded 50 pages for {repo}")
    return runs


def fetch_pr_states(repo: str, branches: list[str]) -> dict[str, str]:
    """Look up the PR state for each distinct head branch (one call per branch).

    Returns {branch: "open" | "closed" | "missing"}. Callers only pass the
    branches of post-cutoff `pull_request` runs (the pre-cutoff floor is
    already ghost-classified, so no lookup is wasted on it). A branch with
    several PRs reports the state of the most recent one -- on CoursIA a
    superseded closed PR behind a new open one is not a produced shape, and
    the misread would only delay a ghost classification, never fabricate one.
    """
    owner = repo.split("/", 1)[0]
    states: dict[str, str] = {}
    for branch in sorted(set(branches)):
        payload = _gh_api_json(f"repos/{repo}/pulls?head={owner}:{branch}&state=all")
        if not isinstance(payload, list):
            raise InstrumentError(
                f"unexpected pulls payload for {branch}: {type(payload).__name__}"
            )
        states[branch] = payload[0]["state"] if payload else "missing"
    return states


def classify_runs(runs: list[dict], cutoff: datetime,
                  pr_states: dict[str, str] | None = None,
                  now: datetime | None = None,
                  stale_runs_on: set[int] | None = None) -> dict:
    """Split queued runs into explained ghosts and live runs.

    A run is a ghost when its class is measured and permanent:

    * `pre-cutoff` -- created before `cutoff` (the 2026-08-19 corruption
      floor, #13579). `cutoff` is exclusive for the ghost bucket, inclusive
      for the live bucket: a run created exactly at cutoff is treated as
      live (defensive against off-by-one floor contamination).
    * `pr-closed` -- a `pull_request` run whose head-branch PR is closed
      (the 2026-09-13 pre-admission limbo of #18215: PR #15946 closed
      while its runs awaited admission, and the API refuses to cancel a
      run "that has not been queued yet"). Regardless of age: a closed PR
      can never be admitted.
    * `scheduled-orphan` -- a run of an event that carries no PR by
      construction (`SCHEDULED_ORPHAN_EVENTS`: `schedule`, `workflow_run`)
      queued for more than `SCHEDULED_ORPHAN_HOURS` (issue #20249: the
      2026-10-07 starvation advisories, event measured as `workflow_run`,
      wedged in the label re-pose window). Structural (event set + age),
      never by run IDs: a sibling run of the same workflow drained on its
      own, so an ID set would drift. Only applied when `now` is provided; a
      raw-shape replay without `now` keeps them live, and the prior-analysis
      replay carries their `reason` through `_ghost_reason`.
    * `stale-runs-on` -- the workflow file at the run's `head_sha` declared
      a `runs-on` pool that no longer exists in the workflow file at the
      `main` HEAD (a tranche of #17397 migrated the workflow to
      `ubuntu-latest`, but the run was queued before the merge and is now
      waiting for a self-hosted pool the workflow no longer requests).
      Cancellation is safe: the API can cancel these runs without the
      "has not been queued yet" 409 the pre-cutoff/pr-closed classes hit.
      Unlike the other two, this class is NOT permanent by nature -- a
      future re-migration back to self-hosted would re-admit them. The
      watch only counts them when they coexist with a non-draining live
      queue, and `--cancel` opts in explicitly.

    Anything else is live: an undrained live queue is the drift signal, not
    a classification failure. Entries carry `reason` (ghosts only), `event`
    and `head_branch` so a replayed prior output reproduces its verdict --
    synthesized ghost entries carry their original reason under
    `_ghost_reason`, which this classifier honors as authoritative.
    """
    pr_states = pr_states or {}
    stale_runs_on = stale_runs_on or set()
    ghosts: list[dict] = []
    live: list[dict] = []
    parse_failures: list[dict] = []

    def entry(run: dict, reason: str | None = None) -> dict:
        out = {"id": run.get("id"), "name": run.get("name"),
               "created_at": run.get("created_at"), "html_url": run.get("html_url"),
               "event": run.get("event"), "head_branch": run.get("head_branch"),
               "path": run.get("path")}
        if reason:
            out["reason"] = reason
        return out

    for run in runs:
        created_raw = run.get("created_at")
        if not isinstance(created_raw, str):
            parse_failures.append({"id": run.get("id"), "reason": "missing created_at"})
            continue
        try:
            created = datetime.fromisoformat(created_raw.replace("Z", "+00:00"))
        except ValueError:
            parse_failures.append({"id": run.get("id"), "reason": f"bad created_at {created_raw!r}"})
            continue
        replayed_reason = run.get("_ghost_reason")
        if isinstance(replayed_reason, str) and replayed_reason:
            ghosts.append(entry(run, replayed_reason))
        elif created < cutoff:
            ghosts.append(entry(run, "pre-cutoff"))
        elif (run.get("event") == "pull_request"
              and pr_states.get(run.get("head_branch")) == "closed"):
            ghosts.append(entry(run, "pr-closed"))
        elif (now is not None
              and run.get("event") in SCHEDULED_ORPHAN_EVENTS
              and (now - created).total_seconds() / 3600.0
              > SCHEDULED_ORPHAN_HOURS):
            ghosts.append(entry(run, "scheduled-orphan"))
        elif run.get("id") in stale_runs_on:
            ghosts.append(entry(run, "stale-runs-on"))
        else:
            live.append(entry(run))
    return {"ghosts": ghosts, "live": live, "parse_failures": parse_failures}


def verdict(ghosts: int, live: int, parse_failures: int) -> str:
    """Verdict for one measurement.

    `CLEAN` if no ghosts (a pure live backlog with an empty ghost set is a
    healthy queue, not a drift). `STALE_FLOOR` is the "every ghost belongs
    to a measured, permanent class and the live queue is empty" shape --
    ghosts > 0 AND live == 0. The count itself carries no signal since
    #18215: the floor grew from 18 (pre-cutoff, #13579) to 55 when the
    pr-closed class absorbed the 37 runs stranded by PR #15946's closure,
    and any future closed-PR wave grows it further by construction. What
    the watch must catch is different: `GHOST_RUNS_DETECTED` fires when
    ghosts coexist with a live queue that is not draining (a NEW zombie
    class -- e.g. the 2026-08-19 shape with open PRs -- lands in the live
    bucket and pins live > 0 at every watch). `INCOMPLETE` means the
    instrument itself could not parse one or more runs -- never confuse a
    broken instrument with a broken state (#14367 acceptance).
    """
    if parse_failures > 0:
        return "INCOMPLETE"
    if ghosts == 0:
        return "CLEAN"
    if live == 0:
        return "STALE_FLOOR"
    return "GHOST_RUNS_DETECTED"


def watch_verdict(ghosts: int, live: int, parse_failures: int) -> str:
    """Verdict for the watch workflow (--watch mode).

    The watch runs on a cron and exists to surface NEW ghost activity
    (zombie runs the API cannot purge). It collapses the four measurement
    verdicts into three actionable buckets:

      * `OK`         : either CLEAN (no ghosts at all) or STALE_FLOOR
                       (explained ghosts, empty live queue) -- the routine
                       CoursIA shape, no action.
      * `DRIFT`      : GHOST_RUNS_DETECTED (a live queue coexisting with
                       the ghost floor is not draining -- new zombie class
                       or blocked runners). The watch opens an alert.
      * `BROKEN`     : INCOMPLETE (the instrument could not parse). The
                       watch cannot conclude and surfaces the failure so a
                       human can investigate.

    This split keeps the steady-state CoursIA signature (explained ghosts,
    0 live) from spamming an issue every day while still catching real
    drift the moment it happens. See PR for #14367 and #18215.

    In `--watch` mode, `main()` passes as `live` only the STALE UNKNOWN live
    runs (see split_live, #18131): known zombies and the fresh backlog of a
    saturated pool no longer count as drift. The pr-closed classification
    (#18215) routes closed-PR runs to ghosts BEFORE split_live runs, so the
    known-zombie ID set is a defensive net for runs whose PR state could
    not be resolved.

    """
    v = verdict(ghosts, live, parse_failures)
    if v in ("CLEAN", "STALE_FLOOR"):
        return "OK"
    if v == "INCOMPLETE":
        return "BROKEN"
    return "DRIFT"


def split_live(live: list[dict], now: datetime, stale_hours: float) -> dict:
    """Split the live bucket for the watch mode (#18131).

    * `known_zombies` : runs of the 2026-09-13 incident (KNOWN_ZOMBIE_RUN_IDS),
      permanent and unpurgeable, reported but never alarming.
    * `stale_live`    : other runs queued for more than `stale_hours` -- the
      candidate NEW zombies, the only live runs the watch alarms on.
    * `fresh_live`    : runs queued for less than `stale_hours` -- ordinary
      backlog of a saturated pool, not drift.

    A run whose `created_at` cannot be parsed has already been routed to
    parse_failures by classify_runs, so every entry here parses.
    """
    known: list[dict] = []
    stale: list[dict] = []
    fresh: list[dict] = []
    for run in live:
        if run.get("id") in KNOWN_ZOMBIE_RUN_IDS:
            known.append(run)
            continue
        created = datetime.fromisoformat(str(run["created_at"]).replace("Z", "+00:00"))
        age_hours = (now - created).total_seconds() / 3600.0
        (stale if age_hours > stale_hours else fresh).append(run)
    return {"known_zombies": known, "stale_live": stale, "fresh_live": fresh}


def load_snapshot(path: Path) -> tuple[list[dict], list[dict]]:
    """Read a snapshot and return (runs, preserved_parse_failures).

    A snapshot is one of:
    - a list of raw `workflow_run` dicts (the live API shape),
    - a dict `{workflow_runs: [...]}`,
    - a dict `{snapshot: {workflow_runs: [...]}}` envelope,
    - a prior analysis output `{cutoff, verdict, counts, snapshot_size,
      ghosts, live, parse_failures}`.

    For raw shapes (the first three), `classify_runs` will re-derive parse
    failures from the runs themselves -- preserved_parse_failures is empty.

    For a prior analysis output, the `parse_failures` bucket is preserved
    as-is (it cannot be re-derived from the synthesized runs). Without this
    propagation, an `INCOMPLETE` snapshot would replay as `CLEAN` or
    `GHOST_RUNS_DETECTED` -- a verdict class change at replay, which
    defeats the purpose of replaying a snapshot.
    """
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise InstrumentError(f"cannot read snapshot {path}: {exc}") from exc
    if isinstance(value, dict) and "snapshot" in value and isinstance(value["snapshot"], dict):
        if "workflow_runs" in value["snapshot"]:
            return value["snapshot"]["workflow_runs"], []
        return value["snapshot"].get("runs", []), []
    if isinstance(value, list):
        return value, []
    if isinstance(value, dict) and "workflow_runs" in value:
        return value["workflow_runs"], []
    # A prior analysis output looks like {cutoff, verdict, counts, snapshot_size,
    # ghosts, live, parse_failures}. It is already classified, so replaying it
    # through classify_runs is pointless -- but the caller still needs the raw
    # timeline to recompute. We synthesize a synthetic list whose created_at is
    # not used: the ghosts and live buckets carry the real IDs and timestamps,
    # and classify_runs will reproduce the same partition if cutoff matches.
    # The `parse_failures` bucket is preserved verbatim because it cannot be
    # re-derived from the synthesized runs.
    if isinstance(value, dict) and "ghosts" in value and "live" in value:
        synthetic: list[dict] = []
        for entry in value.get("ghosts", []) or []:
            if isinstance(entry, dict) and "created_at" in entry:
                # Carry the original ghost class under `_ghost_reason` so the
                # replay classifies by reason (authoritative) instead of
                # re-deriving cutoff-only: a pr-closed ghost created after the
                # cutoff would otherwise replay as live and flip the verdict
                # class (#18215, same replay-fidelity concern as parse_failures
                # in #13966).
                synth = dict(entry)
                if isinstance(entry.get("reason"), str) and entry["reason"]:
                    synth["_ghost_reason"] = entry["reason"]
                synthetic.append(synth)
        for entry in value.get("live", []) or []:
            if isinstance(entry, dict) and "created_at" in entry:
                synthetic.append(dict(entry))
        preserved = list(value.get("parse_failures", []) or [])
        if synthetic or preserved:
            return synthetic, preserved
    raise InstrumentError("snapshot must be a list of runs, a dict with workflow_runs, "
                          "a {snapshot: {...}} envelope, or a prior analysis output")


def _normalize_runs_on(value) -> list[str] | None:
    """Normalize a workflow `runs-on` value to a list of label strings.

    Returns None when the shape is unparseable (caller treats it as "unknown"
    and skips the comparison). Accepts the four GitHub Actions shapes:

    * scalar: `runs-on: ubuntu-latest` -> `["ubuntu-latest"]`
    * list of scalars: `[self-hosted, linux, x64]` -> `["self-hosted", "linux", "x64"]`
    * selector with labels: `{group: ..., labels: [a, b]}` -> `["a", "b"]`
    * list of selectors (mixed): each item's `labels` are flattened

    The default for jobs that omit `runs-on` is propagated from the workflow
    top-level `runs-on` by the caller; this function is the per-job normalizer.
    """
    if value is None:
        return None
    if isinstance(value, str):
        return [value]
    if isinstance(value, list):
        out: list[str] = []
        for v in value:
            if isinstance(v, str):
                out.append(v)
            elif isinstance(v, dict):
                # A selector dict without a `labels` key is malformed --
                # GitHub's syntax requires either `labels` (full form) or
                # `group` (matched against registered groups), and the
                # helper receives the full form. Reject as None so the
                # caller skips the comparison rather than silently
                # producing an empty label set.
                labels = v.get("labels")
                if not isinstance(labels, list):
                    return None
                for label in labels:
                    if isinstance(label, str):
                        out.append(label)
            else:
                return None
        return out
    if isinstance(value, dict):
        labels = value.get("labels")
        if not isinstance(labels, list):
            return None
        out = [label for label in labels if isinstance(label, str)]
        return out
    return None


def _workflow_runs_on_fingerprint(yaml_text: str) -> frozenset | None:
    """Return a fingerprint of a workflow's (job, runs-on) pairs.

    Two workflows that share the same fingerprint declare the same runner
    pools for the same jobs (order-independent). This is what the
    stale-runs-on check compares: a run was queued against a workflow at
    `head_sha`; that workflow's fingerprint must match the workflow's
    fingerprint at the current main HEAD -- otherwise the run waits for a
    runner pool the workflow no longer requests.

    Returns None on parse failure. Returns an empty frozenset for a
    workflow with no jobs (pathological but unobjectionable).
    """
    try:
        data = yaml.safe_load(yaml_text)
    except yaml.YAMLError:
        return None
    if not isinstance(data, dict):
        return frozenset()
    jobs = data.get("jobs")
    if not isinstance(jobs, dict):
        return frozenset()
    default = _normalize_runs_on(data.get("runs-on"))
    pairs: set[tuple[str, tuple[str, ...]]] = set()
    for job_name, job_spec in jobs.items():
        # A bare `job_name:` (no value) parses to None, not {}. Treat
        # as an empty spec: inherit the default runs-on, no overrides.
        spec = job_spec if isinstance(job_spec, dict) else {}
        if "runs-on" in spec:
            runs_on = _normalize_runs_on(spec["runs-on"])
        else:
            runs_on = default
        if runs_on is None:
            return None
        pairs.add((str(job_name), tuple(runs_on)))
    return frozenset(pairs)


def fetch_workflow_runs_on_at_ref(repo: str, workflow_path: str,
                                  ref: str) -> frozenset | None:
    """Read .github/workflows/{path} at {ref} and return its runs-on fingerprint.

    Returns None on any failure (API error, non-text payload, unparseable
    YAML, missing jobs). The caller treats None as "unknown" and skips the
    run -- never synthesizes a fingerprint, never guesses a runner pool.
    """
    endpoint = (f"repos/{repo}/contents/.github/workflows/{workflow_path}"
                f"?ref={ref}")
    try:
        payload = _gh_api_json(endpoint)
    except InstrumentError:
        return None
    if not isinstance(payload, dict):
        return None
    content_b64 = payload.get("content")
    if not isinstance(content_b64, str):
        return None
    try:
        text = base64.b64decode(content_b64).decode("utf-8")
    except (ValueError, UnicodeDecodeError):
        return None
    return _workflow_runs_on_fingerprint(text)


def detect_stale_runs_on(runs: list[dict],
                         runs_on_at_ref) -> set[int]:
    """Return the IDs of runs whose workflow `runs-on` drifted from main HEAD.

    A run is stale when its workflow at `head_sha` has a different
    (job, runs-on) fingerprint than the same workflow at the `main` ref
    -- the run was queued against a runner pool the workflow no longer
    requests, so the queue will never admit it.

    `runs_on_at_ref(workflow_path, ref)` returns the fingerprint, or None
    when the lookup failed for any reason. A None on either side skips
    the run (no synthesis, no guess): a stale-runs-on verdict requires
    a positive comparison on both sides.

    The default top-level `runs-on` is inherited per-job by the fingerprint
    helper, so workflows that lean on the default behave consistently.

    Two caches: (path, head_sha) for the per-run lookups, and path for
    the shared main-HEAD lookup. Without the head_sha component, runs
    from the same workflow file but different commits would all share
    one head fingerprint -- a measured miss on a tranche with multiple
    open PRs pointing at distinct SHAs.
    """
    stale: set[int] = set()
    head_cache: dict[tuple[str, str], frozenset | None] = {}
    main_cache: dict[str, frozenset | None] = {}
    for run in runs:
        path = run.get("path")
        head_sha = run.get("head_sha")
        if not isinstance(path, str) or not isinstance(head_sha, str):
            continue
        run_id = run.get("id")
        if not isinstance(run_id, int):
            continue
        head_key = (path, head_sha)
        if head_key not in head_cache:
            head_cache[head_key] = runs_on_at_ref(path, head_sha)
        if path not in main_cache:
            main_cache[path] = runs_on_at_ref(path, "main")
        head_fp = head_cache[head_key]
        main_fp = main_cache[path]
        if head_fp is None or main_fp is None:
            continue
        if head_fp != main_fp:
            stale.add(run_id)
    return stale


def cancel_run(repo: str, run_id: int) -> dict:
    """Cancel a single queued run via the API. Returns a per-run verdict.

    The API answers 202 on a successful cancellation and 409 on a run
    that "has not been queued yet" (the pre-cutoff / pr-closed classes
    also see this 409 -- the 202 vs 409 split is the only signal the
    script has to know whether the cancellation was applied). The result
    is reported, never interpreted: the caller decides what to do.
    """
    endpoint = f"repos/{repo}/actions/runs/{run_id}/cancel"
    try:
        proc = subprocess.run(
            ["gh", "api", "-X", "POST", endpoint, "--silent"],
            capture_output=True, text=True, encoding="utf-8", check=False,
        )
    except FileNotFoundError:
        return {"ok": False, "status": "gh-missing", "error": "gh CLI not on PATH"}
    if proc.returncode == 0:
        return {"ok": True, "status": "cancelled"}
    snippet = (proc.stderr or proc.stdout).strip()
    return {"ok": False, "status": f"rc={proc.returncode}", "error": snippet[:200]}


def cancel_runs_parallel(repo: str, run_ids: list[int],
                         max_workers: int = 8) -> list[dict]:
    """Cancel multiple runs concurrently. Returns per-run verdicts.

    The 2026-10-15 measurement was ~2 s per cancellation sequentially; 8
    workers keep the wall clock bounded while staying well under the API
    secondary rate limits (1,000 requests per hour per token). The list is
    shuffled lightly in spirit (as_completed order is non-deterministic by
    design) -- no fairness guarantee, only that the slowest run bounds
    the batch.
    """
    if not run_ids:
        return []
    out: list[dict] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as ex:
        future_to_id = {ex.submit(cancel_run, repo, rid): rid for rid in run_ids}
        for fut in concurrent.futures.as_completed(future_to_id):
            rid = future_to_id[fut]
            try:
                res = fut.result()
            except Exception as exc:  # pragma: no cover -- defensive
                res = {"ok": False, "status": "exception", "error": str(exc)}
            res["id"] = rid
            out.append(res)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--repo", help="owner/repository for live collection")
    source.add_argument("--input", type=Path, help="replay an existing snapshot")
    parser.add_argument("--cutoff", default="2026-08-20",
                        help=f"ghost-vs-live cutoff date (YYYY-MM-DD); default 2026-08-20")
    parser.add_argument("--output", type=Path, help="write JSON result (default: stdout)")
    parser.add_argument("--stale-hours", type=float, default=DEFAULT_STALE_HOURS,
                        help="watch mode: a live run queued longer than this, and not "
                             "a known zombie, counts as drift (default "
                             f"{DEFAULT_STALE_HOURS:g}h); younger runs are backlog")
    parser.add_argument("--now", help="watch mode: reference time (ISO 8601), for "
                                      "replaying a snapshot deterministically; "
                                      "default: current UTC time")
    parser.add_argument("--watch", action="store_true",
                        help="emit the watch verdict (OK / DRIFT / BROKEN) and a "
                             "matching exit code; intended for the advisory cron "
                             "workflow that surfaces new ghost activity. Collapses "
                             "the measurement verdict to actionable buckets -- see "
                             "watch_verdict(). Without --watch, the original four-"
                             "bucket measurement verdict is returned.")
    parser.add_argument("--cancel", choices=["stale-runs-on"], default=None,
                        help="detect-and-optionally-cancel a ghost class. "
                             "`stale-runs-on` finds queued runs whose workflow "
                             "no longer requests the runner pool they were "
                             "queued against (a tranche of #17397). Requires "
                             "--repo (live API), and is a no-op on --input "
                             "snapshots that lack the embedded fingerprint. "
                             "Dry-run by default; pass --apply to cancel.")
    parser.add_argument("--apply", action="store_true",
                        help="with --cancel: actually POST cancel requests "
                             "(8 parallel workers, ~2 s/cancellation). "
                             "Default is dry-run -- the affected IDs are "
                             "reported, not touched.")
    parser.add_argument("--cancel-workers", type=int, default=8,
                        help="parallel workers for --apply (default 8). "
                             "8 is below the API secondary rate limits and "
                             "keeps the batch wall-clock bounded.")
    args = parser.parse_args(argv)

    try:
        cutoff = parse_date(args.cutoff)
        if args.input:
            raw_runs, preserved_pf = load_snapshot(args.input)
            pr_states: dict[str, str] = {}
        else:
            raw_runs = fetch_queued_runs(args.repo)
            preserved_pf = []
            # PR-state lookups are only needed for post-cutoff pull_request
            # candidates: everything older is pre-cutoff ghost by definition.
            # created_at is ISO-8601 and args.cutoff is YYYY-MM-DD, so the
            # lexical comparison is a valid date-prefix filter.
            candidates = sorted({
                run.get("head_branch") for run in raw_runs
                if run.get("event") == "pull_request"
                and isinstance(run.get("created_at"), str)
                and run["created_at"] >= args.cutoff
            } - {None})
            pr_states = fetch_pr_states(args.repo, candidates) if candidates else {}
        # Resolve the reference instant once, before classification. An
        # explicit --now always wins (deterministic replay by instant). A
        # live run resolves the wall clock. A snapshot replay without --now
        # keeps now=None for classification: the scheduled-orphan age class
        # (#20249) is inert offline, so the same snapshot renders the same
        # verdict at D+0 and at D+10 -- the replay-fidelity property already
        # guaranteed for parse_failures and _ghost_reason (#13966, #18215).
        if args.now:
            try:
                now = datetime.fromisoformat(args.now.replace("Z", "+00:00"))
            except ValueError as exc:
                raise InstrumentError(f"invalid --now: {args.now!r}") from exc
            if now.tzinfo is None:
                now = now.replace(tzinfo=timezone.utc)
        else:
            now = None if args.input else datetime.now(timezone.utc)

        # stale-runs-on detection: requires --repo (live API), and only
        # for runs whose `path` (the workflow file) and `head_sha` are
        # both set. The result is a set of run IDs routed to the ghost
        # bucket by `classify_runs`. Cancellation is opt-in via --apply
        # (dry-run by default).
        stale_runs_on: set[int] = set()
        cancel_report: list[dict] = []
        if args.cancel == "stale-runs-on":
            if args.input:
                raise InstrumentError(
                    "--cancel stale-runs-on requires --repo (live API); "
                    "snapshot mode does not embed workflow fingerprints"
                )
            fingerprint_cache: dict[tuple[str, str], frozenset | None] = {}

            def _runs_on_at_ref(path: str, ref: str) -> frozenset | None:
                key = (path, ref)
                if key not in fingerprint_cache:
                    fingerprint_cache[key] = fetch_workflow_runs_on_at_ref(
                        args.repo, path, ref)
                return fingerprint_cache[key]

            stale_runs_on = detect_stale_runs_on(raw_runs, _runs_on_at_ref)
            if args.apply and stale_runs_on:
                cancel_report = cancel_runs_parallel(
                    args.repo, sorted(stale_runs_on),
                    max_workers=max(1, args.cancel_workers),
                )
        classification = classify_runs(raw_runs, cutoff, pr_states, now=now,
                                        stale_runs_on=stale_runs_on)
        # When the input was a prior analysis output, `classify_runs` cannot
        # re-derive the parse_failures from the synthesized runs -- they were
        # never serialized into the synthesized list. Merge the preserved
        # bucket in so the verdict survives replay unchanged (#13966).
        if preserved_pf:
            seen_ids = {pf.get("id") for pf in classification["parse_failures"]}
            for pf in preserved_pf:
                if pf.get("id") not in seen_ids:
                    classification["parse_failures"].append(pf)
        gh_count, lv_count, pf_count = (
            len(classification["ghosts"]),
            len(classification["live"]),
            len(classification["parse_failures"]),
        )
        v = verdict(gh_count, lv_count, pf_count)
        result = {
            "cutoff": args.cutoff,
            "verdict": v,
            "counts": {"total": len(raw_runs), "ghosts": gh_count,
                       "live": lv_count, "parse_failures": pf_count},
            "snapshot_size": len(raw_runs),
            "ghosts": classification["ghosts"],
            "live": classification["live"],
            "parse_failures": classification["parse_failures"],
        }
        rendered = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
        if args.cancel == "stale-runs-on":
            # Surface the cancel verdict regardless of --apply. A dry run
            # is exactly as useful as an applied run when the goal is to
            # know which IDs would be cancelled and whether the API
            # accepted the request.
            result["stale_runs_on"] = {
                "detected": sorted(stale_runs_on),
                "applied": args.apply,
                "results": cancel_report,
            }
            rendered = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
        if args.watch:
            # Watch mode replaces the four-bucket verdict with three
            # actionable buckets (OK / DRIFT / BROKEN) and corresponding
            # exit codes. The measurement verdict is preserved under
            # `verdict_measurement` so the alert payload remains
            # diagnosable by the receiver of the JSON.
            # The watch alarms on live runs only when they are stale AND
            # unknown (#18131): the 2026-09-13 zombies and a saturated
            # pool's fresh backlog are reported, never alarmed on.
            # The watch split measures report time: on a replay without an
            # explicit --now the classification instant is None (frozen
            # verdict above), so split_live ages runs against this
            # rendering's wall clock.
            parts = split_live(classification["live"],
                               now or datetime.now(timezone.utc),
                               args.stale_hours)
            result["stale_hours"] = args.stale_hours
            result["counts"].update({
                "known_zombies": len(parts["known_zombies"]),
                "stale_live": len(parts["stale_live"]),
                "fresh_live": len(parts["fresh_live"]),
            })
            result["stale_live"] = parts["stale_live"]
            watch = watch_verdict(gh_count, len(parts["stale_live"]), pf_count)
            result["verdict_watch"] = watch
            result["verdict_measurement"] = v
            watch_rendered = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
            if args.output:
                args.output.parent.mkdir(parents=True, exist_ok=True)
                args.output.write_text(watch_rendered, encoding="utf-8")
                print(f"[queue-health-watch] wrote {args.output} (verdict={watch})")
            else:
                print(watch_rendered, end="")
            if watch == "OK":
                return EXIT_OK
            if watch == "BROKEN":
                print(f"[queue-health-watch] BROKEN INSTRUMENT: {pf_count} parse failures",
                      file=sys.stderr)
                return EXIT_BROKEN
            # DRIFT: ghost count drifted from the floor, or an unknown live
            # run is stuck past the stale threshold. Exit code 1 -- the
            # workflow uses this to fan out the alert (issue or comment).
            return EXIT_GHOST
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(rendered, encoding="utf-8")
            print(f"[queue-health] wrote {args.output} (verdict={v})")
        else:
            print(rendered, end="")
        if v == "CLEAN":
            return EXIT_OK
        if v == "INCOMPLETE":
            print(f"[queue-health] BROKEN INSTRUMENT: {pf_count} parse failures",
                  file=sys.stderr)
            return EXIT_BROKEN
        return EXIT_GHOST
    except InstrumentError as exc:
        # Write the failure to the output file so the workflow's BROKEN step
        # has a payload to surface -- before this the exception returned here
        # with no file written, so the issue opened with "payload non produit"
        # and no diagnosis (#22186).
        print(f"[queue-health] BROKEN INSTRUMENT: {exc}", file=sys.stderr)
        if args.output:
            try:
                args.output.parent.mkdir(parents=True, exist_ok=True)
                args.output.write_text(
                    json.dumps(
                        {"verdict_watch": "BROKEN",
                         "verdict_measurement": "BROKEN",
                         "instrument_error": str(exc)},
                        indent=2, ensure_ascii=False) + "\n",
                    encoding="utf-8")
            except OSError as write_exc:
                print(f"[queue-health] cannot write output on failure: {write_exc}",
                      file=sys.stderr)
        return EXIT_BROKEN


if __name__ == "__main__":
    raise SystemExit(main())
