#!/usr/bin/env python3
"""Measure GitHub Actions runner demand without silent API truncation.

The live mode collects a time-bounded cohort of workflow runs and all their
jobs. The offline mode replays the exact same snapshot without network access.
Every metric carries its denominator; an incomplete job is never converted to
zero runtime, and a broken collection exits 2 instead of returning a clean 0.

Examples:
  python scripts/ci/measure_runner_demand.py --repo owner/repo \
      --since 2026-08-24T09:00:00Z --until 2026-08-24T10:00:00Z \
      --output runner-demand.json
  python scripts/ci/measure_runner_demand.py --input runner-demand.json
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter, defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Callable
from urllib.parse import urlencode

EXIT_OK = 0
EXIT_BROKEN = 2
PER_PAGE = 100
SEARCH_CAP = 1000
MIN_SLICE = timedelta(seconds=1)
TIMESTAMP_SKEW_TOLERANCE = timedelta(seconds=1)
TIMESTAMP_SKEW_TOLERANCE = timedelta(seconds=1)


class MeasurementError(RuntimeError):
    """The instrument cannot prove that its result is complete or coherent."""


def parse_time(value: str) -> datetime:
    text = value.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        parsed = datetime.fromisoformat(text)
    except ValueError as exc:
        raise MeasurementError(f"invalid ISO-8601 timestamp: {value!r}") from exc
    if parsed.tzinfo is None:
        raise MeasurementError(f"timestamp must include a timezone: {value!r}")
    return parsed.astimezone(timezone.utc)


def iso_z(value: datetime) -> str:
    return value.astimezone(timezone.utc).isoformat().replace("+00:00", "Z")


def gh_api(endpoint: str) -> object:
    completed = subprocess.run(
        ["gh", "api", endpoint],
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise MeasurementError(f"gh api failed for {endpoint}: {detail}")
    try:
        return json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise MeasurementError(f"gh api returned invalid JSON for {endpoint}") from exc


def _run_endpoint(repo: str, start: datetime, end: datetime, page: int) -> str:
    # The API range is inclusive at both ends. Adjacent slices therefore share
    # their boundary; run IDs are de-duplicated after collection.
    query = urlencode({
        "created": f"{iso_z(start)}..{iso_z(end)}",
        "per_page": PER_PAGE,
        "page": page,
    })
    return f"repos/{repo}/actions/runs?{query}"


def _collect_run_slice(
    repo: str,
    start: datetime,
    end: datetime,
    fetch: Callable[[str], object],
) -> list[dict]:
    first = fetch(_run_endpoint(repo, start, end, 1))
    if not isinstance(first, dict) or not isinstance(first.get("workflow_runs"), list):
        raise MeasurementError("actions/runs response has no workflow_runs list")
    total = first.get("total_count")
    if not isinstance(total, int) or total < 0:
        raise MeasurementError("actions/runs response has no valid total_count")

    if total >= SEARCH_CAP:
        if end - start <= MIN_SLICE:
            raise MeasurementError(
                f"actions/runs remains capped at {total} in one-second slice "
                f"{iso_z(start)}..{iso_z(end)}"
            )
        middle = start + (end - start) / 2
        return (
            _collect_run_slice(repo, start, middle, fetch)
            + _collect_run_slice(repo, middle, end, fetch)
        )

    rows = list(first["workflow_runs"])
    page = 2
    while len(rows) < total:
        payload = fetch(_run_endpoint(repo, start, end, page))
        if not isinstance(payload, dict) or not isinstance(payload.get("workflow_runs"), list):
            raise MeasurementError(f"invalid actions/runs page {page}")
        chunk = payload["workflow_runs"]
        if not chunk:
            raise MeasurementError(
                f"actions/runs page {page} empty before total_count={total} "
                f"(collected={len(rows)})"
            )
        rows.extend(chunk)
        page += 1
    if len(rows) != total:
        raise MeasurementError(
            f"actions/runs pagination mismatch: total_count={total}, collected={len(rows)}"
        )
    return rows


def collect_runs(
    repo: str,
    since: datetime,
    until: datetime,
    fetch: Callable[[str], object] = gh_api,
) -> list[dict]:
    if since >= until:
        raise MeasurementError("--since must be earlier than --until")
    rows = _collect_run_slice(repo, since, until, fetch)
    by_id: dict[int, dict] = {}
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get("id"), int):
            raise MeasurementError("workflow run without an integer id")
        created = parse_time(str(row.get("created_at") or ""))
        if since <= created < until:
            by_id[row["id"]] = row
    return sorted(by_id.values(), key=lambda row: (row.get("created_at") or "", row["id"]))


def collect_jobs(
    repo: str,
    run_id: int,
    fetch: Callable[[str], object] = gh_api,
) -> list[dict]:
    rows: list[dict] = []
    page = 1
    total: int | None = None
    while total is None or len(rows) < total:
        endpoint = (
            f"repos/{repo}/actions/runs/{run_id}/jobs?"
            + urlencode({"filter": "all", "per_page": PER_PAGE, "page": page})
        )
        payload = fetch(endpoint)
        if not isinstance(payload, dict) or not isinstance(payload.get("jobs"), list):
            raise MeasurementError(f"invalid jobs response for run {run_id}, page {page}")
        reported = payload.get("total_count")
        if not isinstance(reported, int) or reported < 0:
            raise MeasurementError(f"jobs response for run {run_id} has no valid total_count")
        if total is None:
            total = reported
        elif reported != total:
            raise MeasurementError(f"jobs total_count changed while paging run {run_id}")
        chunk = payload["jobs"]
        if not chunk and len(rows) < total:
            raise MeasurementError(
                f"jobs page {page} empty before total_count={total} for run {run_id}"
            )
        rows.extend(chunk)
        page += 1
    if len(rows) != total:
        raise MeasurementError(
            f"jobs pagination mismatch for run {run_id}: total_count={total}, collected={len(rows)}"
        )
    return rows


def _minimal_run(row: dict, jobs: list[dict]) -> dict:
    head_repo = row.get("head_repository") or {}
    return {
        "id": row["id"],
        "name": row.get("name"),
        "event": row.get("event"),
        "status": row.get("status"),
        "conclusion": row.get("conclusion"),
        "created_at": row.get("created_at"),
        "run_started_at": row.get("run_started_at"),
        "updated_at": row.get("updated_at"),
        "head_repository": {"full_name": head_repo.get("full_name")},
        "pull_requests": [
            {"number": pr.get("number")}
            for pr in (row.get("pull_requests") or [])
            if isinstance(pr, dict)
        ],
        "jobs": [
            {
                "id": job.get("id"),
                "name": job.get("name"),
                "status": job.get("status"),
                "conclusion": job.get("conclusion"),
                "created_at": job.get("created_at"),
                "started_at": job.get("started_at"),
                "completed_at": job.get("completed_at"),
                "runner_name": job.get("runner_name"),
                "labels": job.get("labels") or [],
            }
            for job in jobs
        ],
    }


def collect_snapshot(
    repo: str,
    since: datetime,
    until: datetime,
    fetch: Callable[[str], object] = gh_api,
) -> dict:
    runs = collect_runs(repo, since, until, fetch)
    collected = [
        _minimal_run(run, collect_jobs(repo, run["id"], fetch))
        for run in runs
    ]
    return {
        "schema_version": 1,
        "repo": repo,
        "since": iso_z(since),
        "until": iso_z(until),
        "runs": collected,
    }


def _duration_minutes(start: str, end: str, label: str) -> float | None:
    a, b = parse_time(start), parse_time(end)
    if b < a:
        # GitHub timestamps have one-second precision and occasionally invert
        # adjacent events by exactly one second. Exclude and count this datum;
        # never turn it into a clean zero. Larger inversions remain fatal.
        if a - b <= TIMESTAMP_SKEW_TOLERANCE:
            return None
        raise MeasurementError(f"negative duration for {label}: {start} -> {end}")
    return (b - a).total_seconds() / 60.0


def analyze(snapshot: dict) -> dict:
    if snapshot.get("schema_version") != 1:
        raise MeasurementError("unsupported or missing snapshot schema_version")
    repo = snapshot.get("repo")
    runs = snapshot.get("runs")
    if not isinstance(repo, str) or not repo or not isinstance(runs, list):
        raise MeasurementError("snapshot must contain repo and runs")
    since, until = parse_time(snapshot.get("since", "")), parse_time(snapshot.get("until", ""))
    window_hours = (until - since).total_seconds() / 3600.0
    if window_hours <= 0:
        raise MeasurementError("snapshot window must have positive duration")

    provenance = Counter()
    conclusions = Counter()
    burst = Counter()
    workflow_data: dict[str, dict[str, float | int]] = defaultdict(
        lambda: {"runs": 0, "jobs": 0, "timed_jobs": 0, "runner_minutes": 0.0, "queue_minutes": 0.0}
    )
    workflow_conclusions: dict[str, Counter] = defaultdict(Counter)
    workflow_conclusions: dict[str, Counter] = defaultdict(Counter)
    total_jobs = timed_jobs = incomplete_jobs = skipped_without_start = 0
    timestamp_skew_jobs = 0
    runner_minutes = queue_minutes = 0.0

    seen_runs: set[int] = set()
    for run in runs:
        if not isinstance(run, dict) or not isinstance(run.get("id"), int):
            raise MeasurementError("snapshot contains a run without integer id")
        if run["id"] in seen_runs:
            raise MeasurementError(f"duplicate run id in snapshot: {run['id']}")
        seen_runs.add(run["id"])
        created = parse_time(str(run.get("created_at") or ""))
        if not (since <= created < until):
            raise MeasurementError(f"run {run['id']} lies outside snapshot window")
        burst[created.strftime("%Y-%m-%dT%H:%MZ")] += 1
        head_name = ((run.get("head_repository") or {}).get("full_name"))
        provenance["unknown" if not head_name else ("same_repo" if head_name == repo else "fork")] += 1
        conclusions[str(run.get("conclusion") or "incomplete")] += 1
        workflow = str(run.get("name") or "<unnamed>")
        workflow_data[workflow]["runs"] += 1
        workflow_conclusions[workflow][str(run.get("conclusion") or "incomplete")] += 1
        jobs = run.get("jobs")
        if not isinstance(jobs, list):
            raise MeasurementError(f"run {run['id']} has no jobs list")
        for job in jobs:
            total_jobs += 1
            workflow_data[workflow]["jobs"] += 1
            started, completed = job.get("started_at"), job.get("completed_at")
            created_job = job.get("created_at")
            if not started:
                incomplete_jobs += 1
                if job.get("conclusion") == "skipped":
                    skipped_without_start += 1
                continue
            if not completed:
                incomplete_jobs += 1
                continue
            if not created_job:
                raise MeasurementError(f"started job {job.get('id')} has no created_at")
            work = _duration_minutes(started, completed, f"job {job.get('id')} runtime")
            wait = _duration_minutes(created_job, started, f"job {job.get('id')} queue wait")
            if work is None or wait is None:
                timestamp_skew_jobs += 1
                continue
            timed_jobs += 1
            runner_minutes += work
            queue_minutes += wait
            workflow_data[workflow]["timed_jobs"] += 1
            workflow_data[workflow]["runner_minutes"] += work
            workflow_data[workflow]["queue_minutes"] += wait

    by_workflow = []
    for name, data in workflow_data.items():
        by_workflow.append({
            "workflow": name,
            **{key: (round(value, 3) if isinstance(value, float) else value) for key, value in data.items()},
            "run_conclusions": dict(sorted(workflow_conclusions[name].items())),
        })
    by_workflow.sort(key=lambda row: (-row["runner_minutes"], row["workflow"]))

    return {
        "window": {
            "since": iso_z(since),
            "until": iso_z(until),
            "hours": round(window_hours, 6),
        },
        "denominators": {
            "runs": len(runs),
            "jobs": total_jobs,
            "timed_jobs": timed_jobs,
            "incomplete_or_untimed_jobs": incomplete_jobs,
            "timestamp_skew_jobs": timestamp_skew_jobs,
            "skipped_without_start": skipped_without_start,
            "timing_coverage": round(timed_jobs / total_jobs, 6) if total_jobs else None,
        },
        "runner": {
            "runner_minutes": round(runner_minutes, 3),
            "runner_minutes_per_wall_hour": round(runner_minutes / window_hours, 3),
            "average_runner_equivalents": round(runner_minutes / (window_hours * 60.0), 6),
            "queue_minutes_for_timed_jobs": round(queue_minutes, 3),
        },
        "provenance": {
            "same_repo": provenance["same_repo"],
            "fork": provenance["fork"],
            "unknown": provenance["unknown"],
        },
        "run_conclusions": dict(sorted(conclusions.items())),
        "runs_created_per_minute": dict(sorted(burst.items())),
        "by_workflow": by_workflow,
    }


def load_snapshot(path: Path) -> dict:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise MeasurementError(f"cannot read snapshot {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise MeasurementError("snapshot root must be an object")
    # A prior output can be replayed directly; retain only its source snapshot.
    if "snapshot" in value and isinstance(value["snapshot"], dict):
        return value["snapshot"]
    return value


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--input", type=Path, help="replay an existing JSON snapshot")
    source.add_argument("--repo", help="owner/repository for live collection")
    parser.add_argument("--since", help="inclusive UTC ISO-8601 start (live mode)")
    parser.add_argument("--until", help="exclusive UTC ISO-8601 end (live mode)")
    parser.add_argument("--output", type=Path, help="write JSON result (default: stdout)")
    args = parser.parse_args(argv)

    try:
        if args.input:
            if args.since or args.until:
                raise MeasurementError("--since/--until cannot be combined with --input")
            snapshot = load_snapshot(args.input)
        else:
            if not args.since or not args.until:
                raise MeasurementError("live mode requires --since and --until")
            snapshot = collect_snapshot(args.repo, parse_time(args.since), parse_time(args.until))
        result = {"snapshot": snapshot, "analysis": analyze(snapshot)}
        rendered = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(rendered, encoding="utf-8")
            print(f"[runner-demand] wrote {args.output}")
        else:
            print(rendered, end="")
        return EXIT_OK
    except MeasurementError as exc:
        print(f"[runner-demand] BROKEN INSTRUMENT: {exc}", file=sys.stderr)
        return EXIT_BROKEN


if __name__ == "__main__":
    raise SystemExit(main())
