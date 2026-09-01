#!/usr/bin/env python3
"""Measure GitHub Actions queued-run health, isolating the 2026-08-19 ghost floor.

The CoursIA repo carries 18 ghost runs in its queued list since 2026-08-19
03:03-05:15Z : server-side state-machine corruption (cancel = 422, delete =
403, rerun = "already running", GraphQL cancel = no-op). No API mutation can
purge them. The `queued` counter has been floored at 18 since then, so any
naive `gh run list --status queued` measure is biased by a known constant.

This script applies the operational workaround prescribed in #13579 : filter
runs by their `created_at` against a cutoff date (default 2026-08-20). Ghost
runs (created before the cutoff) are reported separately from live runs
(created on/after the cutoff), so the live count is unbiased and the ghost
floor is auditable.

Examples:
  python scripts/ci/gh_queue_health.py --repo jsboige/CoursIA
  python scripts/ci/gh_queue_health.py --repo jsboige/CoursIA \
      --cutoff 2026-08-25 --output queue-health.json
  python scripts/ci/gh_queue_health.py --input queue-health.json
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

EXIT_OK = 0
EXIT_GHOST = 1
EXIT_BROKEN = 2

PER_PAGE = 100
INCIDENT_FLOOR_DATE = "2026-08-19"  # origin of the corruption window


class InstrumentError(RuntimeError):
    """The instrument cannot prove that its result is complete or coherent."""


def parse_date(value: str) -> datetime:
    """Parse a YYYY-MM-DD date into a UTC midnight datetime."""
    try:
        parsed = datetime.strptime(value, "%Y-%m-%d")
    except ValueError as exc:
        raise InstrumentError(f"invalid date (expected YYYY-MM-DD): {value!r}") from exc
    return parsed.replace(tzinfo=timezone.utc)


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
        try:
            proc = subprocess.run(
                ["gh", "api", endpoint],
                capture_output=True, text=True, encoding="utf-8",
                check=False,
            )
        except FileNotFoundError as exc:
            raise InstrumentError("gh CLI not on PATH") from exc
        if proc.returncode != 0:
            raise InstrumentError(
                f"gh api failed (rc={proc.returncode}): {proc.stderr.strip()}"
            )
        try:
            payload = json.loads(proc.stdout)
        except json.JSONDecodeError as exc:
            raise InstrumentError(f"non-JSON response: {proc.stdout[:200]!r}") from exc
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


def classify_runs(runs: list[dict], cutoff: datetime) -> dict:
    """Split queued runs into ghosts (created before cutoff) and live (on/after).

    `cutoff` is exclusive for the ghost bucket, inclusive for the live bucket:
    a run created exactly at cutoff is treated as live (defensive against
    off-by-one floor contamination).
    """
    ghosts: list[dict] = []
    live: list[dict] = []
    parse_failures: list[dict] = []
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
        if created < cutoff:
            ghosts.append({"id": run.get("id"), "name": run.get("name"),
                           "created_at": created_raw, "html_url": run.get("html_url")})
        else:
            live.append({"id": run.get("id"), "name": run.get("name"),
                         "created_at": created_raw, "html_url": run.get("html_url")})
    return {"ghosts": ghosts, "live": live, "parse_failures": parse_failures}


def verdict(ghosts: int, live: int, parse_failures: int) -> str:
    """`CLEAN` if no ghosts and no parse failures. Otherwise `GHOST_RUNS_DETECTED`.

    `GHOST_RUNS_DETECTED` is the expected verdict on CoursIA itself (the 18
    ghosts of 2026-08-19). `CLEAN` is expected on repos without historical
    incidents. `STALE_FLOOR` is reserved for the precise case where the ghost
    count equals the known incident floor (18) -- useful for surfacing the
    signature on CoursIA without false-positive alarms on other repos.
    """
    if parse_failures > 0:
        return "INCOMPLETE"
    if ghosts == 0:
        return "CLEAN"
    if ghosts == 18 and live == 0:
        return "STALE_FLOOR"
    return "GHOST_RUNS_DETECTED"


def load_snapshot(path: Path) -> list[dict]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise InstrumentError(f"cannot read snapshot {path}: {exc}") from exc
    if isinstance(value, dict) and "snapshot" in value and isinstance(value["snapshot"], dict):
        if "workflow_runs" in value["snapshot"]:
            return value["snapshot"]["workflow_runs"]
        return value["snapshot"].get("runs", [])
    if isinstance(value, list):
        return value
    if isinstance(value, dict) and "workflow_runs" in value:
        return value["workflow_runs"]
    # A prior analysis output looks like {cutoff, verdict, counts, snapshot_size,
    # ghosts, live, parse_failures}. It is already classified, so replaying it
    # through classify_runs is pointless -- but the caller still needs the raw
    # timeline to recompute. We synthesize a synthetic list whose created_at is
    # not used: the ghosts and live buckets carry the real IDs and timestamps,
    # and classify_runs will reproduce the same partition if cutoff matches.
    if isinstance(value, dict) and "ghosts" in value and "live" in value:
        synthetic: list[dict] = []
        for entry in value.get("ghosts", []) or []:
            if isinstance(entry, dict) and "created_at" in entry:
                synthetic.append(entry)
        for entry in value.get("live", []) or []:
            if isinstance(entry, dict) and "created_at" in entry:
                synthetic.append(entry)
        if synthetic:
            return synthetic
    raise InstrumentError("snapshot must be a list of runs, a dict with workflow_runs, "
                          "a {snapshot: {...}} envelope, or a prior analysis output")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--repo", help="owner/repository for live collection")
    source.add_argument("--input", type=Path, help="replay an existing snapshot")
    parser.add_argument("--cutoff", default="2026-08-20",
                        help=f"ghost-vs-live cutoff date (YYYY-MM-DD); default 2026-08-20")
    parser.add_argument("--output", type=Path, help="write JSON result (default: stdout)")
    args = parser.parse_args(argv)

    try:
        cutoff = parse_date(args.cutoff)
        if args.input:
            raw_runs = load_snapshot(args.input)
        else:
            raw_runs = fetch_queued_runs(args.repo)
        classification = classify_runs(raw_runs, cutoff)
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
        print(f"[queue-health] BROKEN INSTRUMENT: {exc}", file=sys.stderr)
        return EXIT_BROKEN


if __name__ == "__main__":
    raise SystemExit(main())
