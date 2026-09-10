#!/usr/bin/env python3
r"""Scheduler liveness organ (#15332) -- measure the SERVED cadence of the
``schedule`` event class, and survive the outage it observes.

## Why

Measured 2026-09-09: the last ``event=schedule`` run of the ENTIRE repository is
``2026-09-09T01:13:03Z``; four hours later nothing planned had fired, while the
workflows stayed ``state=active`` and merges kept flowing. What stopped was the
DELIVERY of the ``schedule`` event, not its execution.

``pr-gate-sweep-health-advisory.yml`` already watches ONE organ (the age of the
last successful ``pr-gate-stale-sweep`` run). Two limits, both named by #15332:

  1. the observer is itself carried by a ``schedule:`` -- it dies of the same
     cause it exists to report (it went quiet at 01:13Z like everything else);
  2. it compares the age of ONE organ to a declared window, and nothing ever
     measures the gap between the DECLARED cadence (``7 * * * *``) and the
     SERVED one (~2.5-3.5 h observed, #15332). A cadence that is never served
     as written never goes red -- until it reaches zero, which is too late.

This organ answers (2) for a small registry of critical scheduled workflows and
renders the served-vs-declared ratio. The ``push`` heartbeat added to the
advisory workflow answers (1): merges keep flowing while the scheduler is mute,
so a push-triggered run still happens during the exact failure it reports.

## What it does NOT do

No red on a degraded-but-alive cadence. A permanently red organ on a chronic
condition gets ignored -- the repository's own doctrine. Age predicates decide
the verdict (OK / LATE / DEAD); the served-vs-declared ratio is rendered as a
NAMED WARNING and left to the human/coordinator read.

## Verdicts

  - ``OK``      : last scheduled run within 2x the declared interval
  - ``LATE``    : within 2x-4x (degraded delivery; visible, not red)
  - ``DEAD``    : beyond max(4x declared, 90 min) -- or no scheduled run at all
                  in history. THIS is what reddens the step (exit 1).
  - ``UNKNOWN`` : the gh probe itself failed for that organ -- named, never
                  silently folded into OK or DEAD.

Control against a dead instrument: if EVERY organ returns UNKNOWN or zero runs,
the probe -- not the scheduler -- is the suspect, and the organ exits 1 with
``INSTRUMENT_UNKNOWN`` rather than reporting a fleet-wide green.
"""
from __future__ import annotations

import argparse
import json
import os
import statistics
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone

LATE_FACTOR = 2
DEAD_FACTOR = 4
DEAD_FLOOR_MIN = 90.0

SAMPLE_LIMIT = 20


@dataclass(frozen=True)
class Organ:
    workflow: str
    declared_min: float
    note: str = ""


# Declared cadences read firsthand from each workflow file's `cron:` line.
# KEEP IN SYNC with the `cron:` lines of the workflows listed below: this
# table is a hand-copied snapshot, nothing verifies it against the files. A
# future `cron:` change in any listed workflow diverges SILENTLY -- the
# declared column here would mis-state the cadence (and mis-scale LATE/DEAD
# floors) without failing anything. Update this table in the same PR that
# touches any of these `cron:` lines.
REGISTRY: tuple[Organ, ...] = (
    Organ("pr-gate-stale-sweep.yml", 60.0, "cron '7 * * * *'"),
    Organ("pr-gate-sweep-health-advisory.yml", 30.0, "cron '13,43 * * * *' -- cet observateur"),
    Organ("linux-runner-starvation-advisory.yml", 30.0, "cron '19,49 * * * *'"),
    Organ("stale-guard-red-sweep.yml", 1440.0, "cron '53 4 * * *'"),
    Organ("epic-neglect-sweep.yml", 1440.0, "cron '37 8 * * *'"),
    Organ("grain-orphans-sweep.yml", 1440.0, "cron '23 7 * * *'"),
)


@dataclass
class Liveness:
    organ: Organ
    verdict: str
    age_min: float | None = None
    served_min: float | None = None
    n_runs: int = 0
    detail: str = ""
    warnings: list[str] = field(default_factory=list)


def parse_times(payload: str) -> list[datetime]:
    """Scheduled run creation times, newest first. Raises on malformed payload."""
    runs = json.loads(payload)
    times: list[datetime] = []
    for run in runs:
        created = (run.get("createdAt") or "").replace("Z", "+00:00")
        if not created:
            continue
        times.append(datetime.fromisoformat(created))
    times.sort(reverse=True)
    return times


def served_interval_minutes(times: list[datetime]) -> float | None:
    """Median gap between consecutive scheduled runs -- the SERVED cadence.

    None when fewer than two runs exist: one point carries no interval, and
    inventing one from a declared number would be the very error this organ
    exists to catch.
    """
    if len(times) < 2:
        return None
    gaps = [
        (times[i] - times[i + 1]).total_seconds() / 60.0
        for i in range(len(times) - 1)
    ]
    return statistics.median(gaps)


def verdict_for(age_min: float, declared_min: float) -> str:
    dead_after = max(declared_min * DEAD_FACTOR, DEAD_FLOOR_MIN)
    if age_min > dead_after:
        return "DEAD"
    if age_min > declared_min * LATE_FACTOR:
        return "LATE"
    return "OK"


def evaluate(organ: Organ, times: list[datetime], now: datetime) -> Liveness:
    """Pure verdict for one organ against its scheduled history."""
    if not times:
        return Liveness(
            organ=organ,
            verdict="DEAD",
            n_runs=0,
            detail=(
                "aucun run planifie dans l'historique -- livraison de l'evenement "
                "'schedule' interrompue pour cet organe (#15332)"
            ),
        )
    age_min = (now - times[0]).total_seconds() / 60.0
    served = served_interval_minutes(times)
    verdict = verdict_for(age_min, organ.declared_min)
    result = Liveness(
        organ=organ,
        verdict=verdict,
        age_min=age_min,
        served_min=served,
        n_runs=len(times),
    )
    if served is not None and served > organ.declared_min * LATE_FACTOR:
        result.warnings.append(
            f"cadence SERVIE degradee: {served:.0f} min observes entre runs "
            f"vs {organ.declared_min:.0f} min declares (ratio {served / organ.declared_min:.1f}x)"
        )
    return result


def render(results: list[Liveness]) -> list[str]:
    lines = ["[scheduler-liveness] livraison de l'evenement 'schedule' (#15332)", ""]
    for r in results:
        age = f"{r.age_min:.0f} min" if r.age_min is not None else "n/a"
        served = f"{r.served_min:.0f} min" if r.served_min is not None else "n/a"
        lines.append(
            f"  {r.verdict:<7} {r.organ.workflow:<42} "
            f"declare {r.organ.declared_min:>6.0f} min | servi {served:>8} | "
            f"dernier run {age:>8} | {r.n_runs} runs"
        )
        for w in r.warnings:
            lines.append(f"          WARN {w}")
        if r.verdict in ("DEAD", "UNKNOWN") and r.detail:
            lines.append(f"          {r.detail}")
    return lines


def probe(repo: str, workflow: str) -> tuple[list[datetime] | None, str]:
    """(times, error). times is None when the probe itself failed."""
    cmd = [
        "gh", "run", "list", "--repo", repo, "--workflow", workflow,
        "--event", "schedule", "--limit", str(SAMPLE_LIMIT),
        "--json", "createdAt",
    ]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError) as exc:
        return None, f"sonde gh indisponible: {type(exc).__name__}"
    if out.returncode != 0:
        err = (out.stderr or "").strip().splitlines()
        return None, f"gh rc={out.returncode}: {err[0] if err else 'sans message'}"
    try:
        return parse_times(out.stdout or "[]"), ""
    except (ValueError, TypeError) as exc:
        return None, f"payload illisible: {type(exc).__name__}"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Scheduler liveness (#15332)")
    ap.add_argument("--repo", default=os.environ.get("REPO", "jsboige/CoursIA"))
    ap.add_argument("--json", action="store_true", help="sortie machine")
    args = ap.parse_args(argv)

    now = datetime.now(timezone.utc)
    results: list[Liveness] = []
    for organ in REGISTRY:
        times, error = probe(args.repo, organ.workflow)
        if times is None:
            results.append(Liveness(organ=organ, verdict="UNKNOWN", detail=error))
        else:
            results.append(evaluate(organ, times, now))

    unknown = [r for r in results if r.verdict == "UNKNOWN"]
    dead = [r for r in results if r.verdict == "DEAD"]
    late = [r for r in results if r.verdict == "LATE"]

    if args.json:
        print(json.dumps({
            "unknown": len(unknown), "dead": len(dead), "late": len(late),
            "organs": [
                {
                    "workflow": r.organ.workflow,
                    "declared_min": r.organ.declared_min,
                    "verdict": r.verdict,
                    "age_min": r.age_min,
                    "served_min": r.served_min,
                    "n_runs": r.n_runs,
                    "warnings": r.warnings,
                    "detail": r.detail,
                }
                for r in results
            ],
        }, indent=2))
    else:
        for line in render(results):
            print(line)

    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        try:
            with open(summary, "a", encoding="utf-8") as fh:
                fh.write("\n".join(render(results)) + "\n")
        except OSError:
            pass  # a missing summary surface must not change the verdict

    # Control against a dead instrument: no organ yielded any history at all
    # (every probe failed, or every probe came back empty -- a wrong repo or a
    # token without Actions:read looks exactly like a fleet-wide scheduler
    # death). Report the instrument, never a fabricated fleet verdict.
    if all(r.n_runs == 0 for r in results):
        print(
            "::error::[scheduler-liveness] INSTRUMENT_UNKNOWN -- aucune sonde n'a "
            "rendu d'historique: c'est la mesure qui est en panne, pas forcement "
            "le scheduler. Ne pas lire ce rouge comme un verdict flotte (#15332).",
            file=sys.stderr,
        )
        return 1

    for r in dead:
        print(
            f"::error::[scheduler-liveness] {r.organ.workflow}: {r.detail or 'dernier run planifie trop ancien'} "
            f"-- cadence declaree {r.organ.declared_min:.0f} min ({r.organ.note}). Voir #15332.",
            file=sys.stderr,
        )
    for r in unknown:
        print(
            f"::warning::[scheduler-liveness] {r.organ.workflow}: sonde en echec ({r.detail}) "
            "-- verdict UNKNOWN, non compte comme defaut.",
            file=sys.stderr,
        )
    for r in late:
        print(
            f"::warning::[scheduler-liveness] {r.organ.workflow}: livraison en retard "
            f"({r.age_min:.0f} min pour {r.organ.declared_min:.0f} min declares).",
            file=sys.stderr,
        )

    return 1 if dead else 0


if __name__ == "__main__":
    sys.exit(main())
