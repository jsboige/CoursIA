#!/usr/bin/env python3
"""Garde advisory de variance des runners self-hosted (#15574 item 4).

POURQUOI CE SCRIPT EXISTE
-------------------------
Un meme test CPU rend 342 s sur deux runners et ne termine meme pas en trois
fois ce temps sur deux autres, a code constant (#15574, contre-experience
5ef6d259 du 2026-09-11). Un timeout qui tue un job lent fait alors rougir la
PR d'un tiers pour une raison qui ne vient pas de son diff.

L'item 4, arbitre par ai-01 (c.5916600342) : un runner est SIGNALE quand un
meme job y depasse 3x la mediane du pool pour ce job, au moins 2 fois sur
24 h. La garde est ADVISORY : elle ouvre ou alimente une issue qui nomme le
runner et son hote, et n'eteint rien -- le retrait reste au proprietaire de
l'hote.

POURQUOI UN LOG PORTE PAR UNE ISSUE ET PAS UNE FENETRE 24 H DIRECTE
-------------------------------------------------------------------
Le jeton de workflow plafonne a 1000 requetes/h et par depot, et le depot
tourne a ~780 runs/h mesures (cf runner-coresidence-advisory.yml) : une
fenetre 24 h en un run = ~19 000 appels jobs, quintuple le plafond. Chaque
run de la garde mesure donc une fenetre D'UNE HEURE (le maximum qui tient
sous le plafond, meme discipline que l'organe de co-residence), et le
criterium « 2 fois sur 24 h » se joue sur un LOG ACCUMULE : le corps de
l'issue de suivi porte les entrees horaires en bloc JSON dedie, relu,
enrichi et raza-24 h a chaque run. L'issue EST l'etat -- ouverte une fois,
alimentee ensuite.

Le signal ne declenche AUCUN exit non nul : la garde est advisory par
construction (schedule + workflow_dispatch, jamais pull_request/push), et
c'est le workflow qui poste le commentaire de signalement quand le verdict
JSON en porte un.

Sorties : exit 0 = mesure rendue (signal ou non) ; exit 2 = instrument casse
(erreur de collecte, cf fail-loud de measure_runner_demand.py, jamais un
zero propre qui se lirait « aucun runner lent »).
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

# Reutilisation de la collecte de l'organe de mesure (#15574 items 1-2) :
# meme pagination, memes garde-fous fail-loud, meme extraction d'hote.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from measure_runner_demand import (  # noqa: E402
    MeasurementError,
    _minimal_run,
    collect_jobs,
    collect_runs,
    host_of,
    iso_z,
    parse_time,
)

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_WINDOW_MINUTES = 60.0
DEFAULT_THRESHOLD = 3.0
DEFAULT_MIN_HITS = 2
DEFAULT_MIN_POOL = 4
DEFAULT_MEDIAN_FLOOR_MINUTES = 0.5
LOG_WINDOW_HOURS = 24.0
LOG_BLOCK_TAG = "variance-guard-log"


def _duration_minutes(job: dict) -> float | None:
    started = job.get("started_at")
    completed = job.get("completed_at")
    if not started or not completed:
        return None
    delta = parse_time(str(completed)) - parse_time(str(started))
    minutes = delta.total_seconds() / 60.0
    return minutes if minutes > 0 else None


def _median(values: list[float]) -> float:
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return (ordered[mid - 1] + ordered[mid]) / 2.0


def job_key(run: dict, job: dict) -> str:
    return f"{run.get('name') or '?'} :: {job.get('name') or '?'}"


def find_slow_instances(
    runs: list[dict],
    threshold: float = DEFAULT_THRESHOLD,
    min_pool: int = DEFAULT_MIN_POOL,
    median_floor_minutes: float = DEFAULT_MEDIAN_FLOOR_MINUTES,
) -> dict[str, list[dict]]:
    """Retourne {runner_name: [instances lentes]} pour la fenetre mesuree.

    Une instance est lente si sa duree depasse threshold x la mediane du pool
    pour SA cle de job (workflow :: job). Les pools trop petits (< min_pool)
    ou trop rapides (mediane < plancher) sont exclus : tripler 8 secondes de
    bruit n'est pas un signal, c'est le moyen de fabriquer un garde rouge
    permanent qu'on apprend a ignorer.
    """
    pools: dict[str, list[tuple[float, dict, dict]]] = {}
    for run in runs:
        for job in run.get("jobs", []):
            if job.get("status") != "completed" or not job.get("runner_name"):
                continue
            minutes = _duration_minutes(job)
            if minutes is None:
                continue
            pools.setdefault(job_key(run, job), []).append((minutes, run, job))

    slow: dict[str, list[dict]] = {}
    for key, instances in pools.items():
        if len(instances) < min_pool:
            continue
        median = _median([m for m, _, _ in instances])
        if median < median_floor_minutes:
            continue
        for minutes, run, job in instances:
            if minutes > threshold * median:
                runner = str(job["runner_name"])
                slow.setdefault(runner, []).append({
                    "job": key,
                    "duration_minutes": round(minutes, 2),
                    "pool_median_minutes": round(median, 2),
                    "ratio": round(minutes / median, 2),
                    "conclusion": job.get("conclusion"),
                })
    return slow


def parse_log_body(body: str) -> list[dict]:
    """Extrait le log JSON du corps de l'issue (bloc ```variance-guard-log)."""
    tag = f"```{LOG_BLOCK_TAG}"
    if tag not in body:
        return []
    chunk = body.split(tag, 1)[1].split("```", 1)[0].strip()
    try:
        payload = json.loads(chunk)
    except json.JSONDecodeError:
        return []
    entries = payload.get("entries") if isinstance(payload, dict) else None
    return entries if isinstance(entries, list) else []


def merge_log(
    entries: list[dict],
    window_slow: dict[str, list[dict]],
    now: datetime,
    window_hours: float = LOG_WINDOW_HOURS,
) -> list[dict]:
    """Fusionne le log existant avec la fenetre courante, raza 24 h."""
    merged: dict[str, dict] = {}
    for entry in entries:
        ts = str(entry.get("ts") or "")
        if not ts:
            continue
        try:
            stamp = parse_time(ts)
        except (ValueError, TypeError):
            continue
        if now - stamp > timedelta(hours=window_hours):
            continue
        merged[ts + "|" + str(entry.get("seq", 0))] = entry
    stamp = iso_z(now)
    entry = {
        "ts": stamp,
        "runners": {
            runner: {"host": host_of(runner), "slow": instances}
            for runner, instances in window_slow.items()
        },
    }
    merged[stamp] = entry
    return sorted(merged.values(), key=lambda e: str(e.get("ts")))


def evaluate_signals(log: list[dict], min_hits: int = DEFAULT_MIN_HITS) -> list[dict]:
    """Un runner est signale s'il cumule >= min_hits instances lentes sur la fenetre du log."""
    per_runner: dict[str, dict] = {}
    for entry in log:
        for runner, payload in (entry.get("runners") or {}).items():
            record = per_runner.setdefault(runner, {
                "runner": runner, "host": payload.get("host"), "hits": [],
            })
            for instance in payload.get("slow", []):
                record["hits"].append({"ts": entry.get("ts"), **instance})
    signals = [r for r in per_runner.values() if len(r["hits"]) >= min_hits]
    signals.sort(key=lambda r: (-len(r["hits"]), r["runner"]))
    for signal in signals:
        signal["hit_count"] = len(signal["hits"])
    return signals


def render_log_body(log: list[dict]) -> str:
    payload = json.dumps({"entries": log}, ensure_ascii=False, indent=1)
    return f"```{LOG_BLOCK_TAG}\n{payload}\n```"


def collect_window(
    repo: str,
    until: datetime,
    window_minutes: float,
) -> list[dict]:
    since = until - timedelta(minutes=window_minutes)
    runs = collect_runs(repo, since, until)
    minimal = []
    for row in runs:
        jobs = collect_jobs(repo, int(row["id"]))
        minimal.append(_minimal_run(row, jobs))
    return minimal


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--window-minutes", type=float, default=DEFAULT_WINDOW_MINUTES)
    parser.add_argument("--threshold", type=float, default=DEFAULT_THRESHOLD)
    parser.add_argument("--min-hits", type=int, default=DEFAULT_MIN_HITS)
    parser.add_argument("--min-pool", type=int, default=DEFAULT_MIN_POOL)
    parser.add_argument("--median-floor-minutes", type=float, default=DEFAULT_MEDIAN_FLOOR_MINUTES)
    parser.add_argument("--body-file", type=Path, default=None,
                        help="corps actuel de l'issue de suivi (log precedent)")
    parser.add_argument("--now", default=None, help="horodatage ISO (tests/rejeux)")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    now = parse_time(args.now) if args.now else datetime.now(timezone.utc)
    try:
        runs = collect_window(args.repo, now, args.window_minutes)
    except MeasurementError as exc:
        print(f"BROKEN INSTRUMENT: {exc}", file=sys.stderr)
        return 2

    window_slow = find_slow_instances(
        runs, threshold=args.threshold, min_pool=args.min_pool,
        median_floor_minutes=args.median_floor_minutes,
    )
    prior_body = args.body_file.read_text(encoding="utf-8") if args.body_file else ""
    log = merge_log(parse_log_body(prior_body), window_slow, now)
    signals = evaluate_signals(log, min_hits=args.min_hits)

    verdict = {
        "window_minutes": args.window_minutes,
        "runs_measured": len(runs),
        "window_slow_runners": sorted(window_slow),
        "log_entries": len(log),
        "signals": signals,
        "next_body": render_log_body(log),
        "advisory": True,
    }
    if args.json:
        print(json.dumps(verdict, ensure_ascii=False, indent=1))
    else:
        print(f"runs mesures: {len(runs)} | runners lents (fenetre): "
              f"{len(window_slow)} | signaux (>= {args.min_hits} hits/24 h): {len(signals)}")
        for signal in signals:
            print(f"  SIGNAL {signal['runner']} (hote {signal['host']}) : "
                  f"{signal['hit_count']} instances lentes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
