#!/usr/bin/env python3
"""Characterize the self-hosted runner duration variance (#15574 items 1-2).

Collects completed jobs of a workflow from the GitHub Actions API (runner
name, start/end timestamps, conclusion), attributes each job to a physical
host via the runner-name prefix, and measures how job duration varies with:

  - the runner identity (per-runner median / p90),
  - the hour of day (nocturnal vs diurnal buckets),
  - the number of CPU-heavy jobs overlapping on the same host
    (co-residency, the mechanism suspected by #15574).

This is a measurement instrument, not a gate: exit code 0 means "measure
produced", 1 means operational failure (API unreadable). Nothing here turns
a PR red; the fleet governance decision belongs to #15574 item 3.

Usage:
  python scripts/ci/characterize_runner_variance.py --workflow scripts-tests.yml --days 14
  python scripts/ci/characterize_runner_variance.py --workflow scripts-tests.yml --json
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from statistics import median
from typing import Any, Callable

EXIT_OK = 0
EXIT_BROKEN = 1

DEFAULT_DAYS = 14
DEFAULT_WORKFLOW = "scripts-tests.yml"

# Familles de slots dont le cap CPU est "lourd" : la co-residence de CES
# familles est le mecanisme suspecte par #15574 (sur-souscription CPU de la
# VM hote). Les waiters (1 vCPU, essentiellement oisifs entre deux gates)
# sont exclus du decompte de charge : ils pollent, ils ne calculent pas.
HEAVY_RUNNER_TOKENS = ("-linux-docker-", "-lean-docker-")


def _default_runner(argv: list[str]) -> str:
    """gh api runner par defaut ; injectable pour les tests."""
    import subprocess

    proc = subprocess.run(argv, capture_output=True, text=True, encoding="utf-8", timeout=60)
    if proc.returncode != 0:
        raise RuntimeError(f"command failed rc={proc.returncode}: {argv[:3]}")
    return proc.stdout


def host_of(runner_name: str) -> str:
    """Attribue un job a son hote physique par prefixe de nom de runner.

    ``myia-po-2024-linux-docker-7`` -> ``myia-po-2024`` (les slots d'une
    meme famille partagent la VM) ; un nom sans tiret remains tel quel.
    Le suffixe familial (``-linux-docker-N`` / ``-lean-docker-N`` /
    ``-linux-waiter-N``) est l'unite de slot, pas d'hote (#15152 : le
    prefixe derive de la machine, pas d'un hote code en dur).
    """
    for token in HEAVY_RUNNER_TOKENS + ("-linux-waiter-",):
        idx = runner_name.find(token)
        if idx > 0:
            return runner_name[:idx]
    return runner_name


def is_heavy(runner_name: str) -> bool:
    """Un runner de la famille CPU-lourde (docker/lean) ou non."""
    return any(token in runner_name for token in HEAVY_RUNNER_TOKENS)


def _parse_ts(value: str) -> datetime | None:
    if not value:
        return None
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return None


def collect_jobs(
    repo: str,
    workflow: str,
    since: datetime,
    runner: Callable[[list[str]], str] = _default_runner,
    page_limit: int = 40,
) -> list[dict[str, Any]]:
    """Recupere les jobs COMPLETES du workflow sur la fenetre.

    Chaque job retenu porte : name, runner_name, host, heavy, conclusion,
    started_at, completed_at, duration_s. Les jobs sans runner (hosted,
    annulees avant placement) sont ecartees : elles ne disent rien de la
    variance du pool self-hosted.
    """
    jobs: list[dict[str, Any]] = []
    url = f"repos/{repo}/actions/workflows/{workflow}/runs"
    # Le qualificatif >= du filtre created DOIT etre percent-encode : un `>`
    # brut dans la query rend le filtre invalide cote GitHub, qui repond alors
    # zero run en silence (mesure : 2500 runs sans filtre, 0 avec `created>=`
    # brut).
    params = f"?status=completed&per_page=100&created=%3E%3D{since.date().isoformat()}"
    # gh api n'injecte PAS next_page_url dans le corps JSON (il vit dans
    # l'en-tete Link, invisible sans --include) : la pagination se pilote
    # par&page=N jusqu'a une page courte (mesure : sans cela, seule la
    # centaine de runs la plus recente est vue -- 165 jobs au lieu de la
    # fenetre complete).
    for page in range(1, page_limit + 1):
        sep = "&" if "?" in params else "?"
        payload = json.loads(runner(["gh", "api", f"{url}{params}{sep}page={page}"]))
        for run in payload.get("workflow_runs", []):
            # Pre-filtre de fenetre sur created_at : le endpoint LIST ne porte
            # pas completed_at de facon fiable (null mesure sur ce depot), et
            # le filtre API created>= borne deja la creation. Les horodatages
            # fins viennent des jobs, pas de cette entete.
            created = _parse_ts(run.get("created_at") or "")
            if created is None or created < since:
                continue
            run_id = run["id"]
            jobs_payload = json.loads(
                runner(["gh", "api", f"repos/{repo}/actions/runs/{run_id}/jobs?per_page=100"])
            )
            for job in jobs_payload.get("jobs", []):
                started = _parse_ts(job.get("started_at") or "")
                ended = _parse_ts(job.get("completed_at") or "")
                runner_name = job.get("runner_name") or ""
                if job.get("status") != "completed" or not runner_name:
                    continue
                if started is None or ended is None or ended <= started:
                    continue
                jobs.append(
                    {
                        "run_id": run_id,
                        "name": job.get("name") or "",
                        "runner_name": runner_name,
                        "host": host_of(runner_name),
                        "heavy": is_heavy(runner_name),
                        "conclusion": job.get("conclusion") or "",
                        "started_at": started.isoformat(),
                        "completed_at": ended.isoformat(),
                        "duration_s": (ended - started).total_seconds(),
                    }
                )
        if len(payload.get("workflow_runs", [])) < 100:
            break
    return jobs


def overlap_per_job(jobs: list[dict[str, Any]]) -> dict[int, int]:
    """Pour chaque job lourd (indice -> nombre d'AUTRES jobs lourds du meme
    hote qui le chevauchaient).

    C'est la grandeur que la decision item 3 de #15574 borne : un plafond
    de concurrence par hote se lit comme une borne sur cette distribution.
    """
    heavy_idx = [i for i, job in enumerate(jobs) if job["heavy"]]
    counts: dict[int, int] = {}
    for i in heavy_idx:
        start = _parse_ts(jobs[i]["started_at"])
        end = _parse_ts(jobs[i]["completed_at"])
        if start is None or end is None:
            counts[i] = 0
            continue
        overlaps = 0
        for j in heavy_idx:
            if j == i:
                continue
            o_start = _parse_ts(jobs[j]["started_at"])
            o_end = _parse_ts(jobs[j]["completed_at"])
            if o_start is None or o_end is None:
                continue
            if o_start < end and start < o_end:
                overlaps += 1
        counts[i] = overlaps
    return counts


def overlap_counts(jobs: list[dict[str, Any]]) -> dict[int, int]:
    """Histogramme du nombre de chevauchements (voir overlap_per_job)."""
    hist: dict[int, int] = defaultdict(int)
    for count in overlap_per_job(jobs).values():
        hist[count] += 1
    return dict(sorted(hist.items()))


def _percentile(values: list[float], pct: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    idx = min(len(ordered) - 1, max(0, round(pct * (len(ordered) - 1))))
    return ordered[idx]


def analyze(jobs: list[dict[str, Any]]) -> dict[str, Any]:
    """Agregats : par runner, par hote, par tranche horaire, par co-residence."""
    by_runner: dict[str, list[float]] = defaultdict(list)
    by_host: dict[str, list[float]] = defaultdict(list)
    by_hour: dict[int, list[float]] = defaultdict(list)
    for job in jobs:
        started = _parse_ts(job["started_at"])
        if started is None:
            continue
        by_runner[job["runner_name"]].append(job["duration_s"])
        by_host[job["host"]].append(job["duration_s"])
        by_hour[started.hour].append(job["duration_s"])

    # Correlation durant : mediane des durees par nombre de chevauchements
    # lourds -- LE chiffre que l'arbitrage item 3 regarde (combien coute un
    # voisin CPU-lourd sur le meme hote).
    per_overlap: dict[str, list[float]] = defaultdict(list)
    for idx, count in overlap_per_job(jobs).items():
        bucket = str(count) if count < 3 else "3+"
        per_overlap[bucket].append(jobs[idx]["duration_s"])

    def _stats(values: list[float]) -> dict[str, float]:
        return {
            "n": len(values),
            "median_s": round(median(values), 1) if values else 0.0,
            "p90_s": round(_percentile(values, 0.9), 1),
        }

    order = {"3+": 3}
    overlap_keys = sorted(per_overlap.keys(), key=lambda k: order.get(k, None) or int(k))
    return {
        "jobs_total": len(jobs),
        "jobs_heavy": sum(1 for job in jobs if job["heavy"]),
        "per_runner": {k: _stats(v) for k, v in sorted(by_runner.items())},
        "per_host": {k: _stats(v) for k, v in sorted(by_host.items())},
        "per_hour": {str(k): _stats(v) for k, v in sorted(by_hour.items())},
        "per_overlap": {k: _stats(per_overlap[k]) for k in overlap_keys},
        "overlap_histogram": overlap_counts(jobs),
        "median_s": round(median([job["duration_s"] for job in jobs]), 1) if jobs else 0.0,
    }


def format_report(analysis: dict[str, Any]) -> str:
    lines = [
        f"jobs: {analysis['jobs_total']} (lourds docker/lean: {analysis['jobs_heavy']})",
        f"duree mediane globale: {analysis['median_s']} s",
        "",
        "par runner (n / mediane / p90, en s) :",
    ]
    for name, stats in analysis["per_runner"].items():
        lines.append(f"  {name:38s} {stats['n']:4d}  {stats['median_s']:9.1f}  {stats['p90_s']:9.1f}")
    lines.append("")
    lines.append("par hote (n / mediane / p90, en s) :")
    for name, stats in analysis["per_host"].items():
        lines.append(f"  {name:38s} {stats['n']:4d}  {stats['median_s']:9.1f}  {stats['p90_s']:9.1f}")
    lines.append("")
    lines.append("histogramme de co-residence (jobs lourds chevauches sur le meme hote) :")
    for count, jobs_n in analysis["overlap_histogram"].items():
        lines.append(f"  {count} chevauchement(s) : {jobs_n} job(s)")
    lines.append("")
    lines.append("duree par co-residence (n / mediane / p90, en s) -- le cout d'un voisin lourd :")
    for bucket, stats in analysis.get("per_overlap", {}).items():
        lines.append(f"  {bucket} chevauchement(s) : {stats['n']:4d}  {stats['median_s']:9.1f}  {stats['p90_s']:9.1f}")
    lines.append("")
    lines.append("par heure locale de demarrage (mediane, en s) :")
    for hour, stats in analysis["per_hour"].items():
        lines.append(f"  {hour}h  {stats['n']:4d}  {stats['median_s']:9.1f}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", default="jsboige/CoursIA")
    parser.add_argument("--workflow", default=DEFAULT_WORKFLOW)
    parser.add_argument("--days", type=int, default=DEFAULT_DAYS)
    parser.add_argument("--json", action="store_true", help="sortie JSON brute")
    args = parser.parse_args(argv)

    since = datetime.now(timezone.utc) - timedelta(days=args.days)
    try:
        jobs = collect_jobs(args.repo, args.workflow, since)
        analysis = analyze(jobs)
    except (RuntimeError, json.JSONDecodeError) as exc:
        print(f"[PANNE] collecte impossible : {exc}", file=sys.stderr)
        return EXIT_BROKEN

    if args.json:
        print(json.dumps({"workflow": args.workflow, "window_days": args.days, **analysis}, indent=2))
    else:
        print(format_report(analysis))
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
