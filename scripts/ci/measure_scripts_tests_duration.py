#!/usr/bin/env python3
"""Mesure la duree du job `Scripts Tests (CPU)` sur une branche, avant et apres un instant.

Le grain est la **duree de job** lue a la source (API Actions : `started_at` ->
`completed_at` du job), pas une estimation. Le script separe les runs en deux
groupes autour d'un instant de coupure (`--split`), ce qui permet de mesurer
l'effet d'une modification de la borne xdist (#27167) sur `main`.

Echantillonnage : les runs `cancelled` sont **exclus** (un push suivant annule
le run precedent : sa duree ne mesure rien), de meme que les jobs non
termines. Les conclusions `failure` sont **conservees** : un job qui echoue
apres N minutes a bien dure N minutes.

Sortie : JSON sur stdout, ou `--out <fichier>`.

Usage :
    python scripts/ci/measure_scripts_tests_duration.py \
        --branch main --split 2026-11-18T04:25:19Z --out scripts/results/x.json
"""

from __future__ import annotations

import argparse
import json
import os
import statistics
import subprocess
import sys
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Any

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_WORKFLOW = "scripts-tests.yml"
DEFAULT_JOB = "Scripts Tests (CPU)"
API = "https://api.github.com"


def _token() -> str:
    """Jeton GitHub : `GH_TOKEN` si present, sinon le trousseau `gh` de l'utilisateur demande."""
    env = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if env:
        return env.strip()
    user = os.environ.get("GH_USER", "jsboige")
    out = subprocess.run(
        ["gh", "auth", "token", "--user", user],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=True,
    )
    return out.stdout.strip()


class Actions:
    """Client REST minimal de l'API Actions (lecture seule)."""

    def __init__(self, repo: str, token: str) -> None:
        self.repo = repo
        self._headers = {
            "Authorization": f"token {token}",
            "Accept": "application/vnd.github+json",
            "User-Agent": "coursia-lane",
        }

    def get(self, path: str, **params: Any) -> Any:
        query = "&".join(f"{k}={v}" for k, v in params.items() if v is not None)
        url = f"{API}{path}" + (f"?{query}" if query else "")
        request = urllib.request.Request(url, headers=self._headers)
        with urllib.request.urlopen(request, timeout=60) as response:
            return json.loads(response.read().decode("utf-8"))

    def runs(self, workflow: str, branch: str, limit: int) -> list[dict[str, Any]]:
        found: list[dict[str, Any]] = []
        page = 1
        while len(found) < limit:
            batch = self.get(
                f"/repos/{self.repo}/actions/workflows/{workflow}/runs",
                branch=branch,
                per_page=min(100, limit),
                page=page,
            )
            items = batch.get("workflow_runs", [])
            if not items:
                break
            found.extend(items)
            page += 1
        return found[:limit]

    def jobs(self, run_id: int) -> list[dict[str, Any]]:
        return self.get(f"/repos/{self.repo}/actions/runs/{run_id}/jobs", per_page=100).get("jobs", [])


@dataclass
class Measurement:
    """Une mesure de duree de job."""

    run_id: int
    head_sha: str
    created_at: str
    job: str
    conclusion: str
    started_at: str
    completed_at: str
    duration_s: float
    group: str = "before"
    extra: dict[str, Any] = field(default_factory=dict)


def _parse(ts: str) -> datetime:
    return datetime.fromisoformat(ts.replace("Z", "+00:00"))


def collect(
    api: Actions, workflow: str, branch: str, job_name: str, limit: int, split: datetime
) -> list[Measurement]:
    """Relit les runs de la branche et retient la duree du job vise."""
    measurements: list[Measurement] = []
    for run in api.runs(workflow, branch, limit):
        if run.get("head_branch") != branch:
            continue
        for job in api.jobs(int(run["id"])):
            if job.get("name") != job_name:
                continue
            started = job.get("started_at")
            completed = job.get("completed_at")
            if not started or not completed:
                continue
            if job.get("conclusion") == "cancelled":
                continue
            duration = (_parse(completed) - _parse(started)).total_seconds()
            measurements.append(
                Measurement(
                    run_id=int(run["id"]),
                    head_sha=(run.get("head_sha") or "")[:12],
                    created_at=run.get("created_at") or "",
                    job=job_name,
                    conclusion=job.get("conclusion") or "",
                    started_at=started,
                    completed_at=completed,
                    duration_s=duration,
                    group="after" if _parse(started) >= split else "before",
                )
            )
    return measurements


def stats(values: list[float]) -> dict[str, Any]:
    """Statistiques de duree : effectif, mediane, moyenne, etendue."""
    if not values:
        return {"n": 0, "median_s": None, "mean_s": None, "min_s": None, "max_s": None}
    return {
        "n": len(values),
        "median_s": round(statistics.median(values), 1),
        "mean_s": round(statistics.fmean(values), 1),
        "min_s": round(min(values), 1),
        "max_s": round(max(values), 1),
    }


def build_report(
    measurements: list[Measurement],
    *,
    repo: str,
    workflow: str,
    branch: str,
    job: str,
    split: str,
) -> dict[str, Any]:
    """Assemble le rapport : groupes avant/apres, repartition par conclusion, mesures."""
    before = [m.duration_s for m in measurements if m.group == "before"]
    after = [m.duration_s for m in measurements if m.group == "after"]
    by_conclusion: dict[str, dict[str, Any]] = {}
    for m in measurements:
        key = f"{m.group}:{m.conclusion or 'unknown'}"
        by_conclusion.setdefault(key, {"durations_s": []})["durations_s"].append(m.duration_s)
    return {
        "generated_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "repo": repo,
        "workflow": workflow,
        "branch": branch,
        "job": job,
        "split": split,
        "runs_excluded_cancelled": True,
        "before": stats(before),
        "after": stats(after),
        "by_conclusion": {
            key: stats(values["durations_s"]) for key, values in sorted(by_conclusion.items())
        },
        "measurements": [
            {
                "run_id": m.run_id,
                "head_sha": m.head_sha,
                "created_at": m.created_at,
                "conclusion": m.conclusion,
                "started_at": m.started_at,
                "completed_at": m.completed_at,
                "duration_s": m.duration_s,
                "group": m.group,
            }
            for m in measurements
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--workflow", default=DEFAULT_WORKFLOW)
    parser.add_argument("--branch", default="main")
    parser.add_argument("--job", default=DEFAULT_JOB)
    parser.add_argument("--split", required=True, help="Instant ISO 8601 de la coupure (inclus : apres)")
    parser.add_argument("--limit", type=int, default=40, help="Nombre maximal de runs lus")
    parser.add_argument("--out", default=None, help="Fichier JSON de sortie")
    args = parser.parse_args(argv)

    split = _parse(args.split)
    api = Actions(args.repo, _token())
    try:
        measurements = collect(api, args.workflow, args.branch, args.job, args.limit, split)
    except urllib.error.HTTPError as exc:
        print(f"API Actions inaccessible : {exc}", file=sys.stderr)
        return 2

    report = build_report(
        measurements,
        repo=args.repo,
        workflow=args.workflow,
        branch=args.branch,
        job=args.job,
        split=args.split,
    )

    payload = json.dumps(report, indent=2, ensure_ascii=False)
    if args.out:
        with open(args.out, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(payload + "\n")
    print(payload)
    return 0


if __name__ == "__main__":
    sys.exit(main())
