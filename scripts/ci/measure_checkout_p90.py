"""Mesure de la duree de l'etape de checkout, par workflow (lecture seule, REST).

Usage :
    python scripts/ci/measure_checkout_p90.py --hours 24 [--out .tmp/checkout.json]
    python scripts/ci/measure_checkout_p90.py --runs 40 --workflow scripts-tests.yml

Ce que ca mesure : la duree de l'etape `actions/checkout` de chaque job, et la
duree totale du job. La premiere est le cout du checkout proprement dit ; la
seconde montre ce que le checkout represente du job.

Ce que ca ne mesure pas : l'attente du runner (le job est en file avant sa
premiere etape) ni le temps d'une eventualle etape de heal qui precede le
checkout -- cette derniere est explicitement hors du perimetre, et c'est elle
que la phase P1 ameliore.

Limites annoncees :
- la pagination de l'API Actions est plafonnee a 1 000 resultats filtres ; la
  fenetre reellement couverte se deduit des runs eux-memes, jamais d'un
  `total_count` ;
- le nom de l'etape de checkout a change selon la version de l'action
  ("Checkout repository", "actions/checkout@v4") : les deux formes sont
  reconnues, et une job sans etape reconnue est comptee a part ;
- la duree d'une etape est `completed_at - started_at` : elle inclut le
  telechargement des blobs paresseux, qui est le poste dominant en cas de
  work dir reuse.
"""
from __future__ import annotations

import argparse
import json
import statistics
import subprocess
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path

REPO = "jsboige/CoursIA"
FMT = "%Y-%m-%dT%H:%M:%SZ"
CHECKOUT_NAMES = ("checkout repository", "actions/checkout")


def gh(path: str) -> dict:
    out = subprocess.run(
        ["gh", "api", path],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if out.returncode != 0:
        raise RuntimeError(f"gh api failed: {path}: {out.stderr[:200]}")
    return json.loads(out.stdout)


def ts(value: str | None) -> datetime | None:
    if not value:
        return None
    return datetime.strptime(value, FMT).replace(tzinfo=timezone.utc)


def minutes(start: str | None, end: str | None) -> float | None:
    a, b = ts(start), ts(end)
    if not a or not b or b < a:
        return None
    return (b - a).total_seconds() / 60.0


def percentile(values: list[float], fraction: float) -> float:
    ordered = sorted(values)
    if not ordered:
        return 0.0
    index = int(fraction * (len(ordered) - 1))
    return ordered[index]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--hours", type=int, default=24)
    parser.add_argument("--runs", type=int, default=60, help="runs inspectes au plus")
    parser.add_argument("--workflow", default="", help="filtre sur le nom du workflow")
    parser.add_argument("--out", default="")
    args = parser.parse_args()

    since = (datetime.now(timezone.utc) - timedelta(hours=args.hours)).strftime(FMT)
    runs: list[dict] = []
    page = 1
    while page <= 10 and len(runs) < args.runs:
        data = gh(
            f"/repos/{REPO}/actions/runs?event=pull_request&created%3E={since}"
            f"&per_page=100&page={page}"
        )
        batch = data.get("workflow_runs", [])
        runs.extend(batch)
        if len(batch) < 100:
            break
        page += 1

    if args.workflow:
        runs = [r for r in runs if r.get("name") == args.workflow]
    runs = runs[: args.runs]

    per_workflow: dict[str, dict] = defaultdict(
        lambda: {"jobs": 0, "jobs_sans_checkout": 0, "checkout": [], "job": []}
    )
    for run in runs:
        try:
            jobs = gh(f"/repos/{REPO}/actions/runs/{run['id']}/jobs?per_page=100").get("jobs", [])
        except RuntimeError:
            continue
        for job in jobs:
            bucket = per_workflow[run.get("name", "?")]
            bucket["jobs"] += 1
            total = minutes(job.get("started_at"), job.get("completed_at"))
            if total is not None:
                bucket["job"].append(total)
            found = None
            for step in job.get("steps") or []:
                name = (step.get("name") or "").strip().lower()
                if any(marker in name for marker in CHECKOUT_NAMES):
                    found = minutes(step.get("started_at"), step.get("completed_at"))
                    break
            if found is None:
                bucket["jobs_sans_checkout"] += 1
            else:
                bucket["checkout"].append(found)

    rows = []
    for name, bucket in per_workflow.items():
        checkout = bucket["checkout"]
        rows.append(
            {
                "workflow": name,
                "jobs": bucket["jobs"],
                "jobs_sans_etape_checkout": bucket["jobs_sans_checkout"],
                "checkout_med_min": round(statistics.median(checkout), 2) if checkout else None,
                "checkout_p90_min": round(percentile(checkout, 0.9), 2) if checkout else None,
                "checkout_max_min": round(max(checkout), 2) if checkout else None,
                "job_med_min": round(statistics.median(bucket["job"]), 2) if bucket["job"] else None,
                "job_p90_min": round(percentile(bucket["job"], 0.9), 2) if bucket["job"] else None,
            }
        )
    rows.sort(key=lambda r: -(r["checkout_p90_min"] or 0))

    covered = [ts(r.get("created_at")) for r in runs if r.get("created_at")]
    report = {
        "repo": REPO,
        "measured_at": datetime.now(timezone.utc).strftime(FMT),
        "window_requested_hours": args.hours,
        "window_created_since": since,
        "runs_inspectes": len(runs),
        "window_covered": {
            "from": min(covered).strftime(FMT) if covered else None,
            "to": max(covered).strftime(FMT) if covered else None,
        },
        "rows": rows,
    }
    text = json.dumps(report, indent=2, ensure_ascii=False)
    if args.out:
        out = Path(args.out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(text + "\n", encoding="utf-8")
        print(f"ecrit : {out}")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
