"""Mesure de la duree de l'etape de checkout, par workflow (lecture seule, REST).

Usage :
    python scripts/ci/measure_checkout_p90.py --hours 24 [--out .tmp/checkout.json]
    python scripts/ci/measure_checkout_p90.py --runs 40 --workflow scripts-tests.yml

Ce que ca mesure :
- la duree de l'etape `actions/checkout` de chaque job ;
- la duree de l'etape de **heal** qui precede le checkout dans les quatre
  workflows `always-on-*` ("Purger un work dir reutilise...") ;
- la **somme des deux**, qui est le vrai cout d'entree du job ;
- la duree totale du job.

Ce que ca ne mesure pas : l'attente du runner (le job est en file avant sa
premiere etape). C'est le seul poste que l'instrument ne voit pas, et c'est
celui que la mesure du 2026-11-09 a designe comme dominant (p90 du job a
7,65 min, p90 de l'etape de checkout a 1,07 min).

L'etape de heal n'est plus **exclue** du perimetre : la phase P1 deplace le
cout du checkout vers le heal (l'unshallow est tente avant `actions/checkout`),
et un instrument qui ne verrait que le checkout lirait ce deplacement comme
un gain. C'est pourquoi la somme heal + checkout est rendue.

Limites annoncees :
- la pagination de l'API Actions est plafonnee a 1 000 resultats filtres ; la
  fenetre reellement couverte se deduit des runs eux-memes, jamais d'un
  `total_count` ;
- le nom de l'etape de checkout a change selon la version de l'action
  ("Checkout repository", "actions/checkout") : les deux formes sont
  reconnues, et une job sans etape reconnue est comptee a part ;
- la duree d'une etape est `completed_at - started_at` : elle inclut le
  telechargement des blobs paresseux, qui est le poste dominant en cas de
  work dir reuse.

Ce que ca rend, en plus des percentiles : la **part du checkout dans le p90
du job** (`checkout_share_du_job_p90`), qui dit si le checkout est le poste
dominant ou si le job passe son temps ailleurs -- attente de runner comprise
-- la meme part pour le **cout d'entree** (heal + checkout), et la **liste des
checkouts lents** au-dessus du seuil `--slow-min` (defaut 3 min), qui est la
seule maniere de voir une pathologie rare dans une fenetre courte.
"""
from __future__ import annotations

import argparse
import json
import statistics
import subprocess
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import quote

REPO = "jsboige/CoursIA"
FMT = "%Y-%m-%dT%H:%M:%SZ"
CHECKOUT_NAMES = ("checkout repository", "actions/checkout")
#: L'etape de heal du work dir reutilise, presente dans les quatre
#: workflows `always-on-*` ("Purger un work dir reutilise au graphe
#: incomplet (#15387)"). Le marqueur est le debut du nom : la queue du nom
#: (le numero d'issue) peut changer sans que la mesure perde son objet.
HEAL_NAMES = ("purger un work dir",)


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


def runs_url(since: str, page: int, event: str = "pull_request") -> str:
    """L'URL de lecture des runs, fenetre **reellement appliquee**.

    L'API Actions attend la cle `created` avec l'operateur `>=` : la forme
    est donc `created=%3E%3D{since}`. La forme `created%3E={since}` se decode
    en une cle `created>` -- que l'API ignore : le filtre ne porte alors sur
    rien et l'instrument mesure n'importe quelle fenetre. Mesure du
    2026-11-09 sur la meme fenetre de 2 h : 2 500 runs non filtres contre
    733 filtres.

    La chaine est **construite ici** et non concatenee dans l'appel : c'est
    ce qui permet a un test de verifier la forme reellement envoyee, sans
    appel reseau.
    """
    return (
        f"/repos/{REPO}/actions/runs?event={event}"
        f"&created=%3E%3D{quote(since)}&per_page=100&page={page}"
    )


def step_minutes(steps: list[dict] | None, markers: tuple[str, ...]) -> float | None:
    """Duree de la premiere etape dont le nom porte un des marqueurs.

    Fonction pure : elle raisonne sur les etapes rendues par l'API, sans
    les appeler. `None` signifie « aucune etape reconnue » — ce qui n'est
    pas « une etape de duree nulle ».
    """
    for step in steps or []:
        name = (step.get("name") or "").strip().lower()
        if any(marker in name for marker in markers):
            return minutes(step.get("started_at"), step.get("completed_at"))
    return None


def _bucket() -> dict:
    return {
        "jobs": 0,
        "jobs_sans_checkout": 0,
        "jobs_sans_heal": 0,
        "checkout": [],
        "heal": [],
        "entree": [],
        "job": [],
    }


def _median(values: list[float]) -> float | None:
    return round(statistics.median(values), 2) if values else None


def _p90(values: list[float]) -> float | None:
    if not values:
        return None
    return round(percentile(values, 0.9), 2)


def _max(values: list[float]) -> float | None:
    return round(max(values), 2) if values else None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--hours", type=int, default=24)
    parser.add_argument("--runs", type=int, default=60, help="runs inspectes au plus")
    parser.add_argument("--workflow", default="", help="filtre sur le nom du workflow")
    parser.add_argument("--slow-min", type=float, default=3.0, help="seuil d'un checkout lent")
    parser.add_argument("--out", default="")
    args = parser.parse_args()

    since = (datetime.now(timezone.utc) - timedelta(hours=args.hours)).strftime(FMT)
    runs: list[dict] = []
    page = 1
    while page <= 10 and len(runs) < args.runs:
        data = gh(runs_url(since, page))
        batch = data.get("workflow_runs", [])
        runs.extend(batch)
        if len(batch) < 100:
            break
        page += 1

    if args.workflow:
        runs = [r for r in runs if r.get("name") == args.workflow]
    runs = runs[: args.runs]

    per_workflow: dict[str, dict] = defaultdict(_bucket)
    slow: list[dict] = []
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
            steps = job.get("steps") or []
            found = step_minutes(steps, CHECKOUT_NAMES)
            heal = step_minutes(steps, HEAL_NAMES)
            if heal is None:
                bucket["jobs_sans_heal"] += 1
            else:
                bucket["heal"].append(heal)
            if found is None:
                bucket["jobs_sans_checkout"] += 1
            else:
                bucket["checkout"].append(found)
            # Le cout d'entree : ce que le job paie AVANT de produire quoi que
            # ce soit. Un etage de heal absent compte pour zero -- et le
            # compteur `jobs_sans_heal` dit combien de jobs sont dans ce cas,
            # pour que la somme ne se lise pas comme une mesure complete.
            entree = (found or 0.0) + (heal or 0.0)
            bucket["entree"].append(entree)
            if found is not None and found >= args.slow_min:
                slow.append(
                    {
                        "workflow": run.get("name"),
                        "run_id": run.get("id"),
                        "job_id": job.get("id"),
                        "checkout_min": round(found, 2),
                        "heal_min": round(heal, 2) if heal is not None else None,
                        "entree_min": round(entree, 2),
                        "job_min": round(total, 2) if total is not None else None,
                    }
                )

    rows = []
    for name, bucket in per_workflow.items():
        checkout = bucket["checkout"]
        ck_p90 = percentile(checkout, 0.9) if checkout else None
        job_p90 = percentile(bucket["job"], 0.9) if bucket["job"] else None
        entry_p90 = percentile(bucket["entree"], 0.9) if bucket["entree"] else None
        rows.append(
            {
                "workflow": name,
                "jobs": bucket["jobs"],
                "jobs_sans_etape_checkout": bucket["jobs_sans_checkout"],
                "jobs_sans_etape_heal": bucket["jobs_sans_heal"],
                "checkout_med_min": _median(checkout),
                "checkout_p90_min": _p90(checkout),
                "checkout_max_min": _max(checkout),
                "heal_med_min": _median(bucket["heal"]),
                "heal_p90_min": _p90(bucket["heal"]),
                "heal_max_min": _max(bucket["heal"]),
                "entree_med_min": _median(bucket["entree"]),
                "entree_p90_min": _p90(bucket["entree"]),
                "entree_max_min": _max(bucket["entree"]),
                "job_med_min": _median(bucket["job"]),
                "job_p90_min": _p90(bucket["job"]),
                # Part du checkout dans le p90 du job : c'est le nombre qui
                # dit si le checkout est le poste dominant ou si le job passe
                # son temps ailleurs (attente de runner comprise).
                "checkout_share_du_job_p90": (
                    round(ck_p90 / job_p90, 3) if ck_p90 and job_p90 else None
                ),
                # Meme part pour le cout d'entree (heal + checkout).
                "entree_share_du_job_p90": (
                    round(entry_p90 / job_p90, 3) if entry_p90 and job_p90 else None
                ),
            }
        )
    rows.sort(key=lambda r: -(r["checkout_p90_min"] or 0))
    slow.sort(key=lambda item: -item["checkout_min"])

    covered = [ts(r.get("created_at")) for r in runs if r.get("created_at")]
    report = {
        "repo": REPO,
        "measured_at": datetime.now(timezone.utc).strftime(FMT),
        "window_requested_hours": args.hours,
        "window_created_since": since,
        "runs_inspectes": len(runs),
        "seuil_checkout_lent_min": args.slow_min,
        "checkouts_lents": len(slow),
        "checkouts_lents_detail": slow[:40],
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
