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
- les requetes sont decoupees en fenetres de creation bornees pour eviter
  le plafond de 1 000 runs ; une seconde contenant plus de 1 000 runs ne
  peut pas etre subdivisee et provoque une erreur explicite ;
- `--runs` borne les runs inspectes apres filtrage du workflow : le rapport
  indique si la fenetre a ete parcourue entierement. Les dates observees
  ne prouvent pas a elles seules la couverture ; les suppressions ou
  modifications concurrentes cote API peuvent affecter la collecte ;
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


def runs_url(since: str, page: int, event: str = "pull_request", *, until: str | None = None) -> str:
    """URL Actions : le filtre `created` est une valeur, pas une cle."""
    created = f"{since}..{until}" if until is not None else f">={since}"
    return (
        f"/repos/{REPO}/actions/runs?event={event}"
        f"&created={quote(created, safe='')}&per_page=100&page={page}"
    )


def collect_runs(start: datetime, end: datetime, limit: int, workflow: str = "") -> tuple[list[dict], bool]:
    """Collecte du plus recent au plus ancien, bornes inclusives a la seconde.

    Un temoin supplementaire permet de distinguer une limite atteinte d'une
    fenetre complete. Les fenetres filles sont disjointes, meme aux bornes.
    """
    found: list[dict] = []
    seen: set[int] = set()

    def visit(lo: datetime, hi: datetime) -> bool:
        first = gh(runs_url(lo.strftime(FMT), 1, until=hi.strftime(FMT)))
        count = first.get("total_count")
        if not isinstance(count, int) or isinstance(count, bool) or count < 0:
            raise RuntimeError("total_count des runs invalide")
        if count > 1000:
            if lo == hi:
                raise RuntimeError(f"plus de 1000 runs a la meme seconde : {lo.strftime(FMT)}")
            middle = lo + timedelta(seconds=int((hi - lo).total_seconds()) // 2)
            return visit(middle + timedelta(seconds=1), hi) and visit(lo, middle)

        batch = first.get("workflow_runs")
        if not isinstance(batch, list):
            raise RuntimeError("liste des runs invalide")
        all_runs = list(batch)
        for page in range(2, (count + 99) // 100 + 1):
            data = gh(runs_url(lo.strftime(FMT), page, until=hi.strftime(FMT)))
            if data.get("total_count") != count or not isinstance(data.get("workflow_runs"), list):
                raise RuntimeError("pagination des runs incoherente")
            all_runs.extend(data["workflow_runs"])
        if len(all_runs) != count:
            raise RuntimeError("nombre de runs incoherent avec total_count")
        for run in all_runs:
            try:
                run_id = run["id"]
                created = ts(run["created_at"])
                if not isinstance(run_id, int) or created is None or not lo <= created <= hi:
                    raise ValueError
            except (KeyError, TypeError, ValueError) as exc:
                raise RuntimeError("run invalide ou hors fenetre") from exc
            if run_id in seen:
                raise RuntimeError("run duplique pendant la pagination")
            seen.add(run_id)
            if not workflow or run.get("name") == workflow:
                found.append(run)
                if len(found) > limit:
                    return False
        return True

    complete = visit(start, end)
    return found[:limit], complete


def collect_jobs(run_id: int) -> list[dict]:
    """Toutes les pages de jobs ou une erreur, jamais un resultat partiel muet."""
    jobs: list[dict] = []
    seen: set[int] = set()
    page = 1
    expected = None
    while True:
        data = gh(f"/repos/{REPO}/actions/runs/{run_id}/jobs?per_page=100&page={page}")
        count, batch = data.get("total_count"), data.get("jobs")
        if not isinstance(count, int) or isinstance(count, bool) or count < 0 or not isinstance(batch, list):
            raise RuntimeError(f"pagination des jobs invalide pour {run_id}")
        if expected is None:
            expected = count
        if count != expected or len(jobs) + len(batch) > count:
            raise RuntimeError(f"pagination des jobs incoherente pour {run_id}")
        for job in batch:
            job_id = job.get("id") if isinstance(job, dict) else None
            if not isinstance(job_id, int) or isinstance(job_id, bool) or job_id <= 0:
                raise RuntimeError(f"ID de job invalide pour {run_id}")
            if job_id in seen:
                raise RuntimeError(f"job duplique pendant la pagination pour {run_id}: {job_id}")
            seen.add(job_id)
        jobs.extend(batch)
        if len(jobs) == expected:
            return jobs
        if not batch:
            raise RuntimeError(f"pagination des jobs incomplete pour {run_id}")
        page += 1


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

    if args.hours <= 0 or args.runs <= 0:
        parser.error("--hours et --runs doivent etre strictement positifs")
    end = datetime.now(timezone.utc).replace(microsecond=0)
    start = end - timedelta(hours=args.hours)
    since = start.strftime(FMT)
    runs, complete = collect_runs(start, end, args.runs, args.workflow)

    per_workflow: dict[str, dict] = defaultdict(_bucket)
    slow: list[dict] = []
    for run in runs:
        jobs = collect_jobs(run["id"])
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
        "window_created_until": end.strftime(FMT),
        "workflow_filter": args.workflow or None,
        "runs_limit": args.runs,
        "window_complete": complete,
        "window_complete_note": (
            "Toutes les pages filtrees ont ete lues ; les changements concurrents cote API restent possibles."
            if complete else "Limite --runs atteinte ; la fenetre n'est pas couverte entierement."
        ),
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
