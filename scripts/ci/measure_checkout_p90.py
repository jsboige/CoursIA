"""Mesure de la duree de l'etape de checkout, par workflow (lecture seule, REST).

Usage :
    python scripts/ci/measure_checkout_p90.py --hours 24 [--out .tmp/checkout.json]
    python scripts/ci/measure_checkout_p90.py --runs 40 --workflow scripts-tests.yml
    python scripts/ci/measure_checkout_p90.py --hours 24 --sample 300 --event all --out .tmp/checkout.json

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
  reconnues, et une job sans etape reconnue est comptee a part ; une etape
  de checkout sans duree mesurable (job annule avant sa fin) l'est aussi,
  et n'est jamais lue comme une part nulle ;
- la duree d'une etape est `completed_at - started_at` : elle inclut le
  telechargement des blobs paresseux, qui est le poste dominant en cas de
  work dir reuse.

Ce que ca rend, en plus des percentiles : la **part du checkout dans le p90
du job** (`checkout_share_du_job_p90`), qui dit si le checkout est le poste
dominant ou si le job passe son temps ailleurs -- attente de runner comprise
-- la meme part pour le **cout d'entree** (heal + checkout), et la **liste des
checkouts lents** au-dessus du seuil `--slow-min` (defaut 3 min), qui est la
seule maniere de voir une pathologie rare dans une fenetre courte.

Echantillon et part mediane (critere de sortie de #22469) :
- sans `--sample`, `--runs` prend les N runs **les plus recents** de la fenetre :
  ce n'est pas un echantillon de la fenetre, et la mediane lue ne vaut que pour
  les dernieres heures couvertes ;
- avec `--sample N`, la fenetre entiere est listee (peu couteux), puis N runs
  sont tires **au hasard, sans remise, sur toute la fenetre**, avec la graine
  `--seed` (defaut 20261125). Seuls les runs tires paient un appel `/jobs`.
  Le bloc `selection` du rapport dit la methode, le nombre de runs de la
  fenetre, le taux d'inspection et le facteur d'extrapolation ;
- le bloc `part_du_checkout` rend la mediane, le p90 et la part du temps total
  de la **part du checkout par job** (duree de l'etape / duree du job) sous
  deux populations, parce que le critere ne dit pas laquelle il vise :
  `tous_les_jobs` (un job sans etape de checkout compte pour une part nulle)
  et `jobs_avec_etape_checkout`. En mode `--sample`, chacune porte un
  intervalle a 95 % par bootstrap au niveau du run ;
- `--event` borne les runs a un declencheur (`pull_request` par defaut,
  comportement historique ; `all` = aucun filtre). La population est inscrite
  au rapport (`event_filter`) : une mesure sur les seuls runs `pull_request`
  n'est pas celle de toute l'activite CI.
"""
from __future__ import annotations

import argparse
import json
import random
import statistics
import subprocess
import time
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
#: Nombre d'essais d'un appel REST et pause de base entre deux essais. Une
#: mesure de plusieurs minutes ne doit pas se perdre sur une erreur serveur
#: isolee ; un quota epuise, lui, ne se repare pas en attendant quelques
#: secondes, et echoue des le premier essai.
ESSAIS = 3
PAUSE_S = 1.0


def gh(path: str) -> dict:
    out = None
    for essai in range(1, ESSAIS + 1):
        out = subprocess.run(
            ["gh", "api", path],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
        if out.returncode == 0:
            break
        if "rate limit" in out.stderr.lower():
            break
        if essai < ESSAIS:
            time.sleep(PAUSE_S * essai)
    if out is None or out.returncode != 0:
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
    """URL Actions : le filtre `created` est une valeur, pas une cle.

    `event` vide ne porte aucun filtre de declencheur : l'URL decrit alors
    les runs de tous les evenements.
    """
    created = f"{since}..{until}" if until is not None else f">={since}"
    trigger = f"event={event}&" if event else ""
    return (
        f"/repos/{REPO}/actions/runs?{trigger}"
        f"created={quote(created, safe='')}&per_page=100&page={page}"
    )


def collect_runs(
    start: datetime,
    end: datetime,
    limit: int | None,
    workflow: str = "",
    event: str = "pull_request",
) -> tuple[list[dict], bool]:
    """Collecte du plus recent au plus ancien, bornes incluses a la seconde.

    Un temoin supplementaire permet de distinguer une limite atteinte d'une
    fenetre complete. Les fenetres filles sont disjointes, meme aux bornes.
    `limit=None` garde tous les runs de la fenetre.
    """
    found: list[dict] = []
    seen: set[int] = set()

    def visit(lo: datetime, hi: datetime) -> bool:
        first = gh(runs_url(lo.strftime(FMT), 1, event, until=hi.strftime(FMT)))
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
            data = gh(runs_url(lo.strftime(FMT), page, event, until=hi.strftime(FMT)))
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
                if limit is not None and len(found) > limit:
                    return False
        return True

    complete = visit(start, end)
    return found if limit is None else found[:limit], complete


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


def draw_sample(runs: list[dict], size: int, seed: int) -> list[dict]:
    """Tirage uniforme sans remise, reproductible par la graine.

    Fonction pure. Un tirage plus grand que la population rend toute la
    population. Les runs sont tries par le serveur du plus recent au plus
    ancien : l'ordre de la liste ne doit pas influencer le resultat au-dela
    de ce que la graine fixe.
    """
    if size >= len(runs):
        return list(runs)
    return random.Random(seed).sample(runs, size)


def bootstrap_median_ci(
    per_run: list[list[float]], seed: int, resamples: int = 1000
) -> list[float] | None:
    """Intervalle a 95 % de la mediane des parts, par bootstrap au niveau du run.

    Les jobs d'un meme run ne sont pas independants (meme commit, memes
    conditions de runner) : tirer les runs avec remise et mettre en commun
    leurs jobs respecte cette structure, la ou un tirage de jobs la nie.
    Fonction pure, reproductible par la graine ; `None` sous deux valeurs.
    """
    values = [value for group in per_run for value in group]
    if len(values) < 2:
        return None
    rng = random.Random(seed)
    medians: list[float] = []
    for _ in range(resamples):
        drawn = rng.choices(per_run, k=len(per_run))
        pooled = [value for group in drawn for value in group]
        if pooled:
            medians.append(statistics.median(pooled))
    if not medians:
        return None
    return [round(percentile(medians, 0.025), 3), round(percentile(medians, 0.975), 3)]


def _bucket() -> dict:
    return {
        "jobs": 0,
        "jobs_sans_checkout": 0,
        "jobs_sans_heal": 0,
        "checkout": [],
        "heal": [],
        "entree": [],
        "job": [],
        "checkout_min_somme": 0.0,
        "job_min_somme": 0.0,
    }


def _resume_parts(values: list[float], checkout_min_somme: float, job_min_somme: float) -> dict:
    """Mediane, p90 et part du temps total d'une population de parts par job.

    La part du temps total est la somme des checkouts sur la somme des durees
    de job : elle differe de la moyenne des parts des qu'un job long pese plus
    qu'un job court.
    """
    return {
        "jobs": len(values),
        "mediane": round(statistics.median(values), 3) if values else None,
        "p90": round(percentile(values, 0.9), 3) if values else None,
        "checkout_min_somme": round(checkout_min_somme, 2),
        "job_min_somme": round(job_min_somme, 2),
        "part_du_temps_total": round(checkout_min_somme / job_min_somme, 3) if job_min_somme > 0 else None,
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
    parser.add_argument("--runs", type=int, default=None, help="runs inspectes au plus, les plus recents (defaut 60)")
    parser.add_argument("--workflow", default="", help="filtre sur le nom du workflow")
    parser.add_argument("--sample", type=int, default=None, help="nombre de runs tires sur toute la fenetre")
    parser.add_argument("--seed", type=int, default=20261125)
    parser.add_argument("--event", default="pull_request", help="declencheur Actions, ou all")
    parser.add_argument("--slow-min", type=float, default=3.0, help="seuil d'un checkout lent")
    parser.add_argument("--out", default="")
    args = parser.parse_args()

    limite = args.runs if args.runs is not None else 60
    if args.hours <= 0 or limite <= 0:
        parser.error("--hours et --runs doivent etre strictement positifs")
    if args.sample is not None and (args.sample <= 0 or args.runs is not None):
        parser.error(
            "--sample doit etre strictement positif et ne se combine pas avec --runs :"
            " l'un tire au hasard sur la fenetre, l'autre prend les plus recents"
        )
    event = "" if args.event == "all" else args.event
    end = datetime.now(timezone.utc).replace(microsecond=0)
    start = end - timedelta(hours=args.hours)
    since = start.strftime(FMT)
    echantillon = args.sample is not None
    runs, complete = collect_runs(start, end, None if echantillon else limite, args.workflow, event)
    runs_de_la_fenetre = len(runs)
    if echantillon:
        runs = draw_sample(runs, args.sample, args.seed)

    per_workflow: dict[str, dict] = defaultdict(_bucket)
    slow: list[dict] = []
    # Parts par job, rangees par run : le bootstrap tire des runs, pas des jobs.
    parts_tous: list[list[float]] = []
    parts_avec_checkout: list[list[float]] = []
    somme_tous = [0.0, 0.0]
    somme_avec = [0.0, 0.0]
    avec_checkout_sans_duree = 0
    checkout_duree_inconnue = 0
    jobs_sans_duree = 0
    parts_superieures_a_1 = 0
    for run in runs:
        jobs = collect_jobs(run["id"])
        parts_du_run: list[float] = []
        parts_avec_du_run: list[float] = []
        for job in jobs:
            bucket = per_workflow[run.get("name", "?")]
            bucket["jobs"] += 1
            total = minutes(job.get("started_at"), job.get("completed_at"))
            if total is not None:
                bucket["job"].append(total)
                bucket["job_min_somme"] += total
            steps = job.get("steps") or []
            found = step_minutes(steps, CHECKOUT_NAMES)
            checkout_present = any(
                any(marker in (step.get("name") or "").strip().lower() for marker in CHECKOUT_NAMES)
                for step in steps
            )
            heal = step_minutes(steps, HEAL_NAMES)
            if heal is None:
                bucket["jobs_sans_heal"] += 1
            else:
                bucket["heal"].append(heal)
            if found is None:
                bucket["jobs_sans_checkout"] += 1
            else:
                bucket["checkout"].append(found)
                bucket["checkout_min_somme"] += found
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
            # Part du checkout dans ce job. Un job sans etape de checkout
            # compte pour une part nulle dans la population « tous les jobs »
            # et reste hors de la population « jobs avec checkout ».
            if total is None or total <= 0:
                jobs_sans_duree += 1
                if checkout_present:
                    avec_checkout_sans_duree += 1
            elif checkout_present and found is None:
                checkout_duree_inconnue += 1
            else:
                part = (found or 0.0) / total
                parts_du_run.append(part)
                somme_tous[0] += found or 0.0
                somme_tous[1] += total
                if part > 1.0:
                    parts_superieures_a_1 += 1
                if found is not None:
                    parts_avec_du_run.append(part)
                    somme_avec[0] += found
                    somme_avec[1] += total
        parts_tous.append(parts_du_run)
        parts_avec_checkout.append(parts_avec_du_run)

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
                # Sommes des runs inspectes (minutes) : elles classent les
                # workflows par cout absolu, la ou les percentiles les
                # classent par cout par job.
                "checkout_min_somme": round(bucket["checkout_min_somme"], 2),
                "job_min_somme": round(bucket["job_min_somme"], 2),
                "checkout_share_du_temps": (
                    round(bucket["checkout_min_somme"] / bucket["job_min_somme"], 3)
                    if bucket["job_min_somme"] > 0
                    else None
                ),
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

    selection = {
        "methode": "tirage_aleatoire_sans_remise" if echantillon else "plus_recents",
        "runs_dans_la_fenetre": runs_de_la_fenetre if complete else None,
        "runs_inspectes": len(runs),
        "taux_inspection": (
            round(len(runs) / runs_de_la_fenetre, 4)
            if complete and runs_de_la_fenetre else None
        ),
        "graine": args.seed if echantillon else None,
        "facteur_extrapolation": (
            round(runs_de_la_fenetre / len(runs), 3)
            if echantillon and complete and runs
            else None
        ),
        "note": (
            "Les runs inspectes sont un echantillon aleatoire de toute la fenetre."
            " Les sommes par workflow se lisent a l'echelle de l'echantillon ;"
            " leur extrapolation globale est indicative. Les parts ne s'extrapolent pas."
            if echantillon
            else "Les runs inspectes sont les plus recents de la fenetre, pas un"
            " echantillon de celle-ci : aucune marge n'est calculable, et la mediane"
            " ne vaut que pour la periode couverte (window_covered)."
        ),
    }
    part_du_checkout = {
        "definition": (
            "duree de l'etape de checkout / duree du job (completed_at - started_at"
            " du job ; attente du runner exclue)"
        ),
        "tous_les_jobs": _resume_parts(
            [part for group in parts_tous for part in group], somme_tous[0], somme_tous[1]
        ),
        "jobs_avec_etape_checkout": _resume_parts(
            [part for group in parts_avec_checkout for part in group],
            somme_avec[0],
            somme_avec[1],
        ),
        "jobs_avec_checkout_sans_duree_de_job": avec_checkout_sans_duree,
        "jobs_sans_duree_valide": jobs_sans_duree,
        "jobs_checkout_sans_duree_valide": checkout_duree_inconnue,
        "parts_superieures_a_1": parts_superieures_a_1,
    }
    if echantillon:
        exhaustif = len(runs) == runs_de_la_fenetre
        for nom, groupes, graine in (
            ("tous_les_jobs", parts_tous, args.seed),
            ("jobs_avec_etape_checkout", parts_avec_checkout, args.seed + 1),
        ):
            part_du_checkout[nom]["ic95_mediane"] = (
                None if exhaustif else bootstrap_median_ci(groupes, graine)
            )

    covered = [ts(r.get("created_at")) for r in runs if r.get("created_at")]
    report = {
        "repo": REPO,
        "measured_at": datetime.now(timezone.utc).strftime(FMT),
        "window_requested_hours": args.hours,
        "window_created_since": since,
        "window_created_until": end.strftime(FMT),
        "workflow_filter": args.workflow or None,
        "event_filter": event or None,
        "runs_limit": None if echantillon else limite,
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
        "selection": selection,
        "part_du_checkout": part_du_checkout,
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
