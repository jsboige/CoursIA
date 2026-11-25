#!/usr/bin/env python3
"""Releve de la famille ``GIT_OBJECT_MISSING`` sur une fenetre chargee (#27729).

Le census ``classify_job_deaths.py`` ne balaie que les runs **rouges** : son
denominateur d'activite est donc le nombre de jobs rouges, pas le nombre
d'executions reellement realisees. La mesure de cloture de #18312 (24 h, 371
runs rouges) annoncait « 0 occurrence » sur un denominateur de **12
executions** — le zero portait sur ces 12, pas sur une journee chargee (le fil
le dit lui-meme). C'est le residu que #27729 ouvre : un releve sur une
journee ouvree chargee, avec **au moins 50 executions ayant reellement
franchi le checkout**, et un verdict chiffre.

Cet organe change donc deux choses :

1. il enumere **tous** les runs de la fenetre, pas seulement les rouges ;
2. il compte le denominateur par les **etapes** du job : une execution a
   « franchi le checkout » quand une etape de checkout s'est terminee en
   ``success``. C'est la surface qui dit la verite sans telecharger un seul
   log.

Le numerateur reste la famille deja classee par
``classify_job_deaths`` (annotations du check-run, log en secours), et
l'organe y ajoute la **preuve** : la signature qui a matche, le run, le job,
le runner.

Usage :

    python scripts/ci/releve_git_object_missing.py --depuis 2026-11-17 --jusqu 2026-11-21
    python scripts/ci/releve_git_object_missing.py --depuis 2026-11-19 --jusqu 2026-11-20 --json
"""
from __future__ import annotations

import argparse
import json
import sys
from concurrent.futures import ThreadPoolExecutor
from datetime import UTC, datetime, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from classify_job_deaths import (
    GIT_OBJECT_MISSING_NEEDLES,
    GIT_OBJECT_READ_RE,
    fetch_annotations,
    fetch_job_log,
    fetch_run_jobs,
    gh_api,
    git_object_missing_from_log,
)

# Seuil d'executions reelles exige par #27729 pour que le zero soit un
# acquittement : en dessous, le zero ne prouve rien.
SEUIL_CRITERE = 50

# Une fenetre de plus de ce nombre de runs est tronquee : le releve le dit
# plutot que de presenter une fenetre incomplete comme une journee chargee.
PLAFON_RUNS = 4000

# Pages lues par tranche horaire avant de la declarer tronquee (10 pages =
# 1 000 runs dans l'heure ; au-dela, l'API commence a repondre de travers).
PLAFON_PAGES_TRANCHE = 10


def _borne(texte: str, fin: bool) -> datetime:
    """Borne UTC d'un argument de fenetre (``YYYY-MM-DD`` ou ISO).

    Une date seule designe la journee entiere : 00:00:00Z pour le debut,
    23:59:59Z pour la fin.
    """
    if len(texte) == 10:
        jour = datetime.strptime(texte, "%Y-%m-%d").replace(tzinfo=UTC)
        return jour.replace(hour=23, minute=59, second=59) if fin else jour
    return datetime.strptime(texte.replace("Z", "+0000"), "%Y-%m-%dT%H:%M:%S%z")


def _tranches(depuis: datetime, jusqu: datetime, minutes: int) -> list[tuple[str, str]]:
    """Decoupe la fenetre en tranches de N minutes, bornes ISO UTC."""
    iso = "%Y-%m-%dT%H:%M:%SZ"
    tranches: list[tuple[str, str]] = []
    curseur = depuis
    pas = timedelta(minutes=minutes)
    while curseur <= jusqu:
        fin = min(curseur + pas - timedelta(seconds=1), jusqu)
        tranches.append((curseur.strftime(iso), fin.strftime(iso)))
        curseur = curseur + pas
    return tranches


def lister_runs(depuis: str, jusqu: str, max_runs: int = PLAFON_RUNS,
                minutes: int = 60) -> tuple[list[dict], bool]:
    """Runs de la fenetre, toutes branches et tous evenements.

    La fenetre est decoupee en tranches horaires : l'API rend les runs
    **tries par date decroissante**, et la pagination profonde d'une
    fenetre large sature (mesure : une fenetre de 5 jours rendait 1 000 runs,
    tous du dernier jour, la tranche la plus recente ONLY — le releve aurait
    annonce une fenetre qu'il ne couvrait pas). Une tranche horaire se
    vide au-dela de sa population, ce qui rend la decoupe verifiable : une
    tranche qui sature est signalee comme tronquee.
    """
    runs: list[dict] = []
    tronque = False
    for debut, fin in _tranches(_borne(depuis, False), _borne(jusqu, True), minutes):
        page = 1
        while True:
            data = gh_api(
                "actions/runs",
                f"?per_page=100&page={page}&created={debut}..{fin}",
            )
            if not isinstance(data, dict):
                break
            batch = data.get("workflow_runs", [])
            runs.extend(batch)
            if len(batch) < 100:
                break
            page += 1
            if page > PLAFON_PAGES_TRANCHE:
                # Tranche saturee : une page de plus dit si elle etait pleine
                # ou si elle s'achevait la.
                suite = gh_api(
                    "actions/runs",
                    f"?per_page=100&page={page}&created={debut}..{fin}",
                )
                extra = suite.get("workflow_runs", []) if isinstance(suite, dict) else []
                runs.extend(extra)
                tronque = tronque or len(extra) >= 100
                break
    if len(runs) > max_runs:
        tronque = True
        runs = runs[:max_runs]
    return runs, tronque


def etape_checkout(job: dict) -> dict | None:
    """Premiere etape dont le nom evoque un checkout, ou ``None``."""
    for step in job.get("steps") or []:
        if "checkout" in (step.get("name") or "").lower():
            return step
    return None


def franchit_checkout(job: dict) -> bool:
    """Le job a-t-il reellement franchi le checkout ?

    Vrai si une etape de checkout s'est terminee en ``success`` : c'est
    l'execution reelle, celle qui a donc pu subir la famille. Un checkout
    skips (condition ``if:``) ou en echec n'a pas franchi l'etape.
    """
    step = etape_checkout(job)
    return bool(step) and step.get("conclusion") == "success"


def preuve_signature(job: dict, annotations: list[dict]) -> str | None:
    """Signature de la famille trouvee dans les annotations, ou ``None``.

    Meme logique conservatrice que ``classify_job_deaths.git_object_missing``,
    mais qui REND la signature au lieu d'un booleen : un releve doit pouvoir
    etre relu sans refaire le classement.
    """
    messages = [a.get("message", "") for a in annotations]
    for needle in GIT_OBJECT_MISSING_NEEDLES:
        if any(needle in m for m in messages):
            return needle
    for message in messages:
        found = GIT_OBJECT_READ_RE.search(message)
        if found:
            return found.group(0)
    if any("exit code 128" in m for m in messages):
        failed = [s for s in (job.get("steps") or []) if s.get("conclusion") == "failure"]
        if failed and all("checkout" in (s.get("name") or "").lower() for s in failed):
            return "exit code 128 sur l'etape de checkout"
    return None


def analyser_job(job: dict, run: dict) -> dict:
    """Un job : execution reelle ou non, occurrence de la famille ou non."""
    runner = job.get("runner_name") or ""
    job_id = job.get("id")
    resultat = {
        "job_id": job_id,
        "run_id": run.get("id"),
        "jour": (run.get("created_at") or "")[:10],
        "workflow": (run.get("name") or "")[:80],
        "runner": runner,
        "conclusion": job.get("conclusion"),
        "self_hosted": runner.startswith("myia-"),
        "franchit_checkout": franchit_checkout(job),
        "signature": None,
    }
    if not runner:
        return resultat
    if job.get("conclusion") in ("success", "skipped"):
        return resultat
    try:
        annotations = fetch_annotations(job_id)
    except RuntimeError as exc:
        # Une lecture impossible (quota API epuise, 5xx) ne doit pas disparaitre
        # en silence : un releve qui perd des jobs sans le dire presenterait un
        # denominateur partiel comme s'il etait complet.
        resultat["erreur"] = f"annotations: {exc}"[:160]
        return resultat
    signature = preuve_signature(job, annotations)
    if signature is None:
        # Secours : le journal est la surface qui separe une mort de worker
        # d'un rouge de contenu quand l'annotation reste generique. On ne le
        # telecharge QUE pour les jobs dont le CHECKOUT a echoue : la famille
        # est une panne d'objet git au checkout (mesure fondatrice #18312,
        # les 13 jobs fondateurs), et telecharger le journal de chaque job
        # rouge d'une semaine chargerait des centaines de Mo pour rien.
        checkout = etape_checkout(job)
        if checkout and checkout.get("conclusion") in ("failure", "cancelled", "timed_out"):
            try:
                log = fetch_job_log(job_id)
            except RuntimeError as exc:
                resultat["erreur"] = f"journal: {exc}"[:160]
                return resultat
            if git_object_missing_from_log(log):
                signature = "fetch promisor interrompu (journal)"
    resultat["signature"] = signature
    return resultat


def agreger(analyses: list[dict]) -> dict:
    """Somme les analyses en un releve chiffre."""
    executions = [a for a in analyses if a["franchit_checkout"]]
    occurrences = [a for a in analyses if a["signature"]]
    lectures_en_erreur = [a for a in analyses if a.get("erreur")]
    par_jour: dict[str, dict] = {}
    for analysis in analyses:
        bucket = par_jour.setdefault(
            analysis["jour"], {"executions": 0, "occurrences": 0, "jobs": 0}
        )
        bucket["jobs"] += 1
        if analysis["franchit_checkout"]:
            bucket["executions"] += 1
        if analysis["signature"]:
            bucket["occurrences"] += 1
    return {
        "jobs": len(analyses),
        "executions_reelles": len(executions),
        "executions_self_hosted": sum(1 for a in executions if a["self_hosted"]),
        "occurrences": len(occurrences),
        "lectures_en_erreur": len(lectures_en_erreur),
        "par_jour": par_jour,
        "preuves": occurrences,
    }


def verdict(releve: dict, seuil: int = SEUIL_CRITERE) -> dict:
    """Verdict au critere de #27729.

    Acquittement = zero occurrence SUR un denominateur qui atteint le
    seuil d'executions reelles. Un zero sur un denominateur trop faible ne
    prouve rien : c'est exactement le defaut du releve de #18312. Une lecture
    incomplete (quota API epuise, job illisible) ne vaut pas davantage : le
    releve la declare et refuse alors d'acquitter.
    """
    lecture_complete = releve.get("lectures_en_erreur", 0) == 0
    return {
        "criter_atteint": releve["occurrences"] == 0
        and releve["executions_reelles"] >= seuil
        and lecture_complete,
        "seuil": seuil,
        "executions_reelles": releve["executions_reelles"],
        "executions_self_hosted": releve["executions_self_hosted"],
        "occurrences": releve["occurrences"],
        "lectures_en_erreur": releve.get("lectures_en_erreur", 0),
        "lecture_complete": lecture_complete,
    }


def fenetre_heures(heures: int) -> tuple[str, str]:
    """Bornes ISO d'une fenetre glissante, en UTC."""
    fin = datetime.now(UTC)
    debut = fin - timedelta(hours=heures)
    return debut.strftime("%Y-%m-%dT%H:%M:%SZ"), fin.strftime("%Y-%m-%dT%H:%M:%SZ")


def rendre_markdown(releve: dict, fenetre: dict) -> str:
    """Rendu lisible du releve."""
    lignes = [
        "# Releve GIT_OBJECT_MISSING",
        "",
        f"- fenetre : {fenetre['depuis']} -> {fenetre['jusqu']}",
        f"- runs : {fenetre['runs']}{' (TRONQUE)' if fenetre['tronque'] else ''}",
        f"- jobs vus : {releve['jobs']}",
        (f"- **executions ayant franchi le checkout** : {releve['executions_reelles']}"
         f" (dont {releve['executions_self_hosted']} sur runner self-hosted)"),
        f"- **occurrences GIT_OBJECT_MISSING** : {releve['occurrences']}",
        f"- lectures en erreur (quota API, job illisible) : {releve.get('lectures_en_erreur', 0)}",
        "",
    ]
    if releve["par_jour"]:
        lignes += ["| Jour | Jobs | Executions | Occurrences |", "|---|---:|---:|---:|"]
        for jour in sorted(releve["par_jour"]):
            bucket = releve["par_jour"][jour]
            lignes.append(
                f"| {jour} | {bucket['jobs']} | {bucket['executions']} | {bucket['occurrences']} |"
            )
        lignes.append("")
    if releve["preuves"]:
        lignes += ["| Run | Job | Runner | Signature |", "|---:|---:|---|---|"]
        for preuve in releve["preuves"]:
            lignes.append(
                f"| {preuve['run_id']} | {preuve['job_id']} | {preuve['runner']} "
                f"| {preuve['signature']} |"
            )
        lignes.append("")
    return "\n".join(lignes)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depuis", help="debut de fenetre (YYYY-MM-DD ou ISO)")
    parser.add_argument("--jusqu", help="fin de fenetre (YYYY-MM-DD ou ISO)")
    parser.add_argument("--heures", type=int, help="fenetre glissante en heures")
    parser.add_argument("--seuil", type=int, default=SEUIL_CRITERE,
                        help="executions reelles exigees pour un acquittement")
    parser.add_argument("--max-runs", type=int, default=PLAFON_RUNS)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    if args.heures:
        depuis, jusqu = fenetre_heures(args.heures)
    else:
        if not args.depuis or not args.jusqu:
            parser.error("--depuis et --jusqu (ou --heures) sont requis")
        depuis, jusqu = args.depuis, args.jusqu

    runs, tronque = lister_runs(depuis, jusqu, args.max_runs)

    def _paires(run: dict) -> tuple[list[tuple[dict, dict]], str | None]:
        try:
            return [(run, job) for job in fetch_run_jobs(run["id"])], None
        except RuntimeError as exc:
            return [], f"{exc}"[:160]

    paires: list[tuple[dict, dict]] = []
    runs_illisibles = 0
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        for lot, erreur in pool.map(_paires, runs):
            paires.extend(lot)
            if erreur:
                runs_illisibles += 1

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        analyses = list(pool.map(lambda paire: analyser_job(paire[1], paire[0]), paires))

    releve = agreger(analyses)
    releve["lectures_en_erreur"] += runs_illisibles
    fenetre = {"depuis": depuis, "jusqu": jusqu, "runs": len(runs), "tronque": tronque,
               "runs_illisibles": runs_illisibles}
    bilan = verdict(releve, args.seuil)
    bilan["fenetre"] = fenetre
    if args.json:
        print(json.dumps({"releve": releve, "verdict": bilan}, indent=1, ensure_ascii=False))
    else:
        print(rendre_markdown(releve, fenetre))
        print("## Verdict")
        print()
        print(f"- critere atteint : {bilan['criter_atteint']}")
        print(f"- occurrences / executions reelles : "
              f"{releve['occurrences']} / {releve['executions_reelles']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
