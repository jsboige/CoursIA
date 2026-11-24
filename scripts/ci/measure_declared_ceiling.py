#!/usr/bin/env python3
"""Mesure : un job CI a-t-il atteint le **plafond declare** de son workflow ?

Ce que la mesure ne faisait pas
-------------------------------
`scripts/ci/measure_ci_two_tier.py` mesure deja la duree d'execution par job
(`completed_at - started_at`). `scripts/pr_gate.py::derive_declared_timeouts`
sait deja lire le `timeout-minutes` declare d'un job dans le YAML du workflow.
Mais les deux capacites ne se rencontrerent jamais : **aucun organe ne disait
si un job avait touche SON MUR**, et chaque question de ce genre se refaisait
a la main -- l'en-tete de `.github/workflows/scripts-tests.yml` (qui ecrit
« Re-mesurer sur les 70 prochains runs ... c'est ce qui dira si 40 min
suffit »), la mesure de po-2027 du 2026-11-13, celle-ci.

Ce module fait la jointure, et repond a la seule question utile : **le plafond
declare bind-il ?**

Trois pieges que la mesure ferme
--------------------------------

1. **Un plafond declare change dans le temps.** Un job demarre avant le
   changement n'a pas le meme plafond que celui d'apres. La mesure segmente
   donc par **le plafond en vigueur au demarrage du job**, lu dans l'historique
   git du fichier de workflow -- pas dans sa version courante. Lire la version
   courante appliquerait retroactivement le nouveau plafond aux jobs anciens
   (c'est ce qui ferait paraitre une coupe inexistante, ou masquer une vraie).

2. **`conclusion: cancelled` n'est pas une coupe.** GitHub rend une violation
   de `timeout-minutes` en `cancelled` -- mais `cancel-in-progress` rend de
   meme un job annule **apres** 45 a 129 min, et une famine de runner rend un
   job annule en quelques secondes. Une coupe est donc un job annule **au
   mur** : fenetre bilaterale autour du plafond declare. Sans borne haute, les
   annulations par supersession seraient comptees comme des coupes (mesure :
   11 coupes reelles, 9 annulations par supersession ecartees a tort par une
   premiere version de ce module).

3. **La fenetre mesuree n'est jamais celle demandee.** L'API Actions plafonne
   a 1000 runs filtres : au-dela, la fenetre reellement couverte est plus
   courte que la fenetre demandee. La couverture effective est ecrite dans la
   sortie (`window_covered`), jamais supposee.

L'organe natif de la mort des jobs
-----------------------------------

`scripts/ci/classify_job_deaths.py` est **l'organe qui sait pourquoi un job
est mort** : il lit l'annotation que GitHub pose sur le check-run et en tire
la classe `TIMEOUT` (« The job has exceeded the maximum execution time of
40m0s »), `NO_RUNNER_ACQUIRED`, `OOM`, etc.

Cet organe ne reecrit **pas** cette classification -- il s'y branche. La
fenetre bilaterale de ce module sert a **produire les candidats** (un job
annule est un candidat ; un job reussi ne l'est pas), et le mode
`--cross-check` confronte chaque candidat a la classe de l'organe natif :

- `coupe` (fenetre) **confirmee** par `TIMEOUT` (annotation) ;
- `coupe` **non confirmee** (l'annulation n'etait pas un depassement) ;
- `TIMEOUT` **ratee** par la fenetre (le job a coupe sans que sa duree tombe
  dans la fenetre -- la fenetre est alors un proxy, pas une preuve).

Ce que cet organe ajoute a l'organe natif : la **frise des plafonds**. La
classe `TIMEOUT` dit *ce* job a coupe par *un* plafond ; elle ne dit pas si
le plafond en vigueur au moment du job etait 30 ou 40 minutes. Sans la
frise, un job tue en 30 min le 13/11 (plafond 40) serait lu comme une coupe
du plafond 40 -- une coupe qui n'existe pas.

Usage :

    python scripts/ci/measure_declared_ceiling.py \
        --workflow .github/workflows/scripts-tests.yml --hours 48 \
        --out .tmp/ceiling.json

    # controle croise : la fenetre bilaterale confirme-t-elle l'annotation ?
    python scripts/ci/measure_declared_ceiling.py --cross-check 24

Lecture seule : aucune ecriture dans le depot, aucun secret (le jeton est lu
par `gh auth token` au moment de l'appel).
"""
from __future__ import annotations

import argparse
import json
import statistics
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

REPO = "jsboige/CoursIA"
REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOWS_DIR = REPO_ROOT / ".github" / "workflows"

sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))

# Le client API et le parseur de timestamp de l'organe natif de la mesure CI
# (scripts/ci/measure_ci_two_tier.py) : un seul organe possede l'appel
# GitHub, un seul possede le format des timestamps. Cet organe ne reecrit ni
# l'un ni l'autre.
from measure_ci_two_tier import api, parse_ts  # noqa: E402

try:  # pragma: no cover - PyYAML est present dans l'env CI
    import yaml
except ImportError:  # pragma: no cover
    yaml = None  # type: ignore[assignment]

#: Tolerance de la fenetre de coupe, en secondes. GitHub pose `completed_at`
#: avec un peu de retard sur l'arret du runner : la borne basse tolere ce
#: retard, la borne haute empeche une annulation par supersession (qui peut
#: durer bien plus longtemps que le plafond) d'entrer dans le compte.
TOL_LO_S = 90
TOL_HI_S = 120

#: Largeur du seau "proche du plafond", en minutes. Un job dont la duree
#: approche la limite declaree a moins de cette largeur est comptabilise
#: dans la queue : c'est la queue qui dit si un releve du plafond servirait
#: a quelque chose.
NEAR_CEILING_MIN = 2

#: Version du cache de collecte. Un cache d'une version anterieure est
#: IGNORE (il est recollecte) : la version 1 ne portait que la derniere
#: tentative de chaque run, ce qui censurait la population par les rejeux
#: (mesure du 2026-11-14 : 26 des 40 coupes au mur du segment 40 min
#: etaient absentes de ce cache). Un cache reutilise tel quel rendrait un
#: chiffre faux avec l'apparence d'une mesure.
CACHE_VERSION = 2


def limits_from_yaml(text: str) -> dict[str, int]:
    """Plafonds declares d'un workflow, par **nom de job**.

    Meme regle que `pr_gate.derive_declared_timeouts` : un nom de job qui
    resout a plusieurs limites DISTINCTES est **abandonne** plutot que devine
    -- le lecteur ne doit pas nommer un plafond qu'il ne peut pas attribuer au
    job qu'il regarde. Ici l'ambiguite est interne au fichier (le meme nom
    dans deux jobs du meme workflow).
    """
    if yaml is None:
        return {}
    try:
        data = yaml.safe_load(text)
    except yaml.YAMLError:
        return {}
    if not isinstance(data, dict):
        return {}
    seen: dict[str, set[int]] = {}
    for job_key, job in (data.get("jobs") or {}).items():
        if not isinstance(job, dict):
            continue
        limit = job.get("timeout-minutes")
        if not isinstance(limit, int) or isinstance(limit, bool):
            continue
        name = job.get("name") or job_key
        if isinstance(name, str) and name:
            seen.setdefault(name, set()).add(limit)
    return {
        name: next(iter(limits))
        for name, limits in seen.items()
        if len(limits) == 1
    }


def _parse_iso(value: str) -> datetime | None:
    """Parse un horodatage ISO-8601 **avec decalage** (format de `git log`).

    Le parseur de l'organe natif (`parse_ts`) ne lit que le `%Y-%m-%dT%H:%M:%SZ`
    de l'API ; `git log --format=%cI` rend un decalage local (`+01:00`). Le
    decalage est converti en UTC : la frise des plafonds et les jobs doivent
    etre compares dans le **meme** fuseau, sinon la limite en vigueur est
    decalee d'une heure.
    """
    try:
        stamp = datetime.fromisoformat(value.strip())
    except (AttributeError, ValueError):
        return None
    if stamp.tzinfo is None:
        return stamp.replace(tzinfo=timezone.utc)
    return stamp.astimezone(timezone.utc)


def _git(*args: str) -> str:
    out = subprocess.run(
        ["git", "-C", str(REPO_ROOT), *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        check=True,
    )
    return out.stdout


def limit_timeline(rel_path: str) -> list[tuple[datetime, dict[str, int]]]:
    """Histoire des plafonds declares d'un workflow : (date, {nom: plafond}).

    Les commits qui ne changent aucun plafond sont ecartes : la frise ne garde
    que les **etats distincts** du plafond, ce qui la rend lisible et la
    comparaison avec la mesure immediate.

    La selection des commits utilise `-G` (et non `-S`) : `-S` compte les
    occurrences de la chaine, donc un simple passage de `30` a `40` -- meme
    nombre d'occurrences -- ne serait **pas** selectionne, et l'ancien
    plafond disparaitrait de l'historique. `-G` selectionne les commits dont le
    diff touche une ligne du motif, quel que soit le nombre d'occurrences.
    """
    commits = _git(
        "log", "-G", "timeout-minutes:", "--format=%H %cI", "--", rel_path
    ).strip().splitlines()
    timeline: list[tuple[datetime, dict[str, int]]] = []
    previous: dict[str, int] | None = None
    for line in commits:  # du plus recent au plus ancien
        parts = line.split(" ", 1)
        if len(parts) != 2:
            continue
        sha, when = parts
        try:
            text = _git("show", f"{sha}:{rel_path}")
        except subprocess.CalledProcessError:
            continue
        limits = limits_from_yaml(text)
        if limits != previous:
            stamp = _parse_iso(when)
            if stamp is not None:
                timeline.append((stamp, limits))
                previous = limits
    timeline.sort(key=lambda item: item[0])
    return timeline


def resolve_limit(
    timeline: list[tuple[datetime, dict[str, int]]],
    name: str,
    when: datetime,
) -> int | None:
    """Plafond en vigueur pour `name` a la date `when` (None si inconnu)."""
    limit: int | None = None
    for stamp, limits in timeline:
        if stamp > when:
            break
        limit = limits.get(name)
    return limit


def is_cut(execution_min: float, conclusion: str | None, limit_min: int) -> bool:
    """Le job a-t-il ete coupe par SON plafond declare ?

    Fenetre bilaterale autour du plafond : une annulation par supersession
    (`cancel-in-progress`) peut durer bien plus longtemps que le plafond, et
    ne doit pas etre comptee comme une coupe.
    """
    if conclusion != "cancelled":
        return False
    low = limit_min - TOL_LO_S / 60
    high = limit_min + TOL_HI_S / 60
    return low <= execution_min <= high


def list_runs(workflow: str, since: datetime, max_pages: int) -> list[dict]:
    """Runs termines d'un workflow, du plus recent au plus ancien."""
    runs: list[dict] = []
    page = 1
    while page <= max_pages:
        data = api(
            f"/repos/{REPO}/actions/workflows/{workflow}/runs"
            f"?status=completed&per_page=100&page={page}"
        )
        batch = data.get("workflow_runs", [])
        if not batch:
            break
        runs.extend(batch)
        oldest = min(parse_ts(r["created_at"]) for r in batch)
        if oldest and oldest < since:
            break
        page += 1
    return [r for r in runs if (parse_ts(r["created_at"]) or since) >= since]


def measure(
    workflow_file: str,
    hours: int,
    max_pages: int,
    jobs_cache: str = "",
    annotate_cuts: bool = False,
) -> dict:
    rel_path = f".github/workflows/{workflow_file}"
    since = datetime.now(timezone.utc) - timedelta(hours=hours)
    timeline = limit_timeline(rel_path)
    runs = list_runs(workflow_file, since, max_pages)

    jobs: list[dict] = []
    runs_sans_jobs = 0
    # Le parcours des runs est la partie COUTEUSE de la mesure (un appel
    # `jobs` par run, donc un millier d'appels pour 48 h). Le cache garde la
    # liste des jobs : re-mesurer apres un changement de code ne reboucle pas
    # l'API, et le passage d'annotation (une requete par job annule) ne
    # paie qu'une fois la collecte.
    if jobs_cache and Path(jobs_cache).exists():
        cached = json.loads(Path(jobs_cache).read_text(encoding="utf-8"))
        if cached.get("cache_version") == CACHE_VERSION:
            jobs = cached.get("jobs", [])
            runs = cached.get("runs") or runs
            runs_sans_jobs = cached.get("runs_sans_jobs", 0)
        else:
            # Cache d'une version anterieure : il est IGNORE, pas relu.
            # Reutiliser sa population ferait rendre le chiffre d'avant le
            # correctif, avec l'apparence d'une mesure a jour.
            print(
                f"cache ignore : version {cached.get('cache_version')} != "
                f"{CACHE_VERSION} -- recollecte"
            )
    if not jobs:
        for run in runs:
            try:
                listed = api(
                    # `filter=all` : TOUTES les tentatives du run, pas
                    # seulement la derniere. SANS lui, la population est
                    # CENSOREE par les rejeux : un job coupe au mur puis
                    # rejoue (rejeu automatique de la CI ou re-run humain)
                    # disparait de la population -- le run ne porte plus que
                    # la tentative rejouee, qui reussit. Mesure du 2026-11-14
                    # (controle croise, meme organe natif
                    # `classify_job_deaths.py`, population collectee par
                    # ailleurs avec `filter=all`) : 26 des 40 coupes au mur
                    # du segment 40 min sont ABSENTES de la population
                    # collecte SANS `filter=all`. C'est ce qui faisait
                    # annoncer 2,3 % (12/523) au lieu de 6,5 % (38/582).
                    f"/repos/{REPO}/actions/runs/{run['id']}/jobs?per_page=100&filter=all"
                ).get("jobs", [])
            except Exception:  # noqa: BLE001 - une page illisible ne doit pas
                # faire tomber la mesure entiere ; le run compte pour rien.
                runs_sans_jobs += 1
                continue
            for job in listed:
                started = parse_ts(job.get("started_at") or "")
                completed = parse_ts(job.get("completed_at") or "")
                if started is None or completed is None:
                    continue
                execution = (completed - started).total_seconds() / 60
                if execution < 0:
                    continue
                jobs.append({
                    "run_id": run["id"],
                    "job_id": job.get("id"),
                    "name": job.get("name") or "",
                    "conclusion": job.get("conclusion"),
                    "started_at": job.get("started_at"),
                    "execution_min": execution,
                    "branch": run.get("head_branch"),
                    "run_attempt": job.get("run_attempt"),
                    "steps": job.get("steps") or [],
                })
        if jobs_cache:
            Path(jobs_cache).write_text(json.dumps({
                "cache_version": CACHE_VERSION,
                "jobs": jobs,
                "runs": [{"id": r["id"], "created_at": r.get("created_at"),
                          "head_branch": r.get("head_branch")}
                         for r in runs],
                "runs_sans_jobs": runs_sans_jobs,
            }, ensure_ascii=False), encoding="utf-8")

    segments: dict[tuple[str, int], list[dict]] = {}
    unknown = 0
    for job in jobs:
        when = parse_ts(job["started_at"] or "")
        limit = resolve_limit(timeline, job["name"], when) if when else None
        if limit is None:
            unknown += 1
            continue
        job["limit_min"] = limit
        job["coupe"] = is_cut(job["execution_min"], job["conclusion"], limit)
        segments.setdefault((job["name"], limit), []).append(job)

    rows = []
    classify_job = fetch_annotations = None
    if annotate_cuts:
        # L'organe NATIF de la mort des jobs : c'est lui qui lit l'annotation
        # « The job has exceeded the maximum execution time of 40m0s » et en
        # tire la classe TIMEOUT. Cet organe ne reecrit pas la classification,
        # il l'**importe** et compte.
        from classify_job_deaths import classify_job, fetch_annotations
    for (name, limit), group in sorted(segments.items()):
        cuts = [j for j in group if j["coupe"]]
        successes = [j["execution_min"] for j in group
                      if j["conclusion"] == "success"]
        annules_hors_mur = [j for j in group
                            if j["conclusion"] == "cancelled" and not j["coupe"]]
        # Seau "proche du plafond" : les jobs dont la duree approche la limite
        # declaree. C'est ce seau qui dit si un releve du plafond GANTERAIT
        # quelque chose : un plafond ne serre que s'il y a une queue, et la
        # queue se mesure ici, pas dans le seul taux de coupes.
        proches = [j for j in group
                   if j["execution_min"] >= limit - NEAR_CEILING_MIN]
        rows.append({
            "job": name,
            "limit_min": limit,
            "jobs_mesures": len(group),
            "coupes": len(cuts),
            "taux_coupe": round(len(cuts) / len(group), 4) if group else None,
            "annules_hors_mur": len(annules_hors_mur),
            "exec_max_min": round(max(j["execution_min"] for j in group), 2),
            "exec_med_min": round(statistics.median(
                j["execution_min"] for j in group), 2),
            "succ_max_min": round(max(successes), 2) if successes else None,
            "marge_succ_max_min": (
                round(limit - max(successes), 2) if successes else None
            ),
            "seau_proche_du_plafond_min": NEAR_CEILING_MIN,
            "jobs_proches_du_plafond": len(proches),
            "succ_proches_du_plafond": sum(
                1 for j in proches if j["conclusion"] == "success"),
            "coupe_run_ids": [j["run_id"] for j in cuts],
        })
        if annotate_cuts:
            classes: dict[str, int] = {}
            confirmed = 0
            for j in group:
                if j["conclusion"] != "cancelled":
                    continue
                try:
                    klass = classify_job(j, fetch_annotations(j["job_id"]))
                except Exception:  # noqa: BLE001 - une annotation illisible
                    # ne doit pas faire tomber la mesure ; elle compte comme
                    # « non confirmee », jamais comme un succes.
                    klass = "LECTURE_IMPOSSIBLE"
                classes[klass] = classes.get(klass, 0) + 1
                if klass == "TIMEOUT":
                    confirmed += 1
            rows[-1]["coupes_confirmees_annotation"] = confirmed
            rows[-1]["classes_annulation"] = classes

    created = sorted(r["created_at"] for r in runs if r.get("created_at"))
    return {
        "workflow": rel_path,
        "fenetre_demandee_h": hours,
        "window_covered": {
            "debut": created[0] if created else None,
            "fin": created[-1] if created else None,
            "runs": len(runs),
            "note": "l'API Actions plafonne a 1000 runs filtres : la fenetre "
                    "couverte peut etre plus courte que la fenetre demandee",
        },
        "runs_sans_jobs_lisibles": runs_sans_jobs,
        "jobs_mesures": len(jobs),
        "jobs_sans_plafond_connu": unknown,
        "plafonds_historiques": [
            {"date": stamp.isoformat(), "limites": limits}
            for stamp, limits in timeline
        ],
        "segments": rows,
    }


def cross_check(workflow: str, sample: int, job_name: str,
                from_json: str = "") -> int:
    """Confronte la fenetre bilaterale a la classe de mort de l'organe natif.

    La fenetre est un **proxy** : elle dit qu'un job annule a dure assez
    longtemps pour avoir touche son plafond. L'organe natif
    (`classify_job_deaths.py`) lit l'annotation que GitHub pose sur le
    check-run (« The job has exceeded the maximum execution time of 40m0s »)
    et rend la classe `TIMEOUT` -- la **preuve**, pas le proxy.

    Ce mode mesure l'ecart entre les deux, sur un echantillon de runs :
    combien de coupes la fenetre annonce sont confirmees, combien sont
    ecartees, et combien la fenetre rate.

    `--cross-check-from` ajoute les runs que la mesure a designes comme
    porteurs de coupes : sans eux, l'echantillon ne contredit que des
    annulations par supersession, et le controle ne prouve rien sur les
    coupes qu'il est cense valider.

    Il ne reecrit pas la classification : il **importe** l'organe natif.
    """
    from classify_job_deaths import classify_job, fetch_annotations

    rel_path = f".github/workflows/{workflow}"
    timeline = limit_timeline(rel_path)
    since = datetime.now(timezone.utc) - timedelta(hours=48)
    runs = list_runs(workflow, since, 10)
    if not runs:
        print("aucun run lu : controle croise impossible")
        return 2

    by_id = {r["id"]: r for r in runs}
    picked: list[dict] = []
    seen: set[int] = set()
    cut_ids: list[int] = []

    # D'abord les runs porteurs de coupes, si la mesure est fournie.
    if from_json:
        report = json.loads(Path(from_json).read_text(encoding="utf-8"))
        for row in report.get("segments", []):
            for run_id in row.get("coupe_run_ids", []):
                if run_id not in cut_ids:
                    cut_ids.append(run_id)
        for run_id in cut_ids:
            run = by_id.get(run_id)
            if run is not None and run_id not in seen:
                picked.append(run)
                seen.add(run_id)
        print(f"runs porteurs de coupes ajoutes a l'echantillon : {len(picked)}")

    # Puis les runs les plus recents (la ou sont les coupes du plafond
    # courant) et un pas regulier sur le reste de la fenetre.
    for run in runs[: max(1, sample // 2)]:
        if len(picked) >= sample + len(cut_ids):
            break
        if run["id"] not in seen:
            picked.append(run)
            seen.add(run["id"])
    stride = max(1, len(runs) // max(1, sample))
    for run in runs[::stride]:
        if len(picked) >= sample + len(cut_ids):
            break
        if run["id"] not in seen:
            picked.append(run)
            seen.add(run["id"])

    rows: list[dict] = []
    for run in picked:
        try:
            listed = api(
                # `filter=all` : meme raison que dans la collecte -- sans
                # lui, les rejets des jobs coupes puis rejoues disparaissent
                # de la population, et le controle croise sous-estime les
                # coupes au lieu de les confirmer.
                f"/repos/{REPO}/actions/runs/{run['id']}/jobs?per_page=100&filter=all"
            ).get("jobs", [])
        except Exception:  # noqa: BLE001 - un run illisible ne fait pas
            # tomber le controle croise ; il compte pour rien.
            continue
        for job in listed:
            name = job.get("name") or ""
            if job_name and name != job_name:
                continue
            conclusion = job.get("conclusion")
            if conclusion not in ("cancelled", "failure"):
                continue
            started = parse_ts(job.get("started_at") or "")
            completed = parse_ts(job.get("completed_at") or "")
            if started is None or completed is None:
                continue
            execution = (completed - started).total_seconds() / 60
            limit = resolve_limit(timeline, name, started)
            fenetre = is_cut(execution, conclusion, limit) if limit else None
            annotations = fetch_annotations(job["id"])
            klass = classify_job(job, annotations)
            rows.append({
                "run_id": run["id"],
                "job_id": job.get("id"),
                "job": name,
                "conclusion": conclusion,
                "execution_min": round(execution, 2),
                "limit_min": limit,
                "fenetre": fenetre,
                "classe": klass,
            })

    confirms = [r for r in rows if r["fenetre"] and r["classe"] == "TIMEOUT"]
    ecartees = [r for r in rows if r["fenetre"] and r["classe"] != "TIMEOUT"]
    rates = [r for r in rows if not r["fenetre"] and r["classe"] == "TIMEOUT"]
    classes: dict[str, int] = {}
    for row in rows:
        classes[row["classe"]] = classes.get(row["classe"], 0) + 1

    for row in rows:
        print(
            f"run {row['run_id']} job {row['job_id']} -- {row['job']} : "
            f"{row['execution_min']} min, plafond {row['limit_min']}, "
            f"conclusion {row['conclusion']}, fenetre={row['fenetre']}, "
            f"classe={row['classe']}"
        )
    print("")
    print(f"echantillon : {len(picked)} run(s), {len(rows)} job(s) annule(s)/en echec")
    print(f"coupes fenetre CONFIRMEES par l'annotation TIMEOUT : {len(confirms)}")
    print(f"coupes fenetre NON confirmees : {len(ecartees)}")
    print(f"TIMEOUT rates par la fenetre : {len(rates)}")
    print(f"classes vues : {classes}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--workflow", default="scripts-tests.yml",
                    help="nom de fichier du workflow dans .github/workflows/")
    ap.add_argument("--hours", type=int, default=48,
                    help="fenetre demandee en heures (la fenetre reellement "
                         "couverte est plus courte : l'API plafonne a 1000 runs)")
    ap.add_argument("--max-pages", type=int, default=10)
    ap.add_argument("--out", default="")
    ap.add_argument("--cross-check", type=int, default=0,
                    help="nombre de runs a confronter a la classe de mort de "
                         "l'organe natif (classify_job_deaths.py) ; 0 = "
                         "aucun controle croise")
    ap.add_argument("--cross-check-job", default="",
                    help="nom du job a controler (defaut : tous)")
    ap.add_argument("--cross-check-from", default="",
                    help="sortie JSON d'une mesure : les runs porteurs de "
                         "coupes y sont ajoutes a l'echantillon")
    ap.add_argument("--jobs-cache", default="",
                    help="fichier de cache de la liste des jobs (la collecte "
                         "est la partie couteuse : ~1 appel API par run)")
    ap.add_argument("--annotate", action="store_true",
                    help="classer chaque job annule avec l'organe natif "
                         "(classify_job_deaths.py) et compter les coupes "
                         "CONFIRMEES par annotation")
    args = ap.parse_args()

    if args.cross_check:
        return cross_check(args.workflow, args.cross_check, args.cross_check_job,
                           args.cross_check_from)

    report = measure(args.workflow, args.hours, args.max_pages,
                     args.jobs_cache, args.annotate)
    text = json.dumps(report, ensure_ascii=False, indent=1)
    if args.out:
        Path(args.out).write_text(text, encoding="utf-8")
        print(f"ecrit {args.out}")
    else:
        print(text)
    for row in report["segments"]:
        line = (
            f"{row['job']}: plafond {row['limit_min']} min -- "
            f"{row['coupes']} coupe(s) sur {row['jobs_mesures']} jobs "
            f"({row['taux_coupe']}), annules hors mur {row['annules_hors_mur']}, "
            f"succ max {row['succ_max_min']} min (marge {row['marge_succ_max_min']})"
            f" -- queue (>= {row['limit_min'] - row['seau_proche_du_plafond_min']} min) : "
            f"{row['jobs_proches_du_plafond']} job(s), "
            f"{row['succ_proches_du_plafond']} succes(s)"
        )
        if "coupes_confirmees_annotation" in row:
            line += (
                f" -- CONFIRMEES par annotation (organe natif TIMEOUT) : "
                f"{row['coupes_confirmees_annotation']} ; classes : "
                f"{row['classes_annulation']}"
            )
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
