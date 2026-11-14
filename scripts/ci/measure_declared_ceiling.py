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

Usage :

    python scripts/ci/measure_declared_ceiling.py \
        --workflow .github/workflows/scripts-tests.yml --hours 48 \
        --out .tmp/ceiling.json

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
) -> dict:
    rel_path = f".github/workflows/{workflow_file}"
    since = datetime.now(timezone.utc) - timedelta(hours=hours)
    timeline = limit_timeline(rel_path)
    runs = list_runs(workflow_file, since, max_pages)

    jobs: list[dict] = []
    runs_sans_jobs = 0
    for run in runs:
        try:
            listed = api(
                f"/repos/{REPO}/actions/runs/{run['id']}/jobs?per_page=100"
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
            })

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
    for (name, limit), group in sorted(segments.items()):
        cuts = [j for j in group if j["coupe"]]
        successes = [j["execution_min"] for j in group
                      if j["conclusion"] == "success"]
        annules_hors_mur = [j for j in group
                            if j["conclusion"] == "cancelled" and not j["coupe"]]
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
            "coupe_run_ids": [j["run_id"] for j in cuts],
        })

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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--workflow", default="scripts-tests.yml",
                    help="nom de fichier du workflow dans .github/workflows/")
    ap.add_argument("--hours", type=int, default=48,
                    help="fenetre demandee en heures (la fenetre reellement "
                         "couverte est plus courte : l'API plafonne a 1000 runs)")
    ap.add_argument("--max-pages", type=int, default=10)
    ap.add_argument("--out", default="")
    args = ap.parse_args()

    report = measure(args.workflow, args.hours, args.max_pages)
    text = json.dumps(report, ensure_ascii=False, indent=1)
    if args.out:
        Path(args.out).write_text(text, encoding="utf-8")
        print(f"ecrit {args.out}")
    else:
        print(text)
    for row in report["segments"]:
        print(
            f"{row['job']}: plafond {row['limit_min']} min -- "
            f"{row['coupes']} coupe(s) sur {row['jobs_mesures']} jobs "
            f"({row['taux_coupe']}), annules hors mur {row['annules_hors_mur']}, "
            f"succ max {row['succ_max_min']} min (marge {row['marge_succ_max_min']})"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
