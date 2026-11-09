#!/usr/bin/env python3
"""Mesure les runs redondants d'une meme tete de commit (#22467).

Un run redondant est un **nouvel essai** (`run_attempt == 1`) du meme workflow
sur la meme tete de commit (`head_sha`) : il rejoue un verdict deja rendu sur
l'identique arbre. Ce n'est pas un re-run d'un job interrompu (ceux-la ont
`run_attempt > 1` et sont comptes a part) : c'est un **declencheur** qui
rejoue.

## Ce que l'organe classe, et pourquoi pas une attribution par evenement

La premiere version de cet organe attribuait chaque redondance a un evenement
`edited` lu sur la **timeline d'issue**. Cet axe est **structurellement
aveugle** : la timeline REST n'expose aucune entree `edited` (mesure : 0
entree pour #24102, dont le body a ete republie a 01:33Z). Le chiffre
« 0 redondance imputable a `edited` » qu'il produisait était donc un **faux
zero** : l'absence de lecture, pas l'absence de cause.

L'organe classe donc la **cause** plutot que de pretendre identifier
l'edition :

``SAME_HEAD_PULL_REQUEST``
    tous les essais du groupe sont declenches par `pull_request`. Sur une meme
    tete, un workflow `pull_request` ne peut rejouer que via `edited` ou
    `reopened` : `synchronize` implique une tete changee, `opened` implique
    le premier essai. Cette classe dit donc que le re-fire vient de
    ``edited`` **ou** ``reopened`` -- elle ne separe pas les deux, et
    ``reopened`` n'est compte nulle part ailleurs : le nombre est un
    **minorant** pour `edited`, pas un compte exact.
``MIXED_EVENT``
    le groupe melange des familles d'evenements (double declenchement
    `push` + `pull_request` sur la meme tete, par exemple).
``WITHOUT_LINKED_PR``
    aucun run du groupe ne porte de PR liee (PR fermee, lien absent). Aucune
    timeline n'est alors lisible : l'**attribution est impossible**, ce qui
    n'est pas « non imputable a `edited` ».

La **corroboration** vient d'un evenement de timeline qui, lui, est lisible :
`base_ref_changed`. C'est le signal qu'un retarget a bien eu lieu -- donc
qu'un `edited` a bien ete emis, et que le re-fire etait **legitime** (le
filtre `paths:` est evalue sur le diff base-relative, cf #15652). Le compteur
`redundant_corroborated_base_change` compte ces redondances.

## Collecte

Deux collecteurs, car l'API plafonne a **1000 runs** par requete :

* ``--fleet`` (defaut) : l'endpoint global, plafonne a 1000 runs. Ce que
  l'echantillon couvre est alors **une fenetre implicite**, pas la fenetre
  demandee -- l'organe le signale dans le rapport (``sample_truncated``).
* ``--per-workflow`` : un appel par workflow, avec la fenetre passee sous la
  forme **canonique** ``created=<debut>..<fin>`` (les formes ``created=>=X``
  et ``created<=Y`` sont **ignorees** par l'API, qui rend alors toute
  l'historique du workflow) et un **re-filtre cote client** sur la fenetre.

Le mode par workflow est aussi le mode **economique** : l'endpoint global
consomme le quota REST `core` de la flotte (partagee par tous les agents
sous le login `jsboige`) -- une collecte fleet-wide sur 48 h l'a epuisee.

Exemples
--------
::

    python scripts/ci/measure_redundant_runs.py --repo jsboige/CoursIA \
        --per-workflow --since 2026-10-31T02:00:00Z --until 2026-11-02T02:00:00Z \
        --output redundant.json
    python scripts/ci/measure_redundant_runs.py --input redundant.json
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from measure_runner_demand import (  # noqa: E402
    MeasurementError,
    collect_runs,
    gh_api,
    iso_z,
    parse_time,
)

#: tolerance de corroboration : un retarget suivi du run tombe dans les
#: secondes qui suivent ; trois minutes couvre la latence de l'API.
ATTRIBUTION_WINDOW_SECONDS = 180

#: Plafond de l'endpoint global `actions/runs`.
FLEET_ENDPOINT_CAP = 1000

SAME_HEAD_PULL_REQUEST = "SAME_HEAD_PULL_REQUEST"
MIXED_EVENT = "MIXED_EVENT"
WITHOUT_LINKED_PR = "WITHOUT_LINKED_PR"

EXIT_OK = 0
EXIT_BROKEN = 2


def _base_changes(repo: str, pr_number: int) -> list[str]:
    """Horodatages des evenements `base_ref_changed` de la timeline d'une issue.

    C'est le seul axe de retarget que la timeline REST expose -- et c'est
    l'axe qui **corrobore** qu'un `edited` a bien ete emis.
    """
    payload = gh_api(f"repos/{repo}/issues/{pr_number}/timeline?per_page=100")
    if not isinstance(payload, list):
        raise MeasurementError(f"invalid timeline for issue {pr_number}")
    stamps = []
    for entry in payload:
        if isinstance(entry, dict) and entry.get("event") == "base_ref_changed":
            created = entry.get("created_at")
            if isinstance(created, str):
                stamps.append(created)
    return stamps


def _corroborated(run_started: str, stamps: list[str]) -> bool:
    start = parse_time(run_started)
    for stamp in stamps:
        delta = abs((start - parse_time(stamp)).total_seconds())
        if delta <= ATTRIBUTION_WINDOW_SECONDS:
            return True
    return False


def classify(group: list[dict]) -> str:
    """Classe de cause d'un groupe de premieres tentatives sur une tete."""
    events = {run.get("event") for run in group}
    if events == {"pull_request"}:
        return SAME_HEAD_PULL_REQUEST
    if events == {"pull_request_target"}:
        return SAME_HEAD_PULL_REQUEST
    return MIXED_EVENT


def analyze(runs: list[dict], base_changes_by_pr: dict[str, list[str]]) -> dict:
    """Redondances par workflow, classees par cause."""
    per_workflow: dict[str, dict] = defaultdict(
        lambda: {
            "runs": 0,
            "first_attempts": 0,
            "reruns": 0,
            "heads": set(),
            "redundant_first_attempts": 0,
            "redundant_same_head_pull_request": 0,
            "redundant_mixed_event": 0,
            "redundant_without_linked_pr": 0,
            "redundant_corroborated_base_change": 0,
        }
    )
    by_head: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for run in runs:
        path = run.get("path") or run.get("name") or "?"
        bucket = per_workflow[path]
        bucket["runs"] += 1
        if run.get("run_attempt", 1) == 1:
            bucket["first_attempts"] += 1
            by_head[(path, run.get("head_sha", ""))].append(run)
        else:
            bucket["reruns"] += 1

    for (path, sha), group in by_head.items():
        bucket = per_workflow[path]
        bucket["heads"].add(sha)
        if len(group) < 2:
            continue
        ordered = sorted(group, key=lambda r: (r.get("created_at") or "", r["id"]))
        prs = sorted(
            {
                pr["number"]
                for run in ordered
                for pr in (run.get("pull_requests") or [])
                if isinstance(pr, dict) and "number" in pr
            }
        )
        stamps: list[str] = []
        for pr in prs:
            stamps.extend(base_changes_by_pr.get(str(pr), []))
        linked = bool(prs)
        cause = classify(ordered) if linked else WITHOUT_LINKED_PR
        for run in ordered[1:]:
            bucket["redundant_first_attempts"] += 1
            if cause == SAME_HEAD_PULL_REQUEST:
                bucket["redundant_same_head_pull_request"] += 1
            elif cause == MIXED_EVENT:
                bucket["redundant_mixed_event"] += 1
            else:
                bucket["redundant_without_linked_pr"] += 1
            if linked and _corroborated(run.get("created_at") or "", stamps):
                bucket["redundant_corroborated_base_change"] += 1

    workflows = []
    for path, bucket in per_workflow.items():
        workflows.append(
            {
                "workflow": path,
                "runs": bucket["runs"],
                "at_cap": bucket["runs"] >= FLEET_ENDPOINT_CAP,
                "first_attempts": bucket["first_attempts"],
                "reruns": bucket["reruns"],
                "heads": len(bucket["heads"]),
                "redundant_first_attempts": bucket["redundant_first_attempts"],
                "redundant_same_head_pull_request": bucket[
                    "redundant_same_head_pull_request"
                ],
                "redundant_mixed_event": bucket["redundant_mixed_event"],
                "redundant_without_linked_pr": bucket[
                    "redundant_without_linked_pr"
                ],
                "redundant_corroborated_base_change": bucket[
                    "redundant_corroborated_base_change"
                ],
            }
        )
    workflows.sort(key=lambda row: -row["redundant_first_attempts"])
    totals = {
        "runs": sum(w["runs"] for w in workflows),
        "first_attempts": sum(w["first_attempts"] for w in workflows),
        "reruns": sum(w["reruns"] for w in workflows),
        "heads": len({r.get("head_sha") for r in runs}),
        "redundant_first_attempts": sum(
            w["redundant_first_attempts"] for w in workflows
        ),
        "redundant_same_head_pull_request": sum(
            w["redundant_same_head_pull_request"] for w in workflows
        ),
        "redundant_mixed_event": sum(w["redundant_mixed_event"] for w in workflows),
        "redundant_without_linked_pr": sum(
            w["redundant_without_linked_pr"] for w in workflows
        ),
        "redundant_corroborated_base_change": sum(
            w["redundant_corroborated_base_change"] for w in workflows
        ),
    }
    return {
        "workflows": workflows,
        "totals": totals,
        "attribution_window_seconds": ATTRIBUTION_WINDOW_SECONDS,
    }


def render(report: dict) -> str:
    totals = report["totals"]
    lines = [
        f"{'workflow':46s} {'runs':>6s} {'tetes':>6s} {'redond.':>8s} "
        f"{'edited?':>8s} {'melange':>8s} {'sans PR':>8s} {'retarget':>8s}"
    ]
    for row in report["workflows"]:
        if not row["redundant_first_attempts"]:
            continue
        lines.append(
            f"{row['workflow'][:46]:46s} {row['runs']:6d} {row['heads']:6d} "
            f"{row['redundant_first_attempts']:8d} "
            f"{row['redundant_same_head_pull_request']:8d} "
            f"{row['redundant_mixed_event']:8d} "
            f"{row['redundant_without_linked_pr']:8d} "
            f"{row['redundant_corroborated_base_change']:8d}"
        )
    lines.append("")
    lines.append(
        f"{totals['runs']} runs, {totals['heads']} tetes, "
        f"{totals['redundant_first_attempts']} premieres tentatives redondantes"
    )
    lines.append(
        f"  dont {totals['redundant_same_head_pull_request']} de classe "
        f"{SAME_HEAD_PULL_REQUEST} (meme tete, evenement `pull_request` -- "
        f"donc `edited` ou `reopen`)"
    )
    lines.append(
        f"       {totals['redundant_mixed_event']} de classe {MIXED_EVENT} "
        f"(familles d'evenements melangees)"
    )
    lines.append(
        f"       {totals['redundant_without_linked_pr']} de classe "
        f"{WITHOUT_LINKED_PR} (aucune PR liee -> attribution IMPOSSIBLE, "
        f"pas « non imputable »)"
    )
    lines.append(
        f"  {totals['redundant_corroborated_base_change']} corroborees par un "
        f"evenement `base_ref_changed` lisible (retarget -> `edited` legitime)"
    )
    note = report.get("truncation_note")
    if note:
        lines.append(f"ATTENTION : {note}")
    return "\n".join(lines)


def _workflow_ids(repo: str) -> list[tuple[int, str]]:
    """(id numerique, chemin) des workflows du depot, via l'API (une requete).

    L'endpoint `actions/workflows/{id}/runs` attend un **identifiant** (numerique
    ou nom de fichier) : un chemin complet (`actions/stale/.github/workflows/…`)
    renvoie un 404, et un nom de fichier peut rester ambigu. On passe donc par
    l'id numerique, qui est sans ambiguite.
    """
    payload = gh_api(f"repos/{repo}/actions/workflows?per_page=100")
    if not isinstance(payload, dict):
        raise MeasurementError("invalid workflows payload")
    workflows = payload.get("workflows")
    if not isinstance(workflows, list):
        raise MeasurementError("invalid workflows list")
    out: list[tuple[int, str]] = []
    for wf in workflows:
        if not isinstance(wf, dict):
            continue
        wid = wf.get("id")
        path = wf.get("path")
        if isinstance(wid, int) and isinstance(path, str):
            out.append((wid, path))
    return out


def collect_per_workflow(
    repo: str, since: str, until: str, paths: list[str] | None = None
) -> tuple[list[dict], list[str]]:
    """Collecte workflow par workflow, fenetre canonique, re-filtre client.

    Rend les runs retenus et la liste des workflows dont l'echantillon a
    touche le **plafond de 1000 runs** de l'endpoint : pour eux, la fenetre
    couverte n'est pas celle qui a ete demandee, et leur ligne de rapport est
    un minimum, pas une mesure.
    """
    start = parse_time(since)
    end = parse_time(until)
    if paths:
        targets = [(None, path) for path in paths]
    else:
        targets = _workflow_ids(repo)
    runs: list[dict] = []
    truncated: list[str] = []
    for wid, path in targets:
        key = wid if wid is not None else path
        page = 1
        seen = 0
        while True:
            payload = gh_api(
                f"repos/{repo}/actions/workflows/{key}/runs"
                f"?created={since}..{until}&per_page=100&page={page}"
            )
            if not isinstance(payload, dict):
                raise MeasurementError(f"invalid runs payload for {path}")
            chunk = payload.get("workflow_runs")
            if not isinstance(chunk, list):
                raise MeasurementError(f"invalid runs list for {path}")
            runs.extend(chunk)
            seen += len(chunk)
            if len(chunk) < 100 or page >= 50:
                break
            page += 1
        if seen >= FLEET_ENDPOINT_CAP:
            truncated.append(path)
    # Re-filtre cote client : seule la fenetre demandee compte.
    kept = [
        {
            "id": run.get("id"),
            "path": run.get("path"),
            "name": run.get("name"),
            "head_sha": run.get("head_sha", ""),
            "run_attempt": run.get("run_attempt", 1),
            "created_at": run.get("created_at"),
            "event": run.get("event"),
            "head_branch": run.get("head_branch"),
            "pull_requests": run.get("pull_requests") or [],
        }
        for run in runs
        if start <= parse_time(str(run.get("created_at") or "")) < end
    ]
    return kept, truncated


def collect(
    repo: str, since: str, until: str, per_workflow: bool = False
) -> tuple[list[dict], dict[str, list[str]], bool, list[str]]:
    """Runs + evenements `base_ref_changed` des PRs impliquees.

    Le troisieme element indique si l'echantillon de l'endpoint global a ete
    tronque (plafond de 1000 runs) -- dans ce cas, la fenetre couverte n'est
    pas celle qui a ete demandee. Le quatrieme liste les workflows **individuels**
    qui ont eux-memes touche le plafond, en mode par workflow.
    """
    start = parse_time(since)
    end = parse_time(until)
    if per_workflow:
        runs, truncated_workflows = collect_per_workflow(repo, since, until)
        truncated = False
    else:
        runs = collect_runs(repo, start, end)
        truncated = len(runs) >= FLEET_ENDPOINT_CAP
        truncated_workflows = []
    heads: Counter = Counter(
        (run.get("path") or run.get("name"), run.get("head_sha", ""))
        for run in runs
        if run.get("run_attempt", 1) == 1
    )
    prs = sorted(
        {
            pr["number"]
            for run in runs
            if heads[(run.get("path") or run.get("name"), run.get("head_sha", ""))] > 1
            for pr in (run.get("pull_requests") or [])
            if isinstance(pr, dict) and "number" in pr
        }
    )
    base_changes = {str(pr): _base_changes(repo, pr) for pr in prs}
    return runs, base_changes, truncated, truncated_workflows


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default="jsboige/CoursIA")
    parser.add_argument("--since", required=False, help="debut de fenetre (ISO-8601, TZ)")
    parser.add_argument("--until", required=False, help="fin de fenetre (ISO-8601, TZ)")
    parser.add_argument(
        "--per-workflow",
        action="store_true",
        help="collecter workflow par workflow (evite le plafond de 1000 runs "
        "et la consommation du quota REST de la flotte)",
    )
    parser.add_argument("--output", default=None, help="snapshot JSON")
    parser.add_argument("--input", default=None, help="rejouer un snapshot")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    try:
        if args.input:
            snapshot = json.loads(Path(args.input).read_text(encoding="utf-8"))
            report = analyze(snapshot["runs"], snapshot.get("base_changes", {}))
            report["sample_truncated"] = bool(snapshot.get("sample_truncated"))
            capped = [w["workflow"] for w in report["workflows"] if w["at_cap"]]
            report["truncated_workflows"] = sorted(capped)
            if capped:
                report["truncation_note"] = (
                    "workflow(s) dont l'echantillon touche le plafond de 1000 "
                    "runs : leur ligne est un MINIMUM, pas une mesure de la "
                    "fenetre demandee -- " + ", ".join(sorted(capped))
                )
        else:
            if not args.since or not args.until:
                parser.error("--since et --until sont requis hors mode --input")
            runs, base_changes, truncated, truncated_workflows = collect(
                args.repo, args.since, args.until, per_workflow=args.per_workflow
            )
            report = analyze(runs, base_changes)
            report["sample_truncated"] = truncated
            report["truncated_workflows"] = sorted(truncated_workflows)
            if truncated:
                report["truncation_note"] = (
                    "echantillon tronque au plafond de 1000 runs de l'endpoint "
                    "global : la fenetre couverte n'est PAS celle demandee "
                    "(utiliser --per-workflow)"
                )
            if truncated_workflows:
                report["truncation_note"] = (
                    "workflow(s) dont l'echantillon touche le plafond de 1000 "
                    "runs : leur ligne est un MINIMUM, pas une mesure de la "
                    "fenetre demandee -- " + ", ".join(sorted(truncated_workflows))
                )
            if args.output:
                snapshot = {
                    "repo": args.repo,
                    "since": iso_z(parse_time(args.since)),
                    "until": iso_z(parse_time(args.until)),
                    "sample_truncated": truncated,
                    "runs": runs,
                    "base_changes": base_changes,
                }
                Path(args.output).write_text(
                    json.dumps(snapshot, ensure_ascii=False), encoding="utf-8"
                )
    except MeasurementError as exc:
        print(f"mesure impossible : {exc}", file=sys.stderr)
        return EXIT_BROKEN

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=1))
    else:
        print(render(report))
    return EXIT_OK


if __name__ == "__main__":
    raise SystemExit(main())
