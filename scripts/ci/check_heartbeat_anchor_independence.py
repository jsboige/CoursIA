#!/usr/bin/env python3
"""Une jambe de heartbeat est-elle GitHub-hosted DE FAIT, ou seulement de nom ?

Issue #23195. Le heartbeat `workflow_run` des advisories de starvation existe
pour survivre aux deux pannes qu'il observe (#15332 -- le scheduler GitHub cesse
de livrer `schedule` ; extinction du parc self-hosted). Sa jambe « parc eteint »
n'existe que si l'un des workflows ancres **termine sans aucun runner du parc**.

Le defaut fondeur est une PHRASE, pas un run rouge : le header des advisories
declarait `Notebook outputs required` comme « jobs ubuntu-latest, donc le
heartbeat survit aussi au parc eteint ». #21112 (carrier routing) a route ses
deux jobs sur `[self-hosted, coursia-ephemeral, coursia-linux]` -- mesure du
2026-10-29 : 20/20 jobs self-hosted -- et la phrase a continue de decrire un
monde disparu. Rien ne mesurait l'ecart.

Ce que fait cet organe, pour chaque advisory passee en argument :

  1. lit les noms de workflows cites par son bloc `workflow_run.workflows` ;
  2. pour chacun, resout l'identifiant du workflow, echantillonne ses `N`
     derniers runs termines et lit les jobs de chaque run ;
  3. classe chaque job par la presence du label `self-hosted`, et lit les
     declencheurs du workflow ;
  4. declare une JAMBE GitHub-hosted ssi (a) 100 % des jobs echantillonnes sont
     GitHub-hosted et (b) le workflow est declenche par un evenement que GitHub
     delivre sans le parc (`pull_request` ou `push`). La condition (b) n'est pas
     cosmetique : un `workflow_dispatch` 100 % heberge ne se declenche jamais
     tout seul.

Verdicts : `ANCHOR_PROVED` (au moins une jambe), `NO_HOSTED_LEG` (aucune --
le heartbeat ne survit pas a un parc eteint), `UNKNOWN` (API illisible : un
instrument aveugle n'est pas un rouge, #14849).

Cout borne : les pages de liste des workflows (2 au 2026-10-29, l'API en rend
100 par page pour 169 workflows), puis par ancre `1 + N` appels (`runs`, puis
`jobs` par run). Mesure du passage reel sur les deux advisories, `N=3` :
**11 appels**. Le cout est imprime a chaque passage pour la porte de mesure
#22937 -- c'est lui qui a fait saturer le jeton de depot le 2026-10-28, donc
il se mesure au lieu de s'estimer.

Usage :
    python scripts/ci/check_heartbeat_anchor_independence.py
    python scripts/ci/check_heartbeat_anchor_independence.py --json
    python scripts/ci/check_heartbeat_anchor_independence.py \
        --advisory .github/workflows/linux-runner-starvation-advisory.yml

Sortie : 0 = au moins une jambe prouvee, 1 = aucune, 2 = instrument aveugle.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_runner_starvation import CallStats, _gh_json  # noqa: E402

DEFAULT_REPO = "jsboige/CoursIA"
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_ADVISORIES = (
    ".github/workflows/linux-runner-starvation-advisory.yml",
    ".github/workflows/coursia-waiter-starvation-advisory.yml",
)
# Evenements que GitHub delivre sans le parc : ils declenchent depuis l'API de
# GitHub, pas depuis un runner. `workflow_dispatch` est exclu -- il exige une
# main humaine, donc il ne garantit aucune cadence.
PARK_INDEPENDENT_EVENTS = {"pull_request", "push"}
SELF_HOSTED_LABEL = "self-hosted"
# `/actions/workflows` rend 100 workflows par page ; le depot en compte 169 au
# 2026-10-29. Trois pages couvrent la croissance jusqu'a ~300 workflows.
MAX_WORKFLOW_PAGES = 3


@dataclass
class AnchorMeasure:
    name: str
    workflow_id: int | None = None
    runs_sampled: int = 0
    jobs_total: int = 0
    jobs_hosted: int = 0
    jobs_self_hosted: int = 0
    triggers: list[str] = field(default_factory=list)
    error: str | None = None

    @property
    def hosted_share(self) -> float | None:
        if not self.jobs_total:
            return None
        return self.jobs_hosted / self.jobs_total

    @property
    def is_leg(self) -> bool:
        """Jambe GitHub-hosted : hebergee de fait ET declenchee sans le parc."""
        if self.jobs_total == 0 or self.jobs_self_hosted != 0:
            return False
        return bool(PARK_INDEPENDENT_EVENTS & set(self.triggers))


@dataclass
class Verdict:
    verdict: str
    anchors: list[AnchorMeasure]
    advisories: list[str]
    calls: int


def _yaml_on_block(text: str) -> str:
    """Extrait le bloc `on:` en texte brut.

    Pas de parseur YAML ici : le depot n'en garantit pas la dependance sur
    toutes les machines, et `on` est un booleen en YAML 1.1 -- deux pieges pour
    une lecture dont on n'a besoin que d'une liste de noms.
    """
    match = re.search(r"^on:\n(.*?)^(?:permissions|jobs|concurrency|env):",
                      text, re.S | re.M)
    return match.group(1) if match else ""


def load_anchor_names(advisory_path: Path) -> list[str]:
    """Noms de workflows cites par `workflow_run.workflows` de l'advisory."""
    text = advisory_path.read_text(encoding="utf-8")
    block = _yaml_on_block(text)
    match = re.search(r"workflows:\s*\[(.*?)\]", block, re.S)
    if not match:
        return []
    return [item.strip().strip("'\"") for item in match.group(1).split(",")
            if item.strip()]


def resolve_workflow_id(repo: str, name: str, stats: CallStats) -> int | None:
    """Identifiant du workflow par son `name:`.

    `/actions/workflows` pagine a 100 par page et le depot en compte 169 au
    2026-10-29 : une seule page rend « introuvable » pour un workflow qui
    existe, et un organe qui declare absent ce qu'il n'a pas lu fabrique
    exactement le faux negatif qu'il est cense attraper. On pagine donc, borne
    par `MAX_WORKFLOW_PAGES`.
    """
    for page in range(1, MAX_WORKFLOW_PAGES + 1):
        data = _gh_json(
            [f"repos/{repo}/actions/workflows?per_page=100&page={page}"],
            stats=stats,
        )
        if not isinstance(data, dict):
            return None
        workflows = data.get("workflows") or []
        for wf in workflows:
            if wf.get("name") == name:
                return int(wf.get("id")) if wf.get("id") is not None else None
        if len(workflows) < 100:
            return None
    return None


def sample_run_jobs(repo: str, run_id: int, stats: CallStats) -> list[list[str]]:
    data = _gh_json([f"repos/{repo}/actions/runs/{run_id}/jobs?per_page=100"],
                    stats=stats)
    if not isinstance(data, dict):
        return []
    return [list(job.get("labels") or []) for job in data.get("jobs") or []]


def measure_anchor(repo: str, name: str, runs: int,
                   stats: CallStats) -> AnchorMeasure:
    measure = AnchorMeasure(name=name)
    wf_id = resolve_workflow_id(repo, name, stats)
    if wf_id is None:
        measure.error = "workflow introuvable par nom"
        return measure
    measure.workflow_id = wf_id

    runs_data = _gh_json(
        [f"repos/{repo}/actions/workflows/{wf_id}/runs"
         f"?per_page={max(1, runs)}&status=completed"],
        stats=stats,
    )
    if not isinstance(runs_data, dict):
        measure.error = "runs illisibles"
        return measure

    for run in (runs_data.get("workflow_runs") or [])[:runs]:
        run_id = run.get("id")
        if run_id is None:
            continue
        measure.runs_sampled += 1
        event = run.get("event")
        if event and event not in measure.triggers:
            measure.triggers.append(event)
        for labels in sample_run_jobs(repo, int(run_id), stats):
            measure.jobs_total += 1
            if SELF_HOSTED_LABEL in labels:
                measure.jobs_self_hosted += 1
            else:
                measure.jobs_hosted += 1
    if not measure.triggers and not measure.error:
        measure.error = "aucun run termine echantillonne"
    return measure


def evaluate(repo: str, advisories: list[Path], runs: int,
             stats: CallStats) -> Verdict:
    seen: dict[str, AnchorMeasure] = {}
    for advisory in advisories:
        for name in load_anchor_names(advisory):
            if name in seen:
                continue
            seen[name] = measure_anchor(repo, name, runs, stats)
    anchors = list(seen.values())
    if not anchors or all(a.error for a in anchors):
        verdict = "UNKNOWN"
    elif any(a.is_leg for a in anchors):
        verdict = "ANCHOR_PROVED"
    else:
        verdict = "NO_HOSTED_LEG"
    return Verdict(verdict=verdict, anchors=anchors,
                   advisories=[str(a) for a in advisories],
                   calls=stats.calls)


def render_text(v: Verdict) -> str:
    lines = [f"[heartbeat-anchor] verdict={v.verdict} "
             f"ancres={len(v.anchors)} appels_api={v.calls}"]
    for a in v.anchors:
        share = "n/a" if a.hosted_share is None else f"{a.hosted_share:.0%}"
        leg = "JAMBE" if a.is_leg else "-"
        detail = (f"  {leg:5s} {a.name!r}: runs={a.runs_sampled} "
                  f"jobs={a.jobs_total} hosted={share} "
                  f"self_hosted={a.jobs_self_hosted} "
                  f"triggers={','.join(a.triggers) or 'aucun'}")
        if a.error:
            detail += f" erreur={a.error}"
        lines.append(detail)
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo", default=DEFAULT_REPO)
    ap.add_argument("--advisory", action="append", default=None,
                    help="chemin de l'advisory (repetable ; defaut : les deux)")
    ap.add_argument("--runs", type=int, default=3,
                    help="runs termines echantillonnes par ancre (defaut 3)")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--cwd", default=None, help="racine du depot")
    args = ap.parse_args(argv)

    root = Path(args.cwd) if args.cwd else REPO_ROOT
    raw = args.advisory or list(DEFAULT_ADVISORIES)
    advisories = [root / p for p in raw]
    missing = [str(p) for p in advisories if not p.exists()]
    if missing:
        print(f"[heartbeat-anchor] advisory introuvable: {', '.join(missing)}",
              file=sys.stderr)
        return 2

    stats = CallStats()
    verdict = evaluate(args.repo, advisories, args.runs, stats)

    if args.json:
        print(json.dumps({
            "verdict": verdict.verdict,
            "calls": verdict.calls,
            "advisories": verdict.advisories,
            "anchors": [asdict(a) | {"hosted_share": a.hosted_share,
                                     "is_leg": a.is_leg}
                        for a in verdict.anchors],
        }, ensure_ascii=False, indent=2))
    else:
        print(render_text(verdict))

    if verdict.verdict == "ANCHOR_PROVED":
        return 0
    if verdict.verdict == "UNKNOWN":
        # Un instrument aveugle n'est pas un rouge de forge (#14849).
        return 2
    return 1


if __name__ == "__main__":
    sys.exit(main())
