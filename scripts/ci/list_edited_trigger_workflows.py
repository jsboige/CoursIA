#!/usr/bin/env python3
"""Census des workflows qui rejouent sur `pull_request: edited` (#22467).

Le declencheur `edited` rejoue un workflow a chaque edition du titre, du body
**ou de la base** d'une PR. Sur un workflow filtre par `paths`, le filtre reste
vrai -- les fichiers modifies n'ont pas bouge -- donc chaque edition rejouait
le verdict sur la meme tete de commit. C'est la source des « premieres
tentatives redondantes » mesurees par `scripts/ci/measure_redundant_runs.py`.

Ce module repond a la question que l'issue #22467 pose en son point 1 :
**quels workflows ecoutent `edited` alors que leur verdict n'en depend pas ?**

Quatre axes de dependance, parce qu'un `edited` peut ne changer que le titre,
que le body, ou que la **base** :

``body``
    le verdict bouge quand le body bouge. Etabli par l'inventaire deja
    existant `scripts/ci/body_consuming_guards.py`, qui decouvre mecaniquement
    quels scripts lisent le body et par quel canal.
``title``
    le verdict bouge quand le titre bouge (lecture directe).
``base``
    le verdict bouge quand la base bouge (lecture directe de la base).
``paths``
    le filtre `paths:` est evalue sur le **diff base-relative** : changer la
    base change la liste des fichiers qui matchent, donc un workflow qui ne
    matchait pas peut matcher apres un retarget -- et un workflow qui
    matchait peut ne plus matcher. Sans `edited`, il ne le saurait jamais.

L'axe `paths` est **load-bearing** et il est documente dans le depot :
`lean-knot.yml` porte l'issue #15652 -- « un workflow PR qui combine
`branches: [main]` + `paths:` + une cle `types:` SANS `edited` rate
systematiquement les PR empilees ... quand la parente est mergee et l'enfant
retarget vers main, l'evenement `base_ref_changed` emet un `edited` que les
workflows sans `edited` ignorent ». Le retrait du `edited` y re-ouvrirait la
PR empilee sans CI Lean.

Verdict par workflow :

``PR_METADATA_DEPENDENT``
    au moins un axe est present -> `edited` est utile, il ne doit pas etre
    retire.
``CONTENT_ONLY``
    aucun axe -> `edited` est gratuit : le verdict ne depend que du code.

Exemples
--------
::

    python scripts/ci/list_edited_trigger_workflows.py
    python scripts/ci/list_edited_trigger_workflows.py --json
    python scripts/ci/list_edited_trigger_workflows.py --only content-only
    python scripts/ci/list_edited_trigger_workflows.py --ablate-detector

Ablation
--------

L'axe `body` s'appuie sur l'inventaire `body_consuming_guards.py`, qui
reconnait un nombre **ferme** de formes de lecture du body (les trois formes
`api-gh` sont enoncees dans la docstring de cet organe, avec les formes non
reconnues). Une conclusion qui ne tiendrait que sur une de ces formes serait
fragile.

`--ablate-detector` recalcule donc le verdict **sans** la contribution de
l'inventaire : l'axe `body` ne vient plus que de la lecture directe dans le
fichier de workflow. Si l'ensemble `CONTENT_ONLY` ne change pas, la
couverture des formes ne peut pas changer la conclusion ; sinon, les
workflows concernes sont nommes. Chaque ligne porte d'ailleurs son
`verdict_without_detector` : la dependance est **visible**, pas supposee.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from body_consuming_guards import (  # noqa: E402
    _strip_comment_lines,
    discover_consumers,
)

WORKFLOW_DIR = ".github/workflows"
ACTION_DIR = ".github/actions"

#: Un script du depot appele par le workflow (ou par une action composite).
SCRIPT_RE = re.compile(r"scripts/[\w./-]+\.(?:py|sh)")
#: Une action composite locale referencee par le workflow.
ACTION_RE = re.compile(r"uses:\s*\.github/actions/([\w-]+)/action\.yml")
#: Une lecture directe du body de la PR dans le workflow lui-meme.
DIRECT_BODY_RE = re.compile(r"pull_request\.body|--pr-body|PR_BODY|pr_body")
#: Une lecture du titre de la PR (un `edited` peut ne changer que le titre).
DIRECT_TITLE_RE = re.compile(r"pull_request\.title|PR_TITLE|pr_title")
#: Une lecture de la base de la PR (un `edited` peut ne changer que la base).
DIRECT_BASE_RE = re.compile(
    r"baseRefName|pull_request\.base|changes\.base|base_ref|PR_BASE"
)

PR_METADATA_DEPENDENT = "PR_METADATA_DEPENDENT"
CONTENT_ONLY = "CONTENT_ONLY"

#: profondeur de resolution des actions composites (une action peut en appeler
#: une autre ; au-dela, la dependance au body est supposee nulle et signalee).
MAX_ACTION_DEPTH = 3


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def _load_yaml(path: Path):
    import yaml

    data = yaml.safe_load(_read(path))
    return data if isinstance(data, dict) else {}


def _on_block(data: dict) -> dict:
    """Bloc `on:` du workflow (PyYAML lit `on:` comme le booleen True)."""
    on = data.get(True, data.get("on"))
    return on if isinstance(on, dict) else {}


def _trigger_types(data: dict) -> dict:
    """Types declencheurs de `pull_request` / `pull_request_target`."""
    found: dict[str, list] = {}
    for event in ("pull_request", "pull_request_target"):
        block = _on_block(data).get(event)
        if not isinstance(block, dict):
            continue
        types = block.get("types")
        found[event] = list(types) if isinstance(types, list) else []
    return found


def _scripts_in(text: str) -> set[str]:
    return {m.group(0) for m in SCRIPT_RE.finditer(text)}


def _composite_actions(text: str) -> set[str]:
    return {m.group(1) for m in ACTION_RE.finditer(text)}


def _collect_scripts(root: Path, workflow_text: str) -> tuple[set[str], set[str]]:
    """Scripts et actions composites atteignables depuis le workflow.

    Le premier ensemble est l'union des scripts appeles ; le second, les
    scripts appeles par une action composite (nommee a part, parce que c'est
    la que se cache le plus souvent une lecture du body).
    """
    scripts = _scripts_in(workflow_text)
    from_composite: set[str] = set()
    seen: set[str] = set()
    frontier = _composite_actions(workflow_text)
    depth = 0
    while frontier and depth < MAX_ACTION_DEPTH:
        depth += 1
        nxt: set[str] = set()
        for name in frontier:
            if name in seen:
                continue
            seen.add(name)
            action = root / ACTION_DIR / name / "action.yml"
            if not action.is_file():
                continue
            text = _read(action)
            scripts |= _scripts_in(text)
            from_composite |= _scripts_in(text)
            nxt |= _composite_actions(text)
        frontier = nxt
    return scripts, from_composite


def _paths_filtered(data: dict, events: list[str]) -> bool:
    """Le bloc `pull_request` porte-t-il un filtre `paths:` ?

    Ce filtre est evalue sur le diff **base-relative** : un retarget change la
    liste des fichiers qui matchent. C'est l'axe `paths` du verdict.
    """
    on = _on_block(data)
    for event in events:
        block = on.get(event)
        if isinstance(block, dict) and isinstance(block.get("paths"), list):
            return True
    return False


def survey(root: Path, use_detector: bool = True) -> list[dict]:
    """Census complet des workflows qui ecoutent `edited`.

    `use_detector=False` retire la contribution de l'inventaire
    `body_consuming_guards.py` : l'axe `body` ne vient plus que de la lecture
    directe dans le workflow. C'est l'**ablation** : elle repond a « la
    conclusion du census depend-elle de l'exhaustivite du detecteur ? »
    (#22467). Le verdict `verdict_without_detector` est calcule pour chaque
    workflow, meme quand l'ablation n'est pas demandee : la dependance est
    donc visible, pas supposee.
    """
    consumers = discover_consumers(root) if use_detector else {}
    workflows_dir = root / WORKFLOW_DIR
    rows: list[dict] = []
    for path in sorted(workflows_dir.glob("*.yml")):
        rel = path.relative_to(root).as_posix()
        data = _load_yaml(path)
        triggers = _trigger_types(data)
        listening = sorted(
            event for event, types in triggers.items() if "edited" in types
        )
        if not listening:
            continue
        raw = _read(path)
        stripped = _strip_comment_lines(raw)
        scripts, from_composite = _collect_scripts(root, raw)
        body_scripts = sorted(s for s in scripts if s in consumers)
        direct = bool(DIRECT_BODY_RE.search(stripped))
        title = bool(DIRECT_TITLE_RE.search(stripped))
        base = bool(DIRECT_BASE_RE.search(stripped))
        paths = _paths_filtered(data, listening)
        depends = []
        if direct or body_scripts:
            depends.append("body")
        if title:
            depends.append("title")
        if base:
            depends.append("base")
        if paths:
            depends.append("paths")
        verdict = CONTENT_ONLY if not depends else PR_METADATA_DEPENDENT
        # Ablation : sans la contribution du detecteur, l'axe `body` ne peut
        # venir que de la lecture directe dans le workflow.
        depends_without_detector = [
            axis
            for axis in depends
            if axis != "body" or direct
        ]
        rows.append(
            {
                "workflow": rel,
                "listening_events": listening,
                "trigger_types": {e: triggers[e] for e in listening},
                "paths_filtered": paths,
                "body_scripts": body_scripts,
                "body_scripts_via_composite": sorted(
                    s for s in body_scripts if s in from_composite
                ),
                "direct_body_read": direct,
                "depends_on": depends,
                "verdict": verdict,
                "depends_on_without_detector": depends_without_detector,
                "verdict_without_detector": (
                    CONTENT_ONLY
                    if not depends_without_detector
                    else PR_METADATA_DEPENDENT
                ),
            }
        )
    return rows


def render(rows: list[dict]) -> str:
    lines = [
        f"{'workflow':52s} {'verdict':22s} {'depend de':16s} body(scripts)"
    ]
    for row in rows:
        body = ",".join(row["body_scripts"]) or "-"
        lines.append(
            f"{row['workflow'][:52]:52s} {row['verdict']:22s} "
            f"{','.join(row['depends_on']) or '-':16s} {body[:28]}"
        )
    counts: dict[str, int] = {}
    for row in rows:
        counts[row["verdict"]] = counts.get(row["verdict"], 0) + 1
    lines.append("")
    lines.append(
        f"{len(rows)} workflow(s) ecoutent `edited` -- "
        + ", ".join(f"{k}: {v}" for k, v in sorted(counts.items()))
    )
    dependent = [
        row["workflow"]
        for row in rows
        if row["verdict"] != row["verdict_without_detector"]
    ]
    lines.append(
        f"verdict dependant de l'inventaire `body_consuming_guards` : "
        f"{len(dependent)} workflow(s)"
    )
    for workflow in dependent:
        lines.append(f"    {workflow}")
    return "\n".join(lines)


def render_ablation(rows: list[dict]) -> str:
    """Rapport d'ablation : le verdict tient-il sans l'inventaire ?

    On recalcule le census en retirant la contribution du detecteur
    canonique. Si l'ensemble `CONTENT_ONLY` ne change pas, la couverture des
    formes du detecteur ne peut pas changer la conclusion ; s'il change, les
    workflows concernes sont nommes -- la dependance est visible, pas
    supposee (#22467).
    """
    lines = ["Ablation -- census recalcule SANS l'inventaire `body_consuming_guards`", ""]
    with_detector = {
        row["workflow"] for row in rows if row["verdict"] == CONTENT_ONLY
    }
    without_detector = {
        row["workflow"]
        for row in rows
        if row["verdict_without_detector"] == CONTENT_ONLY
    }
    lines.append(f"CONTENT_ONLY avec le detecteur   : {len(with_detector)}")
    lines.append(f"CONTENT_ONLY sans le detecteur   : {len(without_detector)}")
    lines.append("")
    if with_detector == without_detector:
        lines.append(
            "Conclusion : identique. La couverture des formes du detecteur "
            "ne change pas le verdict du census."
        )
    else:
        lines.append(
            "Conclusion : DIFFERENTE. Les workflows ci-dessous ont un verdict "
            "qui repose sur l'inventaire : la forme reconnue par le detecteur "
            "doit etre verifiee a la main."
        )
        for workflow in sorted(without_detector - with_detector):
            lines.append(f"    {workflow}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        default=None,
        help="racine du depot (defaut : racine du repo)",
    )
    parser.add_argument("--json", action="store_true", help="sortie machine")
    parser.add_argument(
        "--only",
        choices=["content-only", "metadata-dependent"],
        default=None,
        help="filtrer sur le verdict",
    )
    parser.add_argument(
        "--ablate-detector",
        action="store_true",
        help=(
            "affiche l'ablation : le verdict recalcule SANS l'inventaire "
            "`body_consuming_guards.py`, pour montrer si la conclusion du "
            "census depend de la couverture des formes de ce detecteur"
        ),
    )
    args = parser.parse_args(argv)

    root = Path(args.root).resolve() if args.root else Path(__file__).resolve().parents[2]
    rows = survey(root)
    if args.only == "content-only":
        rows = [r for r in rows if r["verdict"] == CONTENT_ONLY]
    elif args.only == "metadata-dependent":
        rows = [r for r in rows if r["verdict"] == PR_METADATA_DEPENDENT]

    if args.json:
        print(json.dumps(rows, ensure_ascii=False, indent=1))
    elif args.ablate_detector:
        print(render_ablation(survey(root)))
    else:
        print(render(rows))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
