#!/usr/bin/env python3
"""Census des workflows qui rejouent sur `pull_request: edited` (#22467).

Le declencheur `edited` rejoue le workflow a chaque edition du titre ou du
body d'une PR. Sur un workflow filtre par `paths`, le filtre reste vrai -- les
fichiers modifies n'ont pas bouge -- donc **chaque edition de body relance le
verdict** sur la meme tete de commit. C'est la source des « premieres
tentatives redondantes » mesurees par `scripts/ci/measure_redundant_runs.py`.

Ce module repond a la question que l'issue #22467 pose en son point 1 :
**quels workflows ecoutent `edited` alors que leur verdict ne depend ni du
titre ni du body ?** La reponse se lit dans le code, pas dans une liste ecrite
a la main :

1. les declencheurs sont lus dans le YAML de chaque workflow ;
2. les scripts appeles par le workflow (et par les actions composites qu'il
   reference) sont releves dans son texte ;
3. la dependance au body est etablie par l'inventaire deja existant
   `scripts/ci/body_consuming_guards.py`, qui decouvre mecaniquement quels
   scripts lisent le body de la PR et par quel canal ;
4. une lecture directe de `github.event.pull_request.body` dans le workflow
   compte aussi comme dependance.

Verdict par workflow :

``PR_METADATA_DEPENDENT``
    le verdict bouge quand le body, le titre ou la base de la PR bouge ->
    `edited` reste utile.
``CONTENT_ONLY``
    le verdict ne depend que du code -> `edited` est gratuit.

Exemples
--------
::

    python scripts/ci/list_edited_trigger_workflows.py
    python scripts/ci/list_edited_trigger_workflows.py --json
    python scripts/ci/list_edited_trigger_workflows.py --only content-only
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


def _trigger_types(data: dict) -> dict:
    """Retourne les types declencheurs de `pull_request` / `pull_request_target`."""
    on = data.get(True, data.get("on"))  # PyYAML lit `on:` comme le booleen True
    if not isinstance(on, dict):
        return {}
    found: dict[str, list] = {}
    for event in ("pull_request", "pull_request_target"):
        block = on.get(event)
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


def survey(root: Path) -> list[dict]:
    """Census complet des workflows qui ecoutent `edited`."""
    consumers = discover_consumers(root)
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
        depends = []
        if direct or body_scripts:
            depends.append("body")
        if title:
            depends.append("title")
        if base:
            depends.append("base")
        verdict = CONTENT_ONLY if not depends else PR_METADATA_DEPENDENT
        rows.append(
            {
                "workflow": rel,
                "listening_events": listening,
                "trigger_types": {e: triggers[e] for e in listening},
                "paths_filtered": any(
                    isinstance(_pull_request_block(data, e).get("paths"), list)
                    for e in listening
                ),
                "body_scripts": body_scripts,
                "body_scripts_via_composite": sorted(
                    s for s in body_scripts if s in from_composite
                ),
                "direct_body_read": direct,
                "depends_on": depends,
                "verdict": verdict,
            }
        )
    return rows


def _pull_request_block(data: dict, event: str) -> dict:
    on = data.get(True, data.get("on"))
    if not isinstance(on, dict):
        return {}
    block = on.get(event)
    return block if isinstance(block, dict) else {}


def render(rows: list[dict]) -> str:
    lines = []
    lines.append(
        f"{'workflow':52s} {'verdict':22s} {'depend de':16s} body(scripts)"
    )
    for row in rows:
        body = ",".join(row["body_scripts"]) or "-"
        lines.append(
            f"{row['workflow'][:52]:52s} {row['verdict']:22s} "
            f"{','.join(row['depends_on']) or '-':16s} {body[:28]}"
        )
    counts = {}
    for row in rows:
        counts[row["verdict"]] = counts.get(row["verdict"], 0) + 1
    lines.append("")
    lines.append(
        f"{len(rows)} workflow(s) ecoutent `edited` -- "
        + ", ".join(f"{k}: {v}" for k, v in sorted(counts.items()))
    )
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
    args = parser.parse_args(argv)

    root = Path(args.root).resolve() if args.root else Path(__file__).resolve().parents[2]
    rows = survey(root)
    if args.only == "content-only":
        rows = [r for r in rows if r["verdict"] == CONTENT_ONLY]
    elif args.only == "metadata-dependent":
        rows = [r for r in rows if r["verdict"] == PR_METADATA_DEPENDENT]

    if args.json:
        print(json.dumps(rows, ensure_ascii=False, indent=1))
    else:
        print(render(rows))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
