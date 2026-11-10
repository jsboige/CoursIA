#!/usr/bin/env python3
"""Coherence de l'etat widgets entre un carnet source execute et son jumeau derive.

Origine : PR #21496. La resynchronisation T4 recopie les cellules de code du
carnet source (FR) dans son jumeau traduit (EN), sorties comprises, mais pas
``metadata.widgets``. Le jumeau affiche alors des vues de widget
(``application/vnd.jupyter.widget-view+json``) dont le ``model_id`` n'existe
dans aucun modele de son propre etat : les sorties sont muettes au rendu, et
l'etat qu'il porte encore est orphelin (aucune sortie ne le reference).

Trois verdicts :

``OK``
    Chaque reference de vue de widget du jumeau resout dans son propre etat.
``DANGLING_FROM_SOURCE``
    Les references non resolues existent toutes dans l'etat du carnet source :
    la sortie vient du source, l'etat doit en venir aussi. ``--apply`` recopie
    l'etat du source et rend le jumeau coherent.
``DANGLING_UNRESOLVABLE``
    Au moins une reference n'existe dans aucun des deux etats : l'etat manquant
    ne peut pas etre reconstitue par recopie — le jumeau doit etre re-execute.
    Aucun ``--apply`` n'est alors effectue.

Usage :
    python scripts/translation/check_twin_widget_state.py \
        --source <carnet source> --twin <carnet jumeau> [--json] [--apply]

Sortie : 0 si OK (ou si ``--apply`` a rendu le jumeau coherent), 1 sinon.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import sys
from typing import Any

VIEW_MIME = "application/vnd.jupyter.widget-view+json"
STATE_MIME = "application/vnd.jupyter.widget-state+json"


def _widgets(nb: dict[str, Any]) -> dict[str, Any]:
    """Bloc metadata.widgets d'un carnet (dict vide s'il est absent)."""
    meta = nb.get("metadata") or {}
    widgets = meta.get("widgets") or {}
    return widgets if isinstance(widgets, dict) else {}


def widget_state(nb: dict[str, Any]) -> dict[str, Any]:
    """Modeles de widgets portes par le carnet, indexes par model_id."""
    block = _widgets(nb).get(STATE_MIME) or {}
    state = block.get("state") or {}
    return state if isinstance(state, dict) else {}


def widget_refs(nb: dict[str, Any]) -> list[tuple[str, str | None]]:
    """(cell_id, model_id) de chaque vue de widget presente dans les sorties."""
    refs: list[tuple[str, str | None]] = []
    for cell in nb.get("cells") or []:
        if cell.get("cell_type") != "code":
            continue
        for out in cell.get("outputs") or []:
            data = out.get("data") or {}
            if VIEW_MIME in data:
                refs.append((cell.get("id") or "?", (data[VIEW_MIME] or {}).get("model_id")))
    return refs


def analyse(source_nb: dict[str, Any], twin_nb: dict[str, Any]) -> dict[str, Any]:
    """Verdict de coherence de l'etat widgets du jumeau contre sa source."""
    twin_state = widget_state(twin_nb)
    source_state = widget_state(source_nb)
    refs = widget_refs(twin_nb)
    dangling = [(cid, mid) for cid, mid in refs if mid not in twin_state]
    resolvable_from_source = [d for d in dangling if d[1] in source_state]
    unresolvable = [d for d in dangling if d[1] not in source_state]
    referenced_twin = {mid for _cid, mid in refs}
    orphan_models = sorted(set(twin_state) - referenced_twin)

    if not dangling:
        verdict = "OK"
    elif unresolvable:
        verdict = "DANGLING_UNRESOLVABLE"
    else:
        verdict = "DANGLING_FROM_SOURCE"

    return {
        "verdict": verdict,
        "twin_models": len(twin_state),
        "source_models": len(source_state),
        "refs": len(refs),
        "dangling": [{"cell": c, "model_id": m} for c, m in dangling],
        "resolvable_from_source": len(resolvable_from_source),
        "unresolvable": [{"cell": c, "model_id": m} for c, m in unresolvable],
        "orphan_models_in_twin": len(orphan_models),
    }


def apply_source_state(source_nb: dict[str, Any], twin_nb: dict[str, Any]) -> bool:
    """Recopie metadata.widgets de la source dans le jumeau. True si ecrit."""
    source_block = _widgets(source_nb).get(STATE_MIME)
    if not isinstance(source_block, dict):
        return False
    meta = twin_nb.setdefault("metadata", {})
    widgets = meta.setdefault("widgets", {})
    widgets[STATE_MIME] = json.loads(json.dumps(source_block))
    return True


def _load(path: pathlib.Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _dump(path: pathlib.Path, nb: dict[str, Any]) -> None:
    path.write_bytes(json.dumps(nb, indent=1, ensure_ascii=False).encode("utf-8") + b"\n")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--source", required=True, type=pathlib.Path)
    ap.add_argument("--twin", required=True, type=pathlib.Path)
    ap.add_argument("--json", action="store_true", help="sortie machine")
    ap.add_argument("--apply", action="store_true",
                    help="recopier l'etat widgets de la source quand il resout tout")
    args = ap.parse_args(argv)

    source_nb = _load(args.source)
    twin_nb = _load(args.twin)
    report = analyse(source_nb, twin_nb)

    applied = False
    if args.apply and report["verdict"] == "DANGLING_FROM_SOURCE":
        if apply_source_state(source_nb, twin_nb):
            _dump(args.twin, twin_nb)
            report = analyse(source_nb, _load(args.twin))
            applied = True
    report["applied"] = applied

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(f"verdict: {report['verdict']}")
        print(f"  modeles jumeau={report['twin_models']} source={report['source_models']} "
              f"references={report['refs']} orphelins={report['orphan_models_in_twin']}")
        for d in report["dangling"]:
            print(f"  reference non resolue: cellule {d['cell']} model_id={d['model_id']}")
        if applied:
            print("  etat widgets recopie depuis la source")

    return 0 if report["verdict"] == "OK" else 1


if __name__ == "__main__":
    sys.exit(main())
