"""Lecture des verdicts d'etat NON REPARABLE portes par une annotation.

Le DWELL (#15910) et l'INCONCLUSIVE du gate (#26564, residu 1 de #26551) sont
deux ETATS, pas des defauts de la PR : aucun des deux ne nomme d'organe, et
le seul geste possible est d'attendre ou de rejouer la jambe.

- DWELL : un plancher de merge a ecouler (le temps le leve).
- INCONCLUSIVE : le quota d'installation GitHub App est epuise, donc l'etat
  des checks est **INCONNU, pas faux** (seul un rejeu apres le reset leve).

Ce module en possede la LECTURE ; le format de chaque message appartient a
son emetteur (`merge_dwell`, `pr_gate`), jamais ici.

Il vit hors de `scripts/pick_idle_grain.py` pour une raison ecrite : le
picker est deja un fichier de ~15 000 lignes, et la contrainte de #26564 est
que la correction ne le fasse PAS grossir.
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys

REPO = "jsboige/CoursIA"
_HERE = pathlib.Path(__file__).resolve().parent
_SCRIPTS = _HERE.parent


def optional_parser(module: str, attr: str, root: pathlib.Path):
    """`module.attr`, ou None si l'import est impossible.

    Import tardif et defensif : l'organe est optionnel, son absence rend le
    verdict illisible -- donc le fail-closed de l'appelant, jamais un crash.
    """
    try:
        sys.path.insert(0, str(root))
        return getattr(__import__(module), attr)
    except Exception:  # noqa: BLE001 - organe optionnel
        return None


def dwell_parser():
    """`merge_dwell.parse_pending_message`, ou None si l'import est impossible."""
    return optional_parser("merge_dwell", "parse_pending_message", _HERE)


def inconclusive_parser():
    """`pr_gate.parse_inconclusive_message`, ou None si l'import est impossible."""
    return optional_parser("pr_gate", "parse_inconclusive_message", _SCRIPTS)


def verdict_from_annotations(annotations, parser):
    """Premier verdict trouve dans les annotations, ou None."""
    if parser is None or annotations is None:
        return None
    for ann in annotations or []:
        parsed = parser(ann.get("message") or "")
        if parsed:
            return parsed
    return None


def read_annotations(check_run_id: int, read_cache=None, store_cache=None) -> list | None:
    """Annotations d'un check-run, ou None si elles sont illisibles.

    `read_cache`/`store_cache` sont les fonctions de cache du caller ; sans
    elles, la lecture est directe.
    """
    try:
        if read_cache is not None:
            cached = read_cache(check_run_id)
            if cached is not None:
                return cached
        raw = subprocess.run(
            ["gh", "api", f"repos/{REPO}/check-runs/{check_run_id}/annotations"],
            capture_output=True, text=True, encoding="utf-8", check=True, timeout=60,
        ).stdout
        annotations = json.loads(raw)
        if store_cache is not None:
            store_cache(check_run_id, annotations)
        return annotations
    except Exception:  # noqa: BLE001 - reseau/parse : fail-closed, jamais un crash
        return None


def unknown_verdict(check_run_id: int, read_cache=None, store_cache=None) -> dict | None:
    """Le verdict d'etat NON REPARABLE porte par l'annotation, ou None.

    Le DWELL d'abord (un minuteur ne se relit pas), l'INCONCLUSIVE ensuite.
    Le verdict porte son `state` : c'est ce qui distingue les deux etats.
    """
    annotations = read_annotations(check_run_id, read_cache, store_cache)
    if annotations is None:
        return None
    for parser, state in ((dwell_parser(), "dwell"),
                          (inconclusive_parser(), "inconclusive")):
        verdict = verdict_from_annotations(annotations, parser)
        if verdict:
            return {**verdict, "state": state}
    return None


def print_inconclusive_waiting(items) -> None:
    """Rend la section INCONCLUSIVE du rapport de rouge.

    Ces rouges ne comptent pas dans le refus et ne sont PAS imputes a la base :
    l'etat des checks est INCONNU, pas faux. Le seul geste est le rejeu de la
    jambe apres le reset du quota -- pas un push.
    """
    if not items:
        return
    print("VERDICT INCONCLUSIVE -- l'etat des checks est INCONNU, pas faux :")
    for item in items:
        print(f"  - #{item['number']} {item['check']}")
        detail = (item.get("detail") or "").strip()
        if detail:
            print(f"      {detail[:200]}")
    print("Ces rouges ne comptent pas dans le refus et ne sont PAS imputes a la")
    print("base. NE PAS pousser pour les lever : le quota se rejoue. Apres le")
    print("reset, rejouer la jambe (`gh run rerun <run_id> --job <job_id>`) ou")
    print("laisser le balayage `pr-gate-stale-sweep` s'en charger, puis")
    print("enchainer un autre grain -- c'est la candidate qui attend.")
    print()
