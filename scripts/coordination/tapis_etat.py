#!/usr/bin/env python3
"""La PERSISTANCE de l'etat d'ancre : le fichier, et rien d'autre.

L'etat est un etat de LANE : il vit dans le repertoire local de la machine
(`LOCALAPPDATA`), jamais dans le depot. Un fichier absent ou illisible
vaut INCONNU (fail-CLOSED) : il ne vaut pas zero.

Son SCHEMA (les classes, un etat neuf, les accesseurs) vit dans
`coordination.tapis_etat_schema` ; l'ESTAMPILLE du code qui l'ecrit (le
commit du depot) dans `coordination.tapis_etat_commit`. La machine a etat
elle vit dans `coordination.tapis_ancre`, l'arithmetique de selection dans
`coordination.tapis_tranche`.

Ce module est extrait de `tapis_etat.py` (revue du 19/11) : le plafond de
lignes se paie en **extrait**, pas en relevant le plafond.
"""
from __future__ import annotations

import json
import os
from pathlib import Path

from coordination import tapis_etat_commit
from coordination.tapis_etat_schema import (CLASSES, ancre_de, entiers,  # noqa: F401
                                            inconnus_de, phase_de, tour_de,
                                            vide)

ENV_ETAT = "COURSIA_TAPIS_ANCRE_DIR"


def chemin_etat(lane: str) -> Path:
    """Le fichier d'ancre de la lane (LOCALAPPDATA par defaut)."""
    base = os.environ.get(ENV_ETAT) or os.environ.get("LOCALAPPDATA")
    racine = Path(base) if base else Path.home() / ".coursia"
    return racine / "CoursIA" / "tapis_ancre" / f"{lane.replace(':', '-')}.json"


def lire(lane: str) -> dict:
    """L'etat normalise ; absent ou illisible = inconnu (fail-CLOSED)."""
    etat = vide()
    try:
        brut = json.loads(chemin_etat(lane).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return etat
    if not isinstance(brut, dict):
        return etat
    for c in CLASSES:
        bloc = brut.get(c)
        if not isinstance(bloc, dict):
            continue
        ancre = bloc.get("ancre")
        etat[c]["ancre"] = ancre if isinstance(ancre, int) else None
        tour = bloc.get("tour")
        etat[c]["tour"] = tour if isinstance(tour, int) else 0
        phase = bloc.get("phase")
        etat[c]["phase"] = phase if isinstance(phase, int) else 0
        etat[c]["commit"] = bloc.get("commit")
        etat[c]["attente"] = {n: bool(b) for n, b
                              in entiers(bloc.get("attente"), "attente").items()}
        etat[c]["inconnus"] = entiers(bloc.get("inconnus"), "inconnus")
        primaire = bloc.get("primaire")
        etat[c]["primaire"] = sorted(
            n for n in primaire if isinstance(n, int)) if isinstance(
                primaire, list) else []
    return etat


def ecrire(lane: str, etat: dict) -> Path:
    """Persiste l'etat (une ecriture atomique).

    L'etat porte le COMMIT du code qui l'ecrit : un etat ecrit par un autre
    code n'est pas comparable (la semantique des etats parkes a change le
    19/11), et la mesure qui compare plusieurs tours doit le dire.
    """
    chemin = chemin_etat(lane)
    chemin.parent.mkdir(parents=True, exist_ok=True)
    corps = {c: {"ancre": etat.get(c, {}).get("ancre"),
                  "tour": etat.get(c, {}).get("tour", 0),
                  "phase": etat.get(c, {}).get("phase", 0),
                  "commit": tapis_etat_commit.commit(),
                  "attente": {str(n): b for n, b in
                              etat.get(c, {}).get("attente", {}).items()},
                  "inconnus": etat.get(c, {}).get("inconnus", {}),
                  "primaire": list(etat.get(c, {}).get("primaire") or [])}
             for c in CLASSES}
    tmp = chemin.with_suffix(".tmp")
    tmp.write_text(json.dumps(corps, ensure_ascii=False, indent=1) + "\n",
                   encoding="utf-8")
    tmp.replace(chemin)
    return chemin
