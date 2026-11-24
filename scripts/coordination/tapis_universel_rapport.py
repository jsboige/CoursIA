#!/usr/bin/env python3
"""Le RAPPORT du tirage universel : les grains, leur etat, l'action, la mesure.

Ce module est **extrait** de `coordination.tapis_universel` : il tient son
propre fichier, comme `tapis_leger_texte` pour `tapis_leger`, et le module
d'origine reste sous son plafond de lignes. `tapis_universel.rapport` reste
appelable (l'alias y garde les appelants intacts).
"""
from __future__ import annotations

from datetime import datetime

from coordination import tapis_equilibre, tapis_marqueurs
from coordination.tapis_rapide import Etat


def action_de(e: Etat, lane: str) -> str:
    """Ce que la lane doit faire de ce grain : le qualifier, puis le servir.

    La qualification est le temps d'ACTION : elle lit le corps et le fil
    complet de l'issue et rejoue les neuf regles d'ecart -- l'organe est
    `scripts/coordination/tapis_prise_en_charge.py`.
    """
    base = (f"qualifier #{e.numero} avant action (corps + fil complet, "
            f"scripts/coordination/tapis_prise_en_charge.py) puis la servir")
    if e.consolidation:
        base += " -- issue de consolidation"
    return base


def rapport(etats_: list[Etat], file: list[Etat], lane: str, maintenant: datetime,
            lecture: dict, ecartees: list[dict] | None = None) -> dict:
    """Le rapport du tirage universel : les grains, leur etat, l'action, la mesure.

    Les exclusions en **donnees** sont publiees (`ecartees`), comme dans le
    tirage complet : une exclusion n'est jamais silencieuse. `ecartees` porte
    les issues ecartees (`tapis_labels.ecartees`) -- le `pool` reste le nombre
    d'issues ouvertes, ecartees comprises.
    """
    conso = tapis_equilibre.familles_consolidation(etats_)
    return {
        "lane": lane, "maintenant": tapis_marqueurs._iso(maintenant),
        "lecture": lecture, "pool": len(etats_) + len(ecartees or []),
        "ecartees": {"LABEL": ecartees or []},
        "grains": [{"numero": e.numero, "titre": e.titre,
                    "visites": e.visites, "visites_total": e.visites_total,
                    "consolidation": e.consolidation,
                    "priorite": tapis_equilibre.raisons(e, conso, maintenant),
                    "action": action_de(e, lane)} for e in file],
    }
