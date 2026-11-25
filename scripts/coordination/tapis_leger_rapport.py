#!/usr/bin/env python3
"""Le RAPPORT du tirage leger : l'etat de chaque grain et l'action a faire.

Extrait de ``tapis_leger.py`` (22/11) : le cumul des deux organes du tapis
(l'**occupation** -- l'urne et la PR occupante, #28090 -- et l'**ordre
d'age**, #27223) fait passer le module au-dessus de son plafond de lignes.
Un depassement se paie en extraction, jamais en relevant le plafond.
"""
from __future__ import annotations

from datetime import datetime

from coordination import tapis_labels, tapis_universel, tapis_universel_rapport
from coordination.tapis_marqueurs import _age, lane_de_pr


def rapport(lane: str, graine: str, maintenant: datetime, metas: list[dict],
            duree: float, secondes: float, budget_s: float, etats_: list,
            file: list, prs: list[dict], origami: dict,
            phases: dict | None = None, fenetre: dict | None = None,
            occupation: dict | None = None,
            qualif: dict | None = None, fil_lu: bool = True) -> dict:
    """Le rapport du tirage leger : l'etat de chaque grain et l'action a faire.

    Il porte ce que la **sortie texte** rend (`tapis_leger_texte`).
    `fil_lu` distingue la voie legere qualifiee (fil complet lu) du repli
    chronologique (candidats du cache, fil NON lu).
    """
    vos = sorted((pr for pr in prs if lane_de_pr(pr) == lane),
                 key=lambda pr: pr.get("created_at") or "")
    rapport_ = tapis_universel.rapport(etats_=etats_, file=file,
                                        lane=lane, maintenant=maintenant,
                                        lecture={},
                                        ecartees=tapis_labels.ecartees(metas),
                                        provenance=tapis_universel_rapport.provenance_de(fil_lu))
    rapport_.update({
        "graine": graine, "voie": "leger", "pool": len(metas),
        "fenetre": fenetre or {},
        "lecture": {"issues": len(metas), "secondes": round(secondes, 1),
                    "selection_s": duree, "budget_s": budget_s,
                    "phases": phases or {}, "budget_epuise": False},
        "vos_prs": [{"numero": pr["number"], "titre": pr.get("title") or "",
                     "age_j": _age(maintenant, pr.get("created_at"), 86400)} for pr in vos],
        "qualification": tapis_universel_rapport.bloc_qualification(qualif),
        "origami_parking": origami,
        "occupations": occupation or {"marques": {}, "exclus": []},
    })
    return rapport_
