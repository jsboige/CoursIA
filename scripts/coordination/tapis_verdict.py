#!/usr/bin/env python3
"""Le VERDICT d'un lot qualifie : ce qui fait avancer le curseur.

Une lecture qui echoue n'est pas une decision : le fil illisible, le mur
atteint, l'echeance et l'issue absente REFUSENT la prise en charge. Seul
un verdict **connu** fait avancer le curseur ; un lot PARTIEL laisse le
curseur en place sur le numero non decide (peer, 19/11). Un refus ne
RETIRE pas la couverture des autres : le numero refuse est PARKE et
revient au tour suivant.
"""
from __future__ import annotations

from coordination import tapis_ancre, tapis_fil_complet, tapis_lot

#: Les codes de REFUS ne sont pas des verdicts terminaux.
CODES_NON_TERMINAUX = tuple(tapis_fil_complet.CODES_REFUS) + (tapis_lot.ABSENT,)


def terminaux(confirmes: dict, ecartees: dict) -> set[int]:
    """Les numeros dont le verdict est connu (confirme ou ecarte)."""
    nums = set(confirmes)
    for n, v in ecartees.items():
        if v.get("code") not in CODES_NON_TERMINAUX:
            nums.add(n)
    return nums


def inconnus(ecartees: dict) -> dict:
    """Les numeros PARKES : la lecture a echoue, le grain n'est pas decide."""
    return {n: {"code": v.get("code"), "motif": v.get("motif", "")}
            for n, v in ecartees.items()
            if v.get("code") in CODES_NON_TERMINAUX}


def avancer(lane: str, confirmes: dict, ecartees: dict,
            lot: set[int] | None = None) -> dict:
    """Fait avancer le curseur de la lane sur les verdicts terminaux.

    `lot` est le lot EFFECTIVEMENT qualifie : le curseur ne passe pas une
    tranche que ce lot n'a pas prise en charge (review du 19/11). Sans lot,
    l'avance est bornee aux numeros **LUS** (famine du 19/11 : le curseur
    passait au max de la tranche alors qu'un seul grain etait lu) : un lu
    et refuse est couvert, un jamais lu est parque. Sans lane, rien.
    """
    if not lane:
        return {}
    term = terminaux(confirmes, ecartees)
    lus = set(confirmes) | set(ecartees)
    return tapis_ancre.avancer(lane, term, inconnus(ecartees),
                               set(lot) if lot is not None else lus)
