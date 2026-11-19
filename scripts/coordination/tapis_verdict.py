#!/usr/bin/env python3
"""Le VERDICT d'un lot qualifie : ce qui fait avancer le curseur.

Une lecture qui echoue n'est pas une decision : le fil illisible
(`FIL_ILLISIBLE`), le mur atteint (`MUR_EPUISE`), l'echeance (`ECHEANCE`)
et l'issue absente (`ABSENT`) REFUSENT la prise en charge -- le grain
n'a pas ete decide, il n'a pas ete lu.
Seul un verdict **connu** fait avancer le curseur de rotation : un grain
confirme (servable) ou ecarte par une regle de contenu. Un lot PARTIEL --
un numero illisible au milieu de trois decisionnes -- laisse donc le
curseur en place sur ce numero : le tour ne saute pas le numero non
decide (peer, 19/11).

**Mais un refus ne RETIRE pas la couverture des autres** (contre-exemple
du 19/11) : le numero refuse est PARKE, il ne bloque pas le curseur et il
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


def avancer(lane: str, confirmes: dict, ecartees: dict) -> dict:
    """Fait avancer le curseur de la lane sur les verdicts terminaux.

    Sans lane (un appel hors contexte de lane) rien n'est ecrit.
    """
    if not lane:
        return {}
    return tapis_ancre.avancer(lane, terminaux(confirmes, ecartees),
                               inconnus(ecartees))
