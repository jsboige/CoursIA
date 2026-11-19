#!/usr/bin/env python3
"""Le VERDICT TERMINAL d'un lot qualifie : ce qui fait avancer l'ancre.

Une lecture qui echoue n'est pas une decision : le fil illisible
(`FIL_ILLISIBLE`), le mur de lectures atteint (`MUR_EPUISE`), l'echeance
depassee (`ECHEANCE`) et l'issue absente de la reponse (`ABSENT`) REFUSENT
la prise en charge -- le grain n'a pas ete decide, il n'a pas ete lu.

Seul un verdict **connu** fait avancer l'ancre de rotation : un grain
confirme (servable) ou ecarte par une regle de contenu. Un lot PARTIEL --
un numero illisible au milieu de trois decisionnes -- laisse donc l'ancre
en place : le tour ne saute pas le numero non decide (peer, 19/11).
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


def avancer(lane: str, confirmes: dict, ecartees: dict) -> dict:
    """Fait avancer l'ancre de la lane sur les verdicts terminaux.

    Sans lane (un appel hors contexte de lane) rien n'est ecrit : l'ancre
    est un etat de lane.
    """
    if not lane:
        return {}
    return tapis_ancre.avancer(lane, terminaux(confirmes, ecartees))
