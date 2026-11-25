#!/usr/bin/env python3
"""Les SEANCES de visite : une livraison en ouvre une neuve.

Une visite est une **seance** : les marqueurs d'une meme lane a moins de
`SEANCE_H` heures d'intervalle n'en font qu'une.

**Une livraison en ouvre une neuve** (19/11) : sans cela, une lane qui
enchaîne plusieurs grains du meme umbrella le jour meme n'y compte qu'UNE
visite, et l'issue reste en tete de classement -- mesure : #27338, sept
livraisons dans la journee, comptees une. La session se ferme sur la
livraison (ou la release) ; la suite ouvre une session neuve.

Ce module porte la regle des **marqueurs** ; celle des **instants** (les
commits qui citent l'issue, sans lane) vit dans
`coordination.tapis_dernier_grain.seances`. Les deux ne sont pas la meme
chose : un ecart d'heures ne dit pas si un marqueur a ferme une seance. Le
compte d'instants que ce module portait aussi -- identique a
`tapis_dernier_grain.seances` -- est retire : une seule fonction fait ce
travail.
"""
from __future__ import annotations

from datetime import datetime, timedelta

from coordination.tapis_marqueurs import FERME, Evt

#: Deux marqueurs d'une meme lane a moins de SEANCE_H heures font une seance.
SEANCE_H = 24


def par_lane(evts: list[Evt], depuis: datetime | None = None) -> int:
    """Les seances d'une lane : une livraison en ouvre une neuve.

    Une release ferme la session sans etre une visite ; une livraison sans
    claim en est une. Les amendements d'un meme grain (CLAIMED-AMEND) restent
    dans la session de leur grain.
    """
    n = 0
    ouverte: datetime | None = None
    for ev in sorted(evts, key=lambda e: e.quand):
        if depuis is not None and ev.quand < depuis:
            continue
        if ouverte is not None and ev.quand - ouverte > timedelta(hours=SEANCE_H):
            n += 1
            ouverte = None
        if ev.marque in FERME:
            if ouverte is not None or ev.marque == "DELIVERED":
                n += 1
            ouverte = None
            continue
        if ouverte is None:
            ouverte = ev.quand
    return n + (1 if ouverte is not None else 0)
