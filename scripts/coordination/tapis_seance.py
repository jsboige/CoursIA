#!/usr/bin/env python3
"""Les SEANCES de visite : une livraison en ouvre une neuve.

Une visite est une **seance** : les marqueurs d'une meme lane a moins de
`SEANCE_H` heures d'intervalle n'en font qu'une. Les commits de `origin/main`
qui citent l'issue forment des seances sans lane.

**Une livraison en ouvre une neuve** (19/11) : sans cela, une lane qui
enchaîne plusieurs grains du meme umbrella le jour meme n'y compte qu'UNE
visite, et l'issue reste en tete de classement -- mesure : #27338, sept
livraisons dans la journee, comptees une. La session se ferme sur la
livraison (ou la release) ; la suite ouvre une session neuve.
"""
from __future__ import annotations

from datetime import datetime, timedelta

from coordination.tapis_marqueurs import FERME, Evt

#: Deux marqueurs d'une meme lane a moins de SEANCE_H heures font une seance.
SEANCE_H = 24


def par_instants(instants: list[datetime],
                 depuis: datetime | None = None) -> int:
    """Le nombre de seances d'une suite d'instants : un ecart de plus de
    `SEANCE_H` en ouvre une neuve."""
    n, avant = 0, None
    for t in sorted(t for t in instants if depuis is None or t >= depuis):
        if avant is None or t - avant > timedelta(hours=SEANCE_H):
            n += 1
        avant = t
    return n


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
