#!/usr/bin/env python3
"""Le COMPTE HISTORIQUE des visites -- extrait du module du classement.

Seam d'extraction de `coordination.tapis_equilibre.py` (19/11) : le module du
classement ne pouvait plus porter la **CLE DE SERVICE** (le departage du
19/11) sans depasser son plafond de lignes.

Le compte est **historique** : il compte les marqueurs du fil et les
citations Git, le plus grand des deux. Le classement, lui, passe par
`tapis_dernier_grain.compter_grains` (les grains seuls) -- le compte
historique ne compte plus, il **annonce**.

`coordination.tapis_equilibre` le reintroduit (`FENETRE_J`, `compter`), donc
les consommateurs (`tapis_universel`) continuent de fonctionner : une seule
adresse.
"""
from __future__ import annotations

from datetime import datetime, timedelta

from coordination import tapis_seance
from coordination.tapis_dernier_grain import seances
from coordination.tapis_marqueurs import FERME, VISITE, Evt, _dt, _iso

FENETRE_J = 7  # le tour : un tour de flotte complet mesure en 4 a 8 jours (16/11)


def compter(evts: list[Evt], citations: list[dict],
            maintenant: datetime) -> tuple[str | None, int, int]:
    """La derniere visite (ISO), les visites au total, celles du tour.

    Le compte **historique** de la **voie legere** (elle ne lit pas le fil) :
    marqueurs et citations, le plus grand des deux ; le classement lui passe
    par `tapis_dernier_grain.compter_grains` (les grains seuls). Les seances
    des marqueurs suivent `tapis_seance.par_lane` (une livraison en ouvre une
    neuve, #27338), celles des citations `seances` ; les citations des PRs
    **ouvertes** comptent UNE visite chacune (elles ne sont pas mergees).
    """
    par_lane: dict[str, list[Evt]] = {}
    visites: list[datetime] = []
    for ev in evts:
        if ev.marque in VISITE:
            visites.append(ev.quand)
            par_lane.setdefault(ev.lane or "?", []).append(ev)
        elif ev.marque in FERME:
            par_lane.setdefault(ev.lane or "?", []).append(ev)
    en_cours = [d for c in citations if c.get("ouvert") and (d := _dt(c.get("date")))]
    commits = [d for c in citations if not c.get("ouvert") and (d := _dt(c.get("date")))]
    tous = visites + commits + en_cours

    def compte(depuis: datetime | None) -> int:
        marques = sum(tapis_seance.par_lane(evs, depuis) for evs in par_lane.values())
        fen = [d for d in en_cours if depuis is None or d >= depuis]
        return max(marques, seances(commits, depuis)) + len(fen)

    return ((_iso(max(tous)) if tous else None), compte(None),
            compte(maintenant - timedelta(days=FENETRE_J)))
