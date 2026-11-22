#!/usr/bin/env python3
"""Le LOT PUBLIC de la rotation : la suite exacte du chemin public.

`coordination.tapis_leger.tirage` rend le lot que la lane recoit ; ce module
est cette suite, isolee pour que les TESTS portent sur le chemin public et
non sur une reconstitution (revue du 19/11, coordinateur).

La suite : le bloc (`tapis_rotation.bloc`), puis la PROPOSITION de ses
tranches primaires et de ses reprises, classe par classe -- la primaire
porte le curseur, la reprise revient au service.
"""
from __future__ import annotations

from datetime import datetime

from coordination import tapis_ancre, tapis_rotation


def lot_public(lane: str, grains: list, conteneurs: list, n_grains: int,
               taille: int, maintenant: datetime, ancres: dict | None = None):
    """Le lot public et sa fenetre : la proposition comprise.

    Rend `(lot, fenetre)`. `n_grains` est le nombre de grains demande,
    `taille` la taille de la fenetre servie.
    """
    ancres = ancres if ancres is not None else tapis_ancre.lire(lane)
    lot, fen = tapis_rotation.bloc(grains, conteneurs, n_grains, taille, lane,
                                    maintenant, ancres=ancres)
    tapis_ancre.proposer(lane, "grains", fen["primaires"]["grains"],
                          fen["reprises"]["grains"])
    tapis_ancre.proposer(lane, "conteneurs", fen["primaires"]["conteneurs"],
                          fen["reprises"]["conteneurs"])
    return lot, fen
