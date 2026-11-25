#!/usr/bin/env python3
"""Le LOT PUBLIC de la rotation : la suite exacte du chemin public.

`coordination.tapis_leger.tirage` rend le lot que la lane recoit ; ce module
est cette suite, isolee pour que les TESTS portent sur le chemin public et
non sur une reconstitution (revue du 19/11, coordinateur). La suite : le bloc
(`tapis_rotation.bloc`), puis la PROPOSITION de ses tranches primaires et de
ses reprises, classe par classe -- la primaire porte le curseur.
"""
from __future__ import annotations

from datetime import datetime

from coordination import tapis_ancre, tapis_rotation


def lot_public(lane: str, grains: list, conteneurs: list, n_grains: int,
               taille: int, maintenant: datetime, ancres: dict | None = None,
               ages_g: list | None = None, exclus_g: set | None = None,
               reboucle: bool = True, reinit: bool = False):
    """Le lot public et sa fenetre : la proposition comprise.

    Rend `(lot, fenetre)`. `n_grains` est le nombre de grains demande,
    `taille` la taille de la fenetre servie.

    `ages_g` / `exclus_g` : la SELECTION par AGE des grains (mandat du 22/11)
    -- l'ordre d'age, et les numeros deja servis. `reboucle=False` : pas de
    rebouclage par numero. `reinit` : le tour est couvert, la file d'attente
    est rendue et le tour recommence.
    """
    ancres = ancres if ancres is not None else tapis_ancre.lire(lane)
    lot, fen = tapis_rotation.bloc(grains, conteneurs, n_grains, taille, lane,
                                    maintenant, ancres=ancres, ages_g=ages_g,
                                    exclus_g=exclus_g)
    tapis_ancre.proposer(lane, "grains", fen["primaires"]["grains"],
                          fen["reprises"]["grains"], reboucle=reboucle,
                          reinit=reinit)
    tapis_ancre.proposer(lane, "conteneurs", fen["primaires"]["conteneurs"],
                          fen["reprises"]["conteneurs"])
    return lot, fen
