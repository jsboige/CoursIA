#!/usr/bin/env python3
"""La POSITION de la lane dans le pool : son decalage, et la tranche du temps.

Deux reperes, tous deux derives du NOM de la lane et de l'heure -- jamais
d'un etat partage :

- le **decalage** : deux lanes ne balayent pas le meme bloc du pool ;
- le **compteur de tranche** : le bloc avance d'un cran toutes les 4 h, donc
  la fenetre qui est servie avance avec le temps, meme a contenu egal.

Ce module est extrait de `coordination.tapis_rotation` (19/11) : la rotation
porte le bloc, cette arithmetique porte la place du bloc.
"""
from __future__ import annotations

import hashlib
from datetime import datetime

#: La fenetre avance d'un bloc par tranche de 4 h.
TRANCHES_JOUR = 6
HEURES_TRANCHE = 24 // TRANCHES_JOUR


def compteur(maintenant: datetime) -> int:
    """Un compteur monotone de tranches de 4 h -- la fenetre avance avec."""
    return maintenant.toordinal() * TRANCHES_JOUR + maintenant.hour // 4


def decalage(lane: str, cle: str, n: int) -> int:
    """Le decalage de la lane sur une liste : deux lanes ne balayent pas le
    meme bloc."""
    if n <= 0:
        return 0
    return int(hashlib.sha256(f"{lane}|{cle}".encode("utf-8")).hexdigest(), 16) % n
