#!/usr/bin/env python3
"""La ROTATION du pool : le bloc servi, et la rotation par NUMERO.

Le classement change a chaque tour : une rotation qui suit la POSITION fait
passer des issues a travers le bloc, et le tour ne se ferme pas -- mesure du
19/11 : **380 issues sur 440** atteintes en un tour, un tour complet en
demandait 440. La rotation suit donc le **NUMERO** : l'ordre des numeros ne
bouge pas, le tour se ferme.

Le bloc est CONTIGU de cet ordre, decale par lane : deux lanes ne balayent pas
le meme bloc. Une tranche de 4 h fait avancer le bloc d'un cran, et un tour
complet tient en `ceil(pool / taille)` tranches -- le delai max de
requalification est publie avec le bloc.

**Chaque numero du pool sort avec un verdict** (#27242) : le bloc publie les
numeros qu'il **visite** et ceux qu'il ne visite pas (`non_visites`). L'ANCRE
(dernier numero qualifie) choisit QUOI servir, la **PRIORITE** l'ordre rendu.
"""
from __future__ import annotations

import hashlib
from datetime import datetime

from coordination import tapis_ancre
from coordination.tapis_rapide import PART_CONTENEURS

#: La fenetre avance d'un bloc par tranche de 4 h.
TRANCHES_JOUR = 6
HEURES_TRANCHE = 24 // TRANCHES_JOUR


def _compteur(maintenant: datetime) -> int:
    """Un compteur monotone de tranches de 4 h -- la fenetre avance avec."""
    return maintenant.toordinal() * TRANCHES_JOUR + maintenant.hour // 4


def _decalage(lane: str, cle: str, n: int) -> int:
    """Le decalage de la lane sur une liste : deux lanes ne balayent pas le
    meme bloc."""
    if n <= 0:
        return 0
    return int(hashlib.sha256(f"{lane}|{cle}".encode("utf-8")).hexdigest(), 16) % n


def bloc(grains: list, conteneurs: list, n_grains: int, taille: int, lane: str,
         maintenant: datetime, bloc_suivant: int = 0,
         ancres: dict | None = None) -> tuple[list, dict]:
    """Le bloc servi : la rotation par numero, dans la fenetre de la lane.

    Les GRAINS et les CONTENEURS ont chacun leur tranche et leur bloc : un
    conteneur ne passe jamais devant un grain (#26926), et son quota tient
    dans la file comme dans la voie lourde.

    `bloc_suivant` decale le bloc de N blocs : c'est la VAGUE suivante de la
    prise en charge. `ancres` porte le dernier numero qualifie par classe :
    c'est l'ancre PERSISTANTE (`tapis_ancre`), celle qui survit a une
    cloture ou a une arrivee.
    """
    quota = max(1, int(n_grains * PART_CONTENEURS)) if conteneurs else 0
    part = max(taille - quota, 1)
    n_g, n_c = len(grains), len(conteneurs)
    compteur = _compteur(maintenant) + bloc_suivant
    ancres = ancres or {}
    b_g, ancre_g = tapis_ancre.membres(
        grains, ancres.get("grains"), part, bloc_suivant,
        _decalage(lane, "grains", n_g) + compteur * part)
    b_c, ancre_c = tapis_ancre.membres(
        conteneurs, ancres.get("conteneurs"), quota, bloc_suivant,
        _decalage(lane, "conteneurs", n_c) + compteur * quota)
    pool = {g.numero for g in grains} | {g.numero for g in conteneurs}
    visites = {g.numero for g in b_g} | {g.numero for g in b_c}
    blocs = max((n_g + part - 1) // part if n_g else 1,
                (n_c + quota - 1) // quota if n_c else 1)
    return b_g + b_c, {
        "taille": taille, "grains": len(b_g), "conteneurs": len(b_c),
        "bloc": (_decalage(lane, "grains", n_g) // part) + 1 if n_g else 0,
        "blocs": blocs, "pool": n_g, "tranche": compteur,
        "ordre": "numero", "delai_max_h": HEURES_TRANCHE * blocs,
        "ancres": {"grains": ancre_g, "conteneurs": ancre_c},
        "visites": sorted(visites), "non_visites": sorted(pool - visites)}
