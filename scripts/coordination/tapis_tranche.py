#!/usr/bin/env python3
"""La SELECTION d'un bloc : la tranche d'apres l'ancre.

La rotation choisit **QUOI** servir ; l'ordre de priorite decide de l'ordre
rendu (`coordination.tapis_rotation`). Ce module tient l'arithmetique de la
selection : ou commence la tranche, quels numeros la composent.

L'ancre est le **numero** du dernier grain qualifie, pas sa position : une
cloture (ou une arrivee) decale l'index du pool sans sauter de numero.
"""
from __future__ import annotations

from coordination import tapis_tete


def position(nums: list[int], ancre: int | None) -> int:
    """L'index du premier numero strictement superieur a l'ancre (cyclique).

    Ancre absente -> 0 (le tour commence par le plus petit numero). Ancre
    superieure a tous les numeros -> 0 : le tour a boucle, on recommence.
    """
    if not nums or ancre is None:
        return 0
    for i, n in enumerate(nums):
        if n > ancre:
            return i
    return 0


def tranche(nums: list[int], ancre: int | None, part: int,
            avance: int = 0) -> list[int]:
    """La tranche d'apres l'ancre : `part` numeros, cyclique.

    `avance` decale de N tranches (la VAGUE suivante). `nums` est supposee
    TRIEE par numero : c'est l'ordre de couverture du tour.
    """
    if not nums or part <= 0:
        return []
    n = len(nums)
    depart = (position(nums, ancre) + avance * part) % n
    return [nums[(depart + i) % n] for i in range(min(part, n))]


def membres(ordre: list, ancre: int | None, part: int, avance: int = 0,
             depart_alea: int = 0) -> tuple[list, list[int]]:
    """Les membres du bloc, ORDONNES par priorite (l'ordre d'entree).

    La SELECTION est la tranche d'apres l'ancre ; l'ORDRE rendu est celui de
    l'entree : la rotation choisit QUOI servir, la priorite decide de
    l'ordre. Sans ancre, le depart vient de `depart_alea` (le decalage de la
    lane).

    Le second rendu est la **tranche primaire** (les numeros servis, dans
    l'ordre des numeros) : c'est elle qui porte le curseur, et elle doit
    donc etre distinguee de la REPRISE (les illisibles parkes, qui
    reviennent au service sans prendre sa place -- 19/11).
    """
    nums = sorted(g.numero for g in ordre)
    if not nums:
        return [], []
    if ancre is None:
        depart = depart_alea % len(nums)
        tranche_ = [nums[(depart + i) % len(nums)]
                    for i in range(min(part, len(nums)))]
    else:
        tranche_ = tranche(nums, ancre, part, avance)
    choisis = set(tranche_)
    membres_ = [g for g in ordre if g.numero in choisis]
    return (tapis_tete.en_tete(membres_, tranche_[0]), tranche_)
