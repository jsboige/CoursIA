#!/usr/bin/env python3
"""Les TAILLES du bloc : le quota des conteneurs, la part des grains, le nombre de blocs.

Ces trois nombres forment **une seule** arithmetique, partagee par la rotation
(`tapis_rotation.bloc`) et par le repli chronologique (`tapis_repli.replir`).
Les dupliquer est ce qui a rompu le cycle du repli (26/11) : le repli comptait
ses blocs avec la taille **demandee** (8) alors que la composition reserve un
creneau aux conteneurs -- la tranche primaire des grains mesurait donc 6. Le
cycle annonce (60) etait plus court que le cycle reel (80) : le curseur
rebouclait avant la fin de l'ordre d'age, et **115 issues sur 558 n'etaient
jamais servies** -- la queue du pool, bande des issues fresh comprise.

Le module ne fait rien d'autre : il donne les trois nombres, et les deux
organes qui les utilisent les lisent ici.
"""
from __future__ import annotations

from coordination.tapis_rapide import PART_CONTENEURS


def quotas(n_grains: int, taille: int, n_conteneurs: int) -> tuple[int, int]:
    """(quota des conteneurs, part des grains) : les deux tailles du bloc.

    Les conteneurs partagent le lot : ils prennent un creneau, et la tranche
    **primaire** des grains est donc plus courte que la taille demandee.
    """
    quota = max(1, int(n_grains * PART_CONTENEURS)) if n_conteneurs else 0
    part = max(taille - quota, 1)
    return quota, part


def nombre_blocs(n_g: int, n_c: int, part: int, quota: int) -> int:
    """Le nombre de blocs que la rotation parcourt : le plus long des deux.

    Les grains (`n_g` par tranches de `part`) et les conteneurs (`n_c` par
    tranches de `quota`) avancent de front : c'est le cycle le plus long qui
    decide -- sinon la queue d'une classe n'est jamais atteinte.
    """
    return max((n_g + part - 1) // part if n_g else 1,
               (n_c + quota - 1) // quota if n_c else 1)
