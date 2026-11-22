#!/usr/bin/env python3
"""La COMPOSITION d'un bloc : la tranche PRIMAIRE et la REPRISE.

Deux choses distinctes, et le melange des deux figeait la rotation (19/11,
DM du coordinateur) :

- la tranche **PRIMAIRE** : les numeros que le curseur sert au tour
  courant. C'est elle qui determine le tour : un rebouclage de la primaire
  ouvre un tour de plus ;
- la **REPRISE** : les numeros illisibles parkes, qui reviennent au service
  SANS prendre la place de la primaire.

La reprise s'ajoute aux grains ET aux conteneurs : un conteneur illisible
revient au service lui aussi.

Les numeros sont rendus **par classe** : l'appelant les passe a
`tapis_ancre.proposer` separement, pour que seule la primaire porte le
curseur.
"""
from __future__ import annotations

from coordination import tapis_ancre, tapis_retry


def compose(grains: list, conteneurs: list, part: int, quota: int,
            ancre_g: int | None, ancre_c: int | None,
            inc_g: dict, inc_c: dict,
            depart_g: int, depart_c: int, avance: int = 0):
    """Le bloc, les tranches primaires et les reprises.

    Rend `(grains_bloc, conteneurs_bloc, primaires, reprises)` : les
    numeros sont donnes par classe, pour que l'appelant les passe a
    `tapis_ancre.proposer` **separement** -- la primaire porte le curseur,
    la reprise ne le porte pas.
    """
    b_g, prim_g = tapis_ancre.membres(grains, ancre_g, part, avance, depart_g)
    b_c, prim_c = tapis_ancre.membres(conteneurs, ancre_c, quota, avance,
                                       depart_c)
    rep_g = tapis_retry.membres_reprise(grains, b_g, inc_g, part)
    rep_c = tapis_retry.membres_reprise(conteneurs, b_c, inc_c, quota)
    reprises = {"grains": [g.numero for g in rep_g],
                "conteneurs": [c.numero for c in rep_c]}
    primaires = {"grains": prim_g, "conteneurs": prim_c}
    return b_g + rep_g, b_c + rep_c, primaires, reprises


def dernier(numeros: list) -> int | None:
    """Le dernier numero servi d'une tranche : l'ancre proposee.

    C'est le **plus grand** numero de la tranche primaire : l'ancre est un
    numero, pas une position (#27242).
    """
    nums = [n for n in numeros if n is not None]
    return max(nums) if nums else None
