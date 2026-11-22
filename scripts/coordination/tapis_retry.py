#!/usr/bin/env python3
"""La FILE DE REPRISE des numeros illisibles : bornee, et nommee.

Un numero dont la lecture a echoue n'est pas decide : il ne doit ni figer
la rotation (le curseur passe par-dessus), ni etre perdu. Il est **PARKE**
dans une file de reprise **BORNEE** : au-dela de la borne, le plus ancien
est rendu -- il reste couvert par la rotation cyclique, qui repasse sur lui
au tour suivant. La borne est donc une borne de *latence*, pas une perte.

La file est un etat de LANE : elle vit avec l'ancre, dans
`coordination.tapis_etat`.
"""
from __future__ import annotations

#: La file de reprise est BORNEE : le nombre de numeros illisibles qu'on
#: garde en memoire. Au-dela, le plus ancien est rendu a la rotation.
MAX_REPRISES = 32


def parquer(inc: dict, n: int, info: dict) -> dict:
    """PARQUE un numero illisible ; la file reste bornee."""
    inc.pop(n, None)
    inc[n] = info
    while len(inc) > MAX_REPRISES:
        inc.pop(next(iter(inc)))
    return inc


def a_retry(inc: dict, limite: int) -> list[int]:
    """Les numeros a re-proposer : les plus anciens, bornees par `limite`."""
    return list(inc)[:max(0, int(limite))]


def membres_reprise(ordre: list, retenus: list, inc: dict, limite: int) -> list:
    """Les membres a re-proposer, dans l'ordre du classement (entree).

    Un numero PARKÉ est servi a nouveau, sans doubbler les membres deja
    retenus par la tranche du tour.
    """
    if not inc or limite <= 0:
        return []
    pris = {g.numero for g in retenus}
    return [g for g in ordre if g.numero in inc and g.numero not in pris][:limite]
