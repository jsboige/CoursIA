#!/usr/bin/env python3
"""La TETE d'un lot : le numero que la rotation sert en premier.

La priorite d'entree ne peut pas porter la tete : elle gardait le meme
membre en tete de chaque tranche (le plus prioritaire du bloc), et le
curseur sautait alors par blocs entiers -- les grains du milieu du bloc
n'etaient plus jamais servis (famine du 19/11 : 4 lus sur 80 en 400 tours).

La tete est donc le **numero suivant le curseur** (l'ordre de la rotation) ;
le reste du lot garde l'ordre de priorite.
"""
from __future__ import annotations


def en_tete(membres: list, numero: int) -> list:
    """Le membre `numero` d'abord, le reste dans l'ordre recu."""
    return ([g for g in membres if g.numero == numero]
            + [g for g in membres if g.numero != numero])
