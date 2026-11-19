#!/usr/bin/env python3
"""Le LOT entrelace : la primaire et la reprise ALTERNES.

Un lot primaire-puis-reprises laisse les reprises en QUEUE : une lane qui
ne qualifie que les premiers candidats du lot ne les lit jamais -- mesure
du 19/11 (pool 1..6, taille 2 : les numeros 2, 4 et 6, parkes, n'etaient
qualifies par AUCUN tour).

Le lot alterne donc les deux classes, et le SENS de l'alternance change d'un
tour a l'autre : la reprise passe devant la primaire un tour sur deux. Le
cout : avec un budget de lecture d'un seul candidat par tour, la file de
reprise est malgre tout relue. La primaire, elle, garde TOUS ses creneaux
dans le lot -- son debit n'est reduit que par le budget de lecture de la
lane, et d'un tour sur deux seulement.
"""
from __future__ import annotations


def intercale(primaire: list, reprises: list, reprise_d_abord: bool) -> list:
    """Le lot : primaire et reprise alternes, la reprise d'abord selon le tour.

    Les deux listes sont rendues dans leur ordre d'entree ; aucune n'est
    perdue, aucune n'est dupliquee.
    """
    lot, p, r = [], list(primaire), list(reprises)
    while p or r:
        if r and reprise_d_abord:
            lot.append(r.pop(0))
        if p:
            lot.append(p.pop(0))
        if r and not reprise_d_abord:
            lot.append(r.pop(0))
    return lot
