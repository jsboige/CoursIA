#!/usr/bin/env python3
"""Le RENDU de la **REINTRODUCTION** (fail-OPEN) : le pool revient, et il
faut le dire.

Extrait de `tapis_occupation_rapport.py` le 25/11 (review du coordinateur
sur #28435) : la reintroduction n'est pas une exclusion, c'est une
**decision** -- le grain de harnais reintroduit doit etre qualifie avant
d'etre servi. Elle a donc son propre rendu, et son propre module : la
confondre avec une exclusion muette Pretendrait que les deux sorties sont
identiques.
"""
from __future__ import annotations


def rendre_reintroduction(rein: dict) -> list[str]:
    """Les lignes de la **REINTRODUCTION** (fail-OPEN) ; `[]` sinon.

    Le fail-OPEN (I1) : quand l'exclusion des grains de harnais vide le
    pool, le pool revient -- et le rapport doit le dire, avec le besoin de
    qualification du grain reintroduit.
    """
    if not rein:
        return []
    numeros = ", ".join(f"#{n}" for n in rein.get("numeros") or [])
    return [f"\nReintroduction (fail-OPEN) -- {rein.get('motif')}",
            f"  grain(s) reintroduit(s) : {numeros}",
            "  a QUALIFIER avant d'etre servi (tapis_prise_en_charge.py)"]
