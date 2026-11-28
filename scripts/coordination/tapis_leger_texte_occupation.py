#!/usr/bin/env python3
"""La SECTION OCCUPATION de la sortie texte du tirage leger.

Extraite de ``tapis_leger_texte.py`` (22/11) : le cumul des deux organes du
tapis -- l'**occupation** (#28090) et l'**ordre d'age** (#27223) -- porte la
fonction `texte` au-dessus de 60 lignes. Une extraction, jamais un plafond.
"""
from __future__ import annotations

from coordination import tapis_occupation


def occupation(occ: dict) -> list[str]:
    """Les lignes de la section Occupation ; `[]` s'il n'y a rien a dire.

    Une lane **worker** : les exclusions **affichees** (numero, marque,
    motif), plafonnees -- une exclusion muette est interdite. Une lane qui
    **gerne** l'urne : la section **courte** (`resume`). La
    **reintroduction** (fail-OPEN) est rendue a part : c'est une decision,
    le grain rendu doit etre qualifie avant d'etre servi.
    """
    lignes: list[str] = []
    exclus = occ.get("exclus") or []
    if exclus:
        lignes += [f"\nOccupation ({len(exclus)}) -- ecartees de la tete, "
                   "affichees, jamais perdues :"]
        lignes += tapis_occupation.rendre_exclus(exclus)
    elif occ.get("resume"):
        lignes += ["\nOccupation -- lanes gerantes : les deux classes sont "
                   "une information, pas une exclusion :"] + occ["resume"]
    lignes += tapis_occupation.rendre_reintroduction(
        occ.get("reintroduction") or {})
    return lignes
