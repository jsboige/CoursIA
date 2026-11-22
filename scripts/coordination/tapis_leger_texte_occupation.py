#!/usr/bin/env python3
"""La SECTION OCCUPATION de la sortie texte du tirage leger.

Extraite de ``tapis_leger_texte.py`` (22/11) : le cumul des deux organes du
tapis -- l'**occupation** (#28090) et l'**ordre d'age** (#27223) -- porte la
fonction `texte` au-dessus de 60 lignes, la regle des fonctions. Une
extraction, jamais un plafond releve.
"""
from __future__ import annotations

from coordination import tapis_occupation


def occupation(occ: dict) -> list[str]:
    """Les lignes de la section Occupation ; `[]` s'il n'y a rien a dire.

    Deux formes, jamais melangees :

    - une lane **worker** : les exclusions **affichees** (numero, marque,
      motif), plafonnees -- une exclusion muette est interdite, une liste de
      284 lignes n'est pas un rapport ;
    - une lane qui **gerne** l'urne : la section **courte** (`resume`), qui
      dit ce qui est a l'urne et ce qui est occupe.
    """
    exclus = occ.get("exclus") or []
    if exclus:
        return ([f"\nOccupation ({len(exclus)}) -- ecartees de la tete, "
                 f"affichees, jamais perdues :"]
                + tapis_occupation.rendre_exclus(exclus))
    if occ.get("resume"):
        return (["\nOccupation -- lanes gerantes : les deux classes sont "
                 "une information, pas une exclusion :"] + occ["resume"])
    return []
