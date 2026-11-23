#!/usr/bin/env python3
"""Les formes `[INFO]` qui valent une VISITE (#27590, dispatch c2014).

Le secretariat et l'adjoint rendent compte d'une visite par une ligne
`[INFO]` : ils ne posent ni `[CLAIMED]` ni `[DELIVERED]`. Sans ces formes,
`visit_coverage` ne voit pas leurs visites, et l'issue qu'ils ont regardee
passe pour jamais servie.

Une lecture n'est pas une avancee : ces evenements comptent pour les visites
et jamais pour `avancee()`, qui ne voit que `[DELIVERED]` et les commits
cites.
"""
from __future__ import annotations

import re

from coordination.tapis_marqueurs import (
    Evt, _DECOR, _FENCE_RE, _INFO_LIVRE_RE, _JAMAIS, _dt, _lane,
)

# `[INFO] Visite ...` : le mot suit immediatement le tag, une ligne `[INFO]`
# quelconque ne vaut pas une visite (119 formes `lane ...` mesurees sur 7 j).
_INFO_VISITE_RE = re.compile(
    _DECOR + r"\[INFO\][ \t]*visite\b[^\n]*", re.MULTILINE | re.IGNORECASE)
#: Une visite **annulee** n'est pas une visite : la ligne dit que la lecture
#: n'a pas eu lieu. Forme mesuree : `[INFO] Visite annulee -- ...`.
_ANNULEE_RE = re.compile(r"\bvisite\s+annul", re.IGNORECASE)


def _ligne_de(texte: str, debut: int) -> str:
    """La ligne complete qui contient la position `debut`."""
    debut_ligne = texte.rfind("\n", 0, debut) + 1
    fin = texte.find("\n", debut)
    return texte[debut_ligne:fin if fin != -1 else len(texte)]


def evenements_info(comments: list[dict]) -> list[Evt]:
    """Les evenements de visite portes par une forme `[INFO]`.

    La deduplication se fait par **ligne**, pas par le fragment capture : une
    ligne qui repond aux deux formes (`[INFO] Visite ... candidate-delivered`)
    ne compte qu'une fois. Une visite annulee ne compte pas.
    """
    evts: list[Evt] = []
    for c in comments:
        texte = _FENCE_RE.sub("", c.get("body") or "")
        quand = _dt(c.get("created_at")) or _JAMAIS
        lignes: dict[str, None] = {}
        for motif in (_INFO_VISITE_RE, _INFO_LIVRE_RE):
            for m in motif.finditer(texte):
                ligne = _ligne_de(texte, m.start()).strip()
                if _ANNULEE_RE.search(ligne):
                    continue
                lignes.setdefault(ligne, None)
        for ligne in lignes:
            evts.append(Evt(quand, "VISITE-INFO", _lane(ligne, texte), None, ligne))
    return sorted(evts, key=lambda e: e.quand)
