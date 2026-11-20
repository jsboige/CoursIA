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


def evenements_info(comments: list[dict]) -> list[Evt]:
    """Les evenements de visite portes par une forme `[INFO]`."""
    evts: list[Evt] = []
    for c in comments:
        texte = _FENCE_RE.sub("", c.get("body") or "")
        quand = _dt(c.get("created_at")) or _JAMAIS
        lignes: dict[str, None] = {}
        for motif in (_INFO_VISITE_RE, _INFO_LIVRE_RE):
            for m in motif.finditer(texte):
                lignes.setdefault(m.group(0).strip(), None)
        for ligne in lignes:
            evts.append(Evt(quand, "VISITE-INFO", _lane(ligne, texte), None, ligne))
    return sorted(evts, key=lambda e: e.quand)
