#!/usr/bin/env python3
"""Les formes CANONIQUES d'un lien vers une issue.

Une PR **couvre** un grain quand elle porte un lien canonique vers lui. La
forme est celle du depot (`.claude/rules/git-workflow.md`, § lien canonique) :
le mot-cle precede immediatement la reference.

- `See #N`, `Part of #N` : le lien ;
- `Closes #N`, `Close #N`, `Fixes #N`, `Fixed #N`, `Resolves #N` : la
  fermeture ;
- `Fix(portee,#N)` : la forme composee, la portee entre parentheses.

Une mention en prose (`#N` seul, `Refs #N`, `cf. #N`) ne prouve **rien** :
l'arbitrage du coordinateur (19/11 17:14Z) est « ni une mention libre ni
See/Part of seuls ne prouvent un service ». Le lien canonique est donc un
**candidat** ; c'est le diff qui fait foi.

Doc : docs/reference/tapis-rapide.md.
"""
from __future__ import annotations

import re

#: Le mot-cle suivi de la reference -- aucun texte libre entre les deux.
_LIEN = re.compile(
    r"\b(?:See|Part\s+of|Close[sd]?|Fix(?:e[sd])?|Resolv(?:e[sd]?))\s*:?\s+#(\d+)\b",
    re.IGNORECASE)
#: La forme composee : `Fix(portee,#N)`, la portee est un texte court.
_FORME = re.compile(r"\bFix\s*\(([^)\n]{0,60}?),\s*#(\d+)\s*\)", re.IGNORECASE)


def est_canonique(texte: str, numero: int) -> bool:
    """Le texte porte-t-il un lien canonique vers `numero` ?"""
    return str(numero) in {str(n) for n in liens_canoniques(texte)}


def liens_canoniques(texte: str) -> set[int]:
    """Les numeros joints par un lien canonique dans le texte."""
    if not texte:
        return set()
    out = {int(m.group(1)) for m in _LIEN.finditer(texte)}
    out |= {int(m.group(2)) for m in _FORME.finditer(texte)}
    return out


def des_prs_canoniques(prs) -> dict[int, list[dict]]:
    """Les PRs qui couvrent un grain, par numero de grain.

    Chaque entree porte `{"pr": numero, "date": creation, "sujet": titre}`.
    La date d'une PR est sa **creation** : une correction poussee dans une
    PR existante ne la recree pas -- elle ne remet donc pas le grain en
    tete (mandat du 19/11).
    """
    out: dict[int, list[dict]] = {}
    for pr in prs or []:
        numero = pr.get("number")
        if not numero:
            continue
        for n in liens_canoniques(pr.get("body") or ""):
            out.setdefault(n, []).append(
                {"pr": int(numero), "date": pr.get("created_at") or "",
                 "sujet": (pr.get("title") or "")[:80]})
    return out
