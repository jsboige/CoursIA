#!/usr/bin/env python3
"""Les citations des COMMITS MERGES : le lien canonique qui couvre un grain.

`coordination.gh_bulk` lit le `git log` d'`origin/main` ; ce module en fait la
**lecture** : il transforme la sortie brute en `{numero: [citations]}`.

Chaque citation porte le **lien canonique** (`See #N`, `Closes #N`,
`Fix(portee,#N)`) qui la distingue d'une simple mention (`(#N)`) : c'est ce
lien qui porte la CLE DE SERVICE du grain (`coordination.tapis_cle`).

Extrait de `gh_bulk.py` pour tenir son plafond de lignes (#27393, 25/11) :
`gh_bulk.py` reste le module qui lance `git` ; ici, rien ne part en reseau.
"""
from __future__ import annotations

import re
from datetime import UTC, datetime

from coordination.tapis_canon import est_canonique
from coordination.tapis_marqueurs import _iso

#: Une mention `#N` dans le corps.
_CITATION_RE = re.compile(r"#(\d+)\b")
# Un commit FERME #N s'il le nomme apres un mot de fermeture, ou dans la portee de son
# sujet (`type(zone,#N):`, le tag du grain) ; `See #N` et `Part of #N` ne livrent rien.
_FERME_RE = re.compile(r"\b(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?)\s*:?\s+#(\d+)\b",
                       re.IGNORECASE)
#: La portee du sujet : `type(zone,#N):`.
_PORTEE_RE = re.compile(r"^[\w.\- ]+\(([^)]*)\)\s*:")


def des_commits_merges(texte: str) -> dict[int, list[dict]]:
    """Les citations de la sortie d'un `git log --format=...`.

    Chaque entree porte `{sha, date, sujet, ferme, canonique}` : `ferme` dit
    si le commit **cloture** le grain, `canonique` si le lien qui le cite
    **couvre** le grain (la CLE DE SERVICE).
    """
    citations: dict[int, list[dict]] = {}
    for record in texte.split("\x1e"):
        parts = record.strip("\n").split("\x1f", 3)
        if len(parts) < 3 or not parts[1].strip().isdigit():
            continue
        date = _iso(datetime.fromtimestamp(int(parts[1]), UTC))
        message = "\n".join(parts[2:])
        portee = _PORTEE_RE.match(parts[2])
        fermes = {int(n) for n in _FERME_RE.findall(message)}
        fermes |= {int(n) for n in _CITATION_RE.findall(portee.group(1))} if portee else set()
        for num in sorted({int(n) for n in _CITATION_RE.findall(message)}):
            citations.setdefault(num, []).append(
                {"sha": parts[0], "date": date, "sujet": parts[2],
                 "ferme": num in fermes,
                 # La mention n'est pas un lien : seule la forme CANONIQUE
                 # candidate le grain a une cle de service (19/11).
                 "canonique": est_canonique(message, num)})
    return citations
