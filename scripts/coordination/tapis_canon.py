#!/usr/bin/env python3
"""La FORME CANONIQUE : quelle PR **couvre** un grain, et laquelle le mentionne.

Extrait de `coordination.tapis_cle` (19/11) pour tenir le plafond de lignes :
la detection d'un lien canonique est un **organe de lecture**, la cle de
service qui classe le tirage en est un autre.

La forme canonique du depot est une forme de LIGNE : `See #N`, `Part of #N`,
`Closes #N`, `Fix(portee,#N)`. Une PR qui **parle** de l'issue en prose ne la
couvre pas : « Sur #27338, les 8 PRs sont canoniques » n'est pas une
couverture, et « le fix de #201 » non plus (sonde adverse Hermes du 19/11 :
5 sondes, 2 PRs merges sur 100).

Le mot-cle doit donc **OUVRIR** sa ligne -- ou suivre un separateur fort
(`|`, `(`) -- et la decoration markdown (`**`, `-`, `_`) est toleree.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination.tapis_citations import _CITE_RE

#: Les formes qui declarent un travail SUR l'issue. Le mot-cle doit etre a
#: moins de 30 caracteres du numero : `Fix(secrets,#11044)` et `Part of #27338`
#: qualifies ; `Sur #27338` (une mention) ne l'est pas.
_MOTS_CANON = (r"closes|closed|close|fixes|fixed|fix|resolves|resolved|resolve"
                r"|see|part\s+of|part-of")
#: Le mot-cle doit OUVRIR sa ligne, ou suivre un separateur fort (`|`, `(`) :
#: la forme canonique du depot est une forme de LIGNE (`See #N`, `Closes #N`,
#: `Fix(portee,#N)`), pas une mention en prose. Sans cette garde, « le fix de
#: #201 » et « as we see #201 shows growth » comptent comme une couverture
#: (sonde adverse Hermes du 19/11 : 5 sondes, 2 PRs merges sur 100).
CANON_RE = re.compile(
    rf"(?im)(?:^|\n|\||\()[\s>*_`-]*(?:{_MOTS_CANON})[^#\n]{{0,30}}?#(\d+)\b")


def est_canonique(texte: str | None, numero: int) -> bool:
    """Le texte declare-t-il un travail SUR l'issue `numero` ?

    La forme canonique est celle du depot (`See #N`, `Part of #N`,
    `Closes #N`, `Fix(scope,#N)`) : c'est elle qui distingue une PR qui
    **sert** l'issue d'une PR qui la **mentionne**.
    """
    return any(int(n) == int(numero) for n in CANON_RE.findall(texte or ""))


def des_prs_canoniques(prs: list[dict]) -> dict[int, list[dict]]:
    """Les issues COUVERTES par les PRs ouvertes, en forme canonique.

    La date retenue est la **creation** de la PR : une correction poussee
    dans une PR existante ne la recree pas, et ne remet donc pas le grain en
    tete. L'auto-reference est exclue, comme dans la voie large.
    """
    cites: dict[int, list[dict]] = {}
    for pr in prs:
        numero = int(pr.get("number") or 0)
        corps = pr.get("body") or ""
        trouves = {int(x) for x in _CITE_RE.findall(corps)} - {numero}
        for n in sorted(x for x in trouves if est_canonique(corps, x)):
            cites.setdefault(n, []).append(
                {"sha": "pr" + str(numero), "date": pr.get("created_at") or "",
                 "sujet": pr.get("title") or "", "ferme": False,
                 "ouvert": True, "canonique": True, "pr": numero})
    return cites
