#!/usr/bin/env python3
"""La CLE DE SERVICE d'un grain : la date de la derniere PR qui le COUVRE.

Mandat du coordinateur (19/11/2026, DM `20261119-picker-date-pr-parent`) :
« Remplacer poids/bonus/seances par une voix par issue, ordre de la derniere PR
dont le diff couvre le grain, departage uniforme a egalite ; sans PR,
vieillissement depuis la creation (pas d'anciennete heritee). Une PR enfant
remet aussi le hub en queue, pas les freres ; pas de nouveau service sur
correction de PR existante. »

Trois regles, et rien d'autre :

1. **Une voix par issue** : la cle est UNE date par grain. Ni bonus d'age, ni
   bonus de consolidation, ni nombre de visites n'ordonnent le tirage.
2. **La cle est la derniere PR qui COUVRE le grain** : la couverture se lit
   dans le **corps** de la PR, en forme **canonique** (`See #N`, `Part of #N`,
   `Closes #N`, `Fix(...#N)`...). Une PR qui **mentionne** l'issue en prose ne
   la couvre pas -- c'est la distinction qui manquait : la PR #27368, qui
   *parle* de #27338 sans le servir, ne le sert pas.
3. **Le hub suit son enfant** : la PR d'un enfant (E) remonte la cle du **hub**
   (H) -- et **seulement** lui : les **freres** (F) gardent leur propre cle.
   Un pli **neuf** n'herite pas de l'age du hub : sans PR, la cle est la
   **creation** du grain.

La date d'une PR est sa **creation** : une correction poussee dans une PR
existante ne la recree pas -- elle ne remet donc pas le grain en tete.

La DENSITE d'un hub (le nombre d'enfants reels) est une **mesure**, pas un
bonus : elle se lit, elle ne classe pas.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination.tapis_citations import _CITE_RE
from coordination.tapis_marqueurs import _dt, _iso

#: Les formes qui declarent un travail SUR l'issue. Le mot-clé doit etre a
#: moins de 30 caracteres du numero : `Fix(secrets,#11044)` et `Part of #27338`
#: qualifies ; `Sur #27338` (une mention) ne l'est pas.
_MOTS_CANON = (r"closes|closed|close|fixes|fixed|fix|resolves|resolved|resolve"
                r"|see|part\s+of|part-of")
CANON_RE = re.compile(rf"(?i)\b(?:{_MOTS_CANON})[^#\n]{{0,30}}?#(\d+)\b")


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


def _note(service: dict[int, tuple[str, str]], numero: int, date: str | None,
          origine: str) -> None:
    """Garde la date de service la plus RECENTE d'un grain."""
    d = _dt(date)
    if d is None:
        return
    courant = service.get(int(numero))
    if courant is None or (_dt(courant[0]) or d) < d:
        service[int(numero)] = (_iso(d), origine)


def _chaine(par: dict[int, int | None], numero: int) -> list[int]:
    """Les ancetres d'un grain, du parent direct au plus haut hub."""
    chaine, vus, cur = [], {numero}, par.get(numero)
    while cur is not None and cur not in vus and len(chaine) < 8:
        chaine.append(cur)
        vus.add(cur)
        cur = par.get(cur)
    return chaine


def appliquer(etats_, cites_ouvertes: dict[int, list[dict]] | None = None,
              cites_merges: dict[int, list[dict]] | None = None) -> None:
    """Pose `cle_service` et `cle_origine` sur chaque etat.

    Les citations retenues sont les **canoniques** seules : une PR qui
    mentionne l'issue en prose ne la couvre pas. La date d'une PR est sa
    **creation** -- une correction d'une PR existante n'est pas un service
    nouveau.

    Le hub **suit** l'enfant : la cle d'un grain remonte a ses ancetres, et
    **seulement** a eux -- les freres, eux, gardent leur propre cle.
    """
    service: dict[int, tuple[str, str]] = {}
    for n, lst in (cites_merges or {}).items():
        for c in lst:
            if c.get("canonique"):
                _note(service, n, c.get("date"), "commit " + str(c.get("sha") or "")[:8])
    for n, lst in (cites_ouvertes or {}).items():
        for c in lst:
            if c.get("canonique"):
                _note(service, n, c.get("date"), "PR #" + str(c.get("pr") or ""))

    par = {e.numero: e.parent for e in etats_}
    numeros = sorted((e.numero for e in etats_),
                      key=lambda n: -len(_chaine(par, n)))
    for numero in numeros:
        s = service.get(numero)
        if not s:
            continue
        for ancetre in _chaine(par, numero):
            _note(service, ancetre, s[0], s[1] + " (enfant)")
    for e in etats_:
        s = service.get(e.numero)
        e.cle_service = s[0] if s else None
        e.cle_origine = s[1] if s else ""


def densites(etats_) -> dict[int, int]:
    """Le nombre d'enfants REELS d'un grain : une mesure, jamais un bonus.

    Elle se lit au moment de la visite du hub ; elle ne classe rien et ne
    declenche aucune creation de ticket.
    """
    d: dict[int, int] = {}
    for e in etats_:
        if e.parent:
            d[e.parent] = d.get(e.parent, 0) + 1
    return d
