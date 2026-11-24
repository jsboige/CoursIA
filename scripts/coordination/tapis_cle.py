#!/usr/bin/env python3
"""La CLE DE SERVICE d'un grain : la date de la derniere PR qui le COUVRE.

Mandat du coordinateur (19/11/2026) : « Remplacer poids/bonus/seances par une
voix par issue, ordre de la derniere PR dont le diff couvre le grain,
departage uniforme a egalite ; sans PR, vieillissement depuis la creation (pas
d'anciennete heritee). Une PR enfant remet aussi le hub en queue, pas les
freres ; pas de nouveau service sur correction de PR existante. »

Ce module tient la CLE : une date par grain, et sa source.

- le **candidat** : un lien canonique (`See #N`, `Closes #N`,
  `Fix(portee,#N)`) porte par le corps d'une PR -- `coordination.tapis_canon`
  ; le lien se lit dans le corps, jamais dans un titre ni dans une mention en
  prose ;
- la **date** : celle de la PR candidate la plus RECENTE ; a defaut, la
  **creation** du grain (mandat : « sans PR, vieillissement depuis la
  creation »).

Le hub **suit son enfant** : une PR qui couvre un enfant couvre aussi le hub,
et **seulement** lui -- les freres gardent leur propre cle.

La cle **ne classe pas seule** : elle est le **departage a niveau egal**. La
classe -- le niveau de visite -- reste le premier critere, parce que
l'invariant de couverture du 16/11 (#27590) est merge et execute : une issue
jamais servie ne cede jamais sa place a une issue deja servie. La variante
« cle primaire » rend ce modele impossible (deux tests de propriete de
`scripts/tests/test_visit_coverage.py` echouent) ; le detail est dans le body
de la PR #27393.

Doc : docs/reference/tapis-rapide.md.
"""
from __future__ import annotations

from coordination.tapis_canon import des_prs_canoniques
from coordination.tapis_marqueurs import _dt, _iso


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


def candidats(lecture) -> dict[int, tuple[str, str]]:
    """La date de service CANDIDATE de chaque grain : (date, origine).

    Deux sources : les **commits merges** qui citent l'issue (le corps du
    squash porte le body de la PR) et les **PRs ouvertes** qui la couvrent.
    Seuls les liens **canoniques** comptent (`coordination.tapis_canon`).
    """
    service: dict[int, tuple[str, str]] = {}
    for n, lst in (getattr(lecture, "citations", None) or {}).items():
        for c in lst:
            if c.get("canonique"):
                _note(service, n, c.get("date"),
                      "commit " + str(c.get("sha") or "")[:8])
    for n, lst in des_prs_canoniques(getattr(lecture, "prs", None)).items():
        for c in lst:
            _note(service, n, c.get("date"), "PR #" + str(c.get("pr") or ""))
    return service


def appliquer(etats_, lecture) -> None:
    """Pose `cle_service` et `cle_origine` sur chaque etat.

    Le hub suit l'enfant : la cle d'un grain remonte a ses ancetres, et
    **seulement** a eux. Un grain sans PR candidate garde une cle **vide** :
    c'est la creation qui fait alors son anciennete.
    """
    par = {e.numero: e.parent for e in etats_}
    service = candidats(lecture)
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
        e.cle_service = s[0] if s else ""
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
