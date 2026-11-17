#!/usr/bin/env python3
"""Equilibrage des visites du tapis rapide (mandat user du 2026-11-16).

Verbatim : « Toute issue doit etre visitee au moins une fois avant qu'une
autre le soit deux fois, a l'exception de quelques issues anciennes de
consolidation qui peuvent recevoir plusieurs visites, et des marathon csharp
et Rust qui recevront le fruit du travail du nouveau harnais. Les issues
recentes en particulier ne devraient pas recevoir plus de visites que les
anciennes. »

Le tapis range les servables par NIVEAU, le nombre de visites recues dans les
`FENETRE_J` derniers jours : c'est le « tour » de la regle. La mesure du
16/11 (395 issues ouvertes, environ 47 seances par jour) donne un tour
complet en 4 a 8 jours. Un compte sur toute la vie de l'issue aurait l'effet
inverse du mandat : les anciennes en ont plus parce qu'elles vivent plus
longtemps (1,1 visite en moyenne avant 7 jours, 6,2 entre 30 et 90 jours), et
un niveau strict sur ce compte les affamerait. Dans un niveau, l'issue jamais
visitee passe d'abord, puis la plus ancienne : une issue recente recoit sa
premiere visite, puis attend que les anciennes aient recu la leur.

Deux exceptions, celles du mandat :

- une issue de consolidation (label, ou racine de famille labellisee) ouverte
  depuis plus de `AGE_CONSOLIDATION_J` jours a pour niveau
  `visites // VISITES_CONSOLIDATION` : elle recoit plusieurs visites par tour ;
- les marathons de parite C# (#26070, titres « Marathon ») et Rust (#26510)
  sortent de l'equilibrage et passent apres le pool equilibre : c'est le
  harnais sk-agent qui les servira.

Une visite est une SEANCE : les marqueurs VISITE (CLAIMED, CLAIMED-AMEND,
DELIVERED) d'une meme lane a moins de `SEANCE_H` heures d'intervalle n'en font
qu'une. Les commits de `origin/main` qui citent l'issue forment des seances
sans lane ; le compte retenu est le plus grand des deux (un claim puis le merge
de sa PR comptent une fois). Fonctions pures, sans reseau. Doc :
docs/reference/tapis-rapide.md, section « L'ordre : l'equilibrage des visites ».
"""
from __future__ import annotations

import hashlib
import math
import re
from datetime import datetime, timedelta

from coordination.tapis_marqueurs import VISITE, Evt, _dt, _iso

FENETRE_J = 7  # le tour : un tour de flotte complet mesure en 4 a 8 jours (16/11)
AGE_CONSOLIDATION_J = 60
VISITES_CONSOLIDATION = 3
SEANCE_H = 24
MARATHONS = frozenset({26070, 26510})  # racines : parite C# (Marathon II), parite Rust
TETE = 24  # tete de niveau decalee par lane, pour que deux lanes divergent
_MARATHON_RE = re.compile(r"^\s*\[?\s*marathon\b", re.IGNORECASE)


def _seances(instants: list[datetime], depuis: datetime | None = None) -> int:
    """Le nombre de seances : un ecart de plus de SEANCE_H en ouvre une neuve."""
    n, avant = 0, None
    for t in sorted(t for t in instants if depuis is None or t >= depuis):
        if avant is None or t - avant > timedelta(hours=SEANCE_H):
            n += 1
        avant = t
    return n


def compter(evts: list[Evt], citations: list[dict],
            maintenant: datetime) -> tuple[str | None, int, int]:
    """La derniere visite (ISO), les visites au total, celles du tour."""
    par_lane: dict[str, list[datetime]] = {}
    for ev in evts:
        if ev.marque in VISITE:
            par_lane.setdefault(ev.lane or "?", []).append(ev.quand)
    commits = [d for c in citations if (d := _dt(c.get("date")))]
    tous = [t for ts in par_lane.values() for t in ts] + commits

    def compte(depuis: datetime | None) -> int:
        marques = sum(_seances(ts, depuis) for ts in par_lane.values())
        return max(marques, _seances(commits, depuis))

    return ((_iso(max(tous)) if tous else None), compte(None),
            compte(maintenant - timedelta(days=FENETRE_J)))


def est_marathon(e) -> bool:
    return e.famille in MARATHONS or e.numero in MARATHONS or bool(_MARATHON_RE.match(e.titre))


def familles_consolidation(etats_) -> set[int]:
    """Les numeros labellises consolidation : une famille l'est par sa racine."""
    return {e.numero for e in etats_ if e.consolidation}


def _vieille_consolidation(e, conso: set[int], maintenant: datetime) -> bool:
    cree = _dt(e.cree_le)
    return bool((e.consolidation or e.famille in conso) and cree
                and maintenant - cree > timedelta(days=AGE_CONSOLIDATION_J))


def niveau(e, conso: set[int], maintenant: datetime) -> float:
    """Le niveau de service : les marathons hors equilibrage, au fond."""
    if est_marathon(e):
        return math.inf
    if _vieille_consolidation(e, conso, maintenant):
        return e.visites // VISITES_CONSOLIDATION
    return e.visites


def raisons(e, conso: set[int], maintenant: datetime) -> list[str]:
    """Ce que le rapport dit du rang d'un grain."""
    if est_marathon(e):
        return ["marathon : hors equilibrage (harnais sk-agent)"]
    r = [f"{e.visites} visite(s) en {FENETRE_J} j ({e.visites_total} au total)"]
    if _vieille_consolidation(e, conso, maintenant):
        r.append(f"consolidation ancienne : niveau {int(niveau(e, conso, maintenant))}")
    return r


def _decaler(tour: list, graine: str, cle: float) -> list:
    """Les grains de la tete d'un niveau tournent d'un rang propre a la lane.

    Le decalage porte sur les grains seuls : un conteneur garde sa place, que
    le quota de conteneurs de `ordonner` lit dans l'ordre. Il est deterministe
    pour (graine, niveau) : une lane retrouve sa liste dans sa tranche.
    """
    tete = list(tour[:TETE])
    pos = [i for i, e in enumerate(tete) if not e.conteneur]
    if len(pos) < 2:
        return tour
    h = hashlib.sha256(f"{graine}|{cle}|decalage".encode()).digest()
    k = int.from_bytes(h[:8], "big") % len(pos)
    grains = [tete[i] for i in pos]
    for i, e in zip(pos, grains[k:] + grains[:k], strict=True):
        tete[i] = e
    return tete + list(tour[TETE:])


def ordre(etats_, servables, graine: str, maintenant: datetime) -> list:
    """Niveau croissant ; dans un niveau, la jamais visitee puis la plus
    ancienne d'abord, les familles servies a tour de role."""
    conso = familles_consolidation(etats_)
    niveaux: dict[float, dict[int, list]] = {}
    for e in sorted(servables, key=lambda e: (e.visites_total > 0, e.cree_le,
                                             e.derniere_visite or "", e.numero)):
        niveaux.setdefault(niveau(e, conso, maintenant), {}).setdefault(e.famille, []).append(e)
    tour: list = []
    for n in sorted(niveaux):
        listes, rr, rang = list(niveaux[n].values()), [], 0
        while any(rang < len(lst) for lst in listes):
            rr.extend(lst[rang] for lst in listes if rang < len(lst))
            rang += 1
        tour += _decaler(rr, graine, n)
    return tour
