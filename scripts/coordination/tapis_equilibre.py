#!/usr/bin/env python3
"""Equilibrage des visites du tapis rapide (mandat user du 2026-11-16).

Verbatim : « Toute issue doit etre visitee au moins une fois avant qu'une autre
le soit deux fois, a l'exception de quelques issues anciennes de consolidation
qui peuvent recevoir plusieurs visites, et des marathon csharp et Rust qui
recevront le fruit du travail du nouveau harnais. Les issues recentes en
particulier ne devraient pas recevoir plus de visites que les anciennes. »

Le tapis range les servables par NIVEAU, le nombre de visites recues dans les
`FENETRE_J` derniers jours : c'est le « tour » de la regle. La mesure du
16/11 (395 issues ouvertes, environ 47 seances par jour) donne un tour complet
en 4 a 8 jours. Un compte sur toute la vie de l'issue aurait l'effet inverse
du mandat : les anciennes en ont plus parce qu'elles vivent plus longtemps.
Dans un niveau, l'issue jamais visitee passe d'abord, puis la plus ancienne.

Les priorites LEGERES du mandat du 2026-11-18 (age, consolidation) sont dans
`coordination/tapis_avantages.py` ; leur total reste sous une visite (l'equite
du 16/11 tient : 0 visite avant 1 visite) et la consolidation passe DEVANT
l'anciennete (invariant I7, #28114) ; les marathons de parite C# (#26070) et
Rust (#26510) sortent de l'equilibrage : le harnais sk-agent les servira.

Une visite est une SEANCE : les marqueurs VISITE (CLAIMED, CLAIMED-AMEND,
DELIVERED) d'une meme lane a moins de `SEANCE_H` heures n'en font qu'une --
et **une livraison en ouvre une neuve** (19/11, #27338). Les seances des
marqueurs sont celles de `tapis_seance.py` (`par_lane`), celles des citations
celles de `tapis_dernier_grain.seances`. Le **classement** ne compte que les
prises en charge nominatives (un **grain**) : une citation Git n'est pas une
visite ; `compter` garde le compte historique pour la seule **voie legere**.
Fonctions pures, sans reseau. Doc : docs/reference/tapis-rapide.md.
"""
from __future__ import annotations

import hashlib
import math
import re
from datetime import datetime, timedelta

from coordination import tapis_avantages, tapis_seance
from coordination.tapis_marqueurs import FERME, VISITE, Evt, _dt, _iso
from coordination.tapis_dernier_grain import cle_tri, seances

FENETRE_J = 7  # le tour : un tour de flotte complet mesure en 4 a 8 jours (16/11)
MARATHONS = frozenset({26070, 26510})  # racines : parite C# (Marathon II), parite Rust
TETE = 24  # tete de niveau decalee par lane, pour que deux lanes divergent
_MARATHON_RE = re.compile(r"^\s*\[?\s*marathon\b", re.IGNORECASE)


def compter(evts: list[Evt], citations: list[dict],
            maintenant: datetime) -> tuple[str | None, int, int]:
    """La derniere visite (ISO), les visites au total, celles du tour.

    Le compte **historique** de la **voie legere** (elle ne lit pas le fil) :
    marqueurs et citations, le plus grand des deux ; le classement lui passe
    par `tapis_dernier_grain.compter_grains` (les grains seuls). Les seances
    des marqueurs suivent `tapis_seance.par_lane` (une livraison en ouvre une
    neuve, #27338), celles des citations `seances` ; les citations des PRs
    **ouvertes** comptent UNE visite chacune (elles ne sont pas mergees).
    """
    par_lane: dict[str, list[Evt]] = {}
    visites: list[datetime] = []
    for ev in evts:
        if ev.marque in VISITE:
            visites.append(ev.quand)
            par_lane.setdefault(ev.lane or "?", []).append(ev)
        elif ev.marque in FERME:
            par_lane.setdefault(ev.lane or "?", []).append(ev)
    en_cours = [d for c in citations if c.get("ouvert") and (d := _dt(c.get("date")))]
    commits = [d for c in citations if not c.get("ouvert") and (d := _dt(c.get("date")))]
    tous = visites + commits + en_cours

    def compte(depuis: datetime | None) -> int:
        marques = sum(tapis_seance.par_lane(evs, depuis) for evs in par_lane.values())
        fen = [d for d in en_cours if depuis is None or d >= depuis]
        return max(marques, seances(commits, depuis)) + len(fen)

    return ((_iso(max(tous)) if tous else None), compte(None),
            compte(maintenant - timedelta(days=FENETRE_J)))


def est_marathon(e) -> bool:
    return e.famille in MARATHONS or e.numero in MARATHONS or bool(_MARATHON_RE.match(e.titre))


def familles_consolidation(etats_) -> set[int]:
    """Les numeros labellises consolidation : une famille l'est par sa racine."""
    return {e.numero for e in etats_ if e.consolidation}


def bonus(e, conso: set[int], maintenant: datetime) -> tuple[float, list[str]]:
    """Le bonus leger du mandat du 18/11 : la consolidation, puis l'age.

    Deux contributions PETITES et DISTINCTES, comptees en dixiemes de visite :
    le niveau reste un multiple de 0,1, les issues se regroupent par niveau
    (c'est ce qui fait tourner la tete d'une lane a l'autre), et l'equite du
    16/11 tient : 0 visite avant 1 visite. La consolidation est posee EN
    PREMIER (I7) : elle passe devant l'anciennete."""
    dix, motifs = tapis_avantages.bonus_dixiemes(
        tapis_avantages.age_jours(e.cree_le, maintenant),
        tapis_avantages.est_consolidation(e.consolidation, e.famille, conso))
    return dix / 10, motifs


def niveau(e, conso: set[int], maintenant: datetime) -> float:
    """Le niveau de service : les visites du tour moins le bonus leger.

    Plus petit niveau d'abord : 0 visite passe devant 1 visite (le bonus total
    est borne a 0,9), et la consolidation puis l'age font les departages."""
    if est_marathon(e):
        return math.inf
    return e.visites - bonus(e, conso, maintenant)[0]


def raisons(e, conso: set[int], maintenant: datetime) -> list[str]:
    """Ce que le rapport dit du rang d'un grain."""
    if est_marathon(e):
        return ["marathon : hors equilibrage (harnais sk-agent)"]
    r = [f"{e.visites} visite(s) en {FENETRE_J} j ({e.visites_total} au total)"]
    r.extend(bonus(e, conso, maintenant)[1])
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


def ordre(etats_, servables, graine: str, maintenant: datetime,
          rotation: bool = True) -> list:
    """Niveau croissant ; dans un niveau, la jamais visitee puis la plus
    ancienne d'abord, les familles servies a tour de role.

    `rotation=False` : l'ordre **fair**, sans rotation de tete par lane
    (la fenetre qui avance decide de la rotation, pas le pool)."""
    conso = familles_consolidation(etats_)
    niveaux: dict[float, dict[int, list]] = {}
    for e in sorted(servables, key=cle_tri):
        niveaux.setdefault(niveau(e, conso, maintenant), {}).setdefault(e.famille, []).append(e)
    tour: list = []
    for n in sorted(niveaux):
        listes, rr, rang = list(niveaux[n].values()), [], 0
        while any(rang < len(lst) for lst in listes):
            rr.extend(lst[rang] for lst in listes if rang < len(lst))
            rang += 1
        tour += _decaler(rr, graine, n) if rotation else rr
    return tour
