#!/usr/bin/env python3
"""Equilibrage des visites du tapis rapide (mandat user du 2026-11-16).

Verbatim : « Toute issue doit etre visitee au moins une fois avant qu'une
autre le soit deux fois, a l'exception de quelques issues anciennes de
consolidation qui peuvent recevoir plusieurs visites, et des marathon csharp
et Rust qui recevront le fruit du travail du nouveau harnais. Les issues
recentes en particulier ne devraient pas recevoir plus de visites que les
anciennes. »

Le tapis range les servables par **CLE DE SERVICE** (19/11, mandat
`20261119-picker-date-pr-parent`) : la date de la derniere PR qui **couvre**
le grain (`coordination.tapis_cle`), et, sans PR, la creation du grain. Le
departage a egalite est **uniforme** (le numero). Ni le nombre de visites, ni
le bonus d'age, ni le bonus de consolidation n'ordonnent plus : une voix par
issue.

Ce qui **reste** mesure : les visites se comptent en seances
(`coordination.tapis_seance`), et une livraison en ouvre une neuve (19/11) --
sans cela, sept livraisons d'une meme journee sur un umbrella n'y comptent
qu'une visite. Ces visites **informent** le rapport et l'organe d'equite du
dispatch (`coordination.belt_equite`) ; elles n'ordonnent plus.


L'equite du 16/11 tient dans la cle : une issue jamais servie porte la date de
sa **creation**, une issue servie porte la date de son dernier travail.

Une exception reste : les marathons de parite C# (#26070) et Rust (#26510) sortent
de l'equilibrage : c'est le harnais sk-agent qui les servira.
"""
from __future__ import annotations

import hashlib
import math
import re
from datetime import datetime, timedelta

from coordination import tapis_avantages, tapis_seance
from coordination.tapis_marqueurs import FERME, VISITE, Evt, _dt, _iso

FENETRE_J = 7  # le tour : un tour de flotte complet mesure en 4 a 8 jours (16/11)
SEANCE_H = tapis_seance.SEANCE_H
MARATHONS = frozenset({26070, 26510})  # racines : parite C# (Marathon II), parite Rust
TETE = 24  # tete de niveau decalee par lane, pour que deux lanes divergent
_MARATHON_RE = re.compile(r"^\s*\[?\s*marathon\b", re.IGNORECASE)


def compter(evts: list[Evt], citations: list[dict],
            maintenant: datetime) -> tuple[str | None, int, int]:
    """La derniere visite (ISO), les visites au total, celles du tour.

    Les citations des PRs **ouvertes** (marquees `ouvert`) comptent UNE
    visite chacune : elles ne sont pas encore mergees, elles ne se fondent
    donc pas dans les seances de commits.
    """
    par_lane: dict[str, list[Evt]] = {}
    visites: list[datetime] = []
    for ev in evts:
        if ev.marque in VISITE:
            visites.append(ev.quand)
            par_lane.setdefault(ev.lane or "?", []).append(ev)
        elif ev.marque in FERME:
            par_lane.setdefault(ev.lane or "?", []).append(ev)
    cites = list(citations)
    en_cours = [d for c in cites if c.get("ouvert") and (d := _dt(c.get("date")))]
    commits = [d for c in cites if not c.get("ouvert") and (d := _dt(c.get("date")))]
    tous = visites + commits + en_cours

    def compte(depuis: datetime | None) -> int:
        marques = sum(tapis_seance.par_lane(evs, depuis) for evs in par_lane.values())
        fen = [d for d in en_cours if depuis is None or d >= depuis]
        return (max(marques, tapis_seance.par_instants(commits, depuis))
                + len(fen))

    return ((_iso(max(tous)) if tous else None), compte(None),
            compte(maintenant - timedelta(days=FENETRE_J)))


def est_marathon(e) -> bool:
    return e.famille in MARATHONS or e.numero in MARATHONS or bool(_MARATHON_RE.match(e.titre))


def familles_consolidation(etats_) -> set[int]:
    """Les numeros labellises consolidation : une famille l'est par sa racine."""
    return {e.numero for e in etats_ if e.consolidation}


def niveau(e, conso: set[int], maintenant: datetime) -> float:
    """Le niveau de service : les visites du tour moins le bonus leger.

    Il **ne classe plus** (mandat du 19/11 : une voix par issue, la cle de
    service). Il reste une MESURE, pour l'observation -- et l'equite du 16/11
    se lit desormais dans la cle, pas dans le niveau."""
    if est_marathon(e):
        return math.inf
    return e.visites - tapis_avantages.bonus(e, conso, maintenant)[0]


def raisons(e, conso: set[int], maintenant: datetime,
            densite: int | None = None) -> list[str]:
    """Ce que le rapport dit du rang d'un grain.

    Depuis le 19/11, le rang ne se lit plus dans un **niveau** (visites moins
    bonus) : il se lit dans la **cle de service**. Le nombre de visites
    reste informe ; le bonus n'est plus une priorite et n'est donc plus annonce.

    La **densite** (nombre d'enfants REELS d'un hub) est annoncee quand elle
    existe : elle se LIT au moment de la visite du hub -- elle ne classe
    rien, et ne declenche aucune creation de ticket.
    """
    if est_marathon(e):
        return ["marathon : hors equilibrage (harnais sk-agent)"]
    r = [f"{e.visites} visite(s) en {FENETRE_J} j ({e.visites_total} au total)"]
    if e.cle_service:
        r.append(f"cle de service : {e.cle_service} ({e.cle_origine})")
    else:
        r.append(f"cle de service : aucune PR -- creation {e.cree_le}")
    if densite:
        r.append(f"densite : {densite} enfant(s) reel(s)")
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
    """Cle de service croissante, departage **uniforme** a egalite.

    Mandat du 19/11 (`20261119-picker-date-pr-parent`) : une voix par issue.
    Ni le nombre de visites, ni le bonus d'age, ni le bonus de consolidation
    n'ordonnent plus le tirage -- la cle est la date de la derniere PR qui
    **couvre** le grain (`coordination.tapis_cle`), et, sans PR, la creation
    du grain. Le hub suit son enfant ; ses freres ne bougent pas.

    `rotation=False` : l'ordre **fair**, sans rotation de tete par lane
    (la fenetre qui avance decide de la rotation, pas le pool)."""

    def cle(e):
        return (e.cle_service or e.cree_le or "", e.numero)

    tour = sorted((e for e in servables if not est_marathon(e)), key=cle)
    tour += [e for e in servables if est_marathon(e)]
    return _decaler(tour, graine, cle(tour[0])[0]) if rotation and tour else tour
