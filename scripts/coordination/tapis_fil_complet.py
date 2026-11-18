#!/usr/bin/env python3
"""Le FIL COMPLET des candidats retenus : lever le doute de la fenetre.

La lecture groupee ne voit que les 12 derniers commentaires : le marqueur qui
ecarte un grain peut etre plus ancien que la fenetre (constat de #27179, qui
a produit l'organe `tapis_reverif`). Le fil complet est donc relu -- par
l'organe REST `gh_snapshot` -- pour les **seuls** candidats que la fenetre
RETIENT, et la decision est rejouee (`tapis_rapide._decider`, comme
`tapis_reverif`).

C'est la separation demandee : la rotation universelle est legere (metadonnees
seules), la lecture complete n'intervient qu'**avant l'action**, sur le grain
que la lane engage a prendre.

Mesure du 2026-11-18 (pool de 440 issues) : relire le fil complet de TOUS les
candidats coute 1 appel REST par candidat (48 appels, 59 s) ; relire d'abord
la fenetre en un lot GraphQL (1 appel pour 50 candidats) et ne relire le fil
complet que des candidats **retenus** coute 1 appel REST par candidat retenu.

Un fil illisible laisse le candidat servi (fail-OPEN : le tapis propose, il ne
fait pas autorite) ; le mur global arrete la lecture et le dit.
"""
from __future__ import annotations

import time
from datetime import datetime
from pathlib import Path

import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk, gh_snapshot, tapis_rapide, tapis_reverif

#: Borne des lectures REST du fil complet (les candidats retenus).
APPELS_MAX = 16


def _fil(numero: int, repo: str = gh_bulk.DEPOT_GH) -> list[dict]:
    """Le fil complet de l'issue, dans la forme des marqueurs.

    L'organe `gh_snapshot` pagine en REST : c'est le **fil complet**, pas la
    fenetre des 12 derniers commentaires de la lecture groupee.
    """
    return [{"created_at": c.get("createdAt") or "",
             "author": (c.get("author") or {}).get("login") or "",
             "body": c.get("body") or ""}
            for c in gh_snapshot.fetch_issue_comments(repo, numero)]


def confirmer(retenus: list, lecture, lane: str, maintenant: datetime, jours: int,
              echeance: float | None = None, horloge=time.monotonic,
              appels_max: int = APPELS_MAX) -> tuple[list, list, list[int], int]:
    """Re-decide sur le fil complet les candidats RETENUS par la fenetre.

    Rend `(confirmes, rejetes, echecs, appels)`. Un candidat dont la fenetre
    EST le fil complet (moins de 12 commentaires) est confirme sans appel :
    il n'y a rien a lever.
    """
    ouvertes, parents, _, ctx = tapis_rapide._contexte(lecture, lane,
                                                       maintenant, jours)
    confirmes, rejetes, echecs, appels = [], [], [], 0
    for e in retenus:
        it = ouvertes.get(e.numero) or {}
        lus = len(it.get("comments") or [])
        if (it.get("comments_total") or 0) <= lus:
            confirmes.append(e)
            continue
        if appels >= appels_max or (echeance is not None and horloge() > echeance):
            confirmes.append(e)
            continue
        try:
            fil = _fil(e.numero)
        except Exception:  # noqa: BLE001 - un fil illisible ne bloque pas le tirage
            echecs.append(e.numero)
            confirmes.append(e)
            continue
        appels += 1
        code = tapis_reverif._redecrire(e, ouvertes, parents, ctx, fil,
                                         tapis_rapide)
        if code is None:
            confirmes.append(e)
        else:
            rejetes.append({"numero": e.numero, "code": code, "motif": e.motif})
    return confirmes, rejetes, echecs, appels
