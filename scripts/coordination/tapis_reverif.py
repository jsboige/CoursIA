#!/usr/bin/env python3
"""Re-decision des grains servis au fil tronque, sur le fil complet (#27179).

La lecture groupee ne voit que les 12 derniers commentaires d'une issue
(``gh_bulk.QUERY``) : sur le pool du 18/11, 180 issues ouvertes sur 426 ont un
fil tronque, et le marqueur qui ecarte un grain ([RELEASED], [FROZEN],
[DELIVERED] sans paths, visite de plafond) peut etre plus vieux que la fenetre
-- temoin #26534, servi 2,1 j apres son [RELEASED]. Ce module re-decide LES
GRAINS SERVIS dont le fil est tronque, au moment du service : leur fil complet
est relu par l'organe deja present (REST pagine de ``gh_snapshot``, pas un
second lecteur) et le meme ``_decider`` est rejoue ; si un ecart apparait, le
grain sort de la liste et son remplacant entre, lui-meme re-verifie. Le tapis
PROPOSE toujours : cette passe reduit les grains servis a rebuter, elle ne
remplace pas ``check_lane_claim.py`` avant edition.
"""
from __future__ import annotations

import time
from collections.abc import Callable
from datetime import datetime

from coordination import gh_bulk, gh_snapshot
from coordination.tapis_marqueurs import evenements

#: Lecture du fil complet d'une issue, deja adaptee a la forme des marqueurs
#: (``created_at``/``body``, celle de ``gh_bulk._issue``).
LireFils = Callable[[int], list[dict]]
#: Borne d'appels REST de la passe : les grains servis plus leurs remplacants.
APPELS_MAX = 16


def lire_defaut(numero: int) -> list[dict]:
    """Le fil complet d'une issue par l'organe deja present, adapte en forme
    de marqueurs : le lecteur rend ``createdAt``, les marqueurs lisent
    ``created_at``."""
    return [{"created_at": c.get("createdAt") or "",
             "author": (c.get("author") or {}).get("login") or "",
             "body": c.get("body") or ""}
            for c in gh_snapshot.fetch_issue_comments(gh_bulk.DEPOT_GH, numero)]


def _tronque(it: dict) -> bool:
    return (it.get("comments_total") or 0) > len(it.get("comments") or [])


def _redecrire(e, ouvertes: dict, parents: dict, ctx: dict,
               comments: list[dict], tapis_rapide) -> str | None:
    """Re-joue ``_decider`` sur le fil complet ; le code de l'ecart apparu."""
    it = {**ouvertes[e.numero], "comments": comments,
          "comments_total": len(comments)}
    e.notes = [n for n in e.notes if not n.startswith("fil partiel")]
    tapis_rapide._decider(e, it, evenements(comments),
                          tapis_rapide._ancetres(e.numero, parents)[0], ctx)
    if e.ecart is None:
        e.notes.append(f"fil complet relu ({len(comments)} commentaires)")
    return e.ecart


def passer(tous: list, file: list, nb_grains: int, lane: str,
           maintenant: datetime, jours: int, graine: str,
           lecture: gh_bulk.Lecture, lire: LireFils | None = None,
           appels_max: int = APPELS_MAX) -> tuple[list, dict]:
    """Re-decide sur fil complet les grains servis au fil tronque (#27179).

    Retourne ``(file finale, stats)``. Pure hors ``lire`` : la re-decision
    rejoue ``tapis_rapide._decider`` sur une issue dont les commentaires sont
    le fil complet ; un fil illisible laisse le grain servi (fail-OPEN, la
    note « fil partiel » reste), le tapis ne fait pas autorite.
    """
    from coordination import tapis_rapide  # tardif : tapis_rapide nous importe au main

    lire = lire or lire_defaut
    ouvertes, parents, _, ctx = tapis_rapide._contexte(lecture, lane,
                                                       maintenant, jours)
    fils: dict[int, list[dict] | None] = {}  # numero -> fil complet (None : illisible)
    jetes: list[dict] = []
    echecs: list[int] = []
    appels, borne = 0, False
    debut = time.monotonic()
    while True:
        cibles = [e for e in file if e.numero not in fils
                  and _tronque(ouvertes.get(e.numero) or {})]
        if not cibles:
            break
        if appels >= appels_max:
            borne = True  # la fenetre reste la fenetre pour les non relus
            break
        for e in cibles:
            if appels >= appels_max:
                borne = True
                break
            try:
                fils[e.numero] = lire(e.numero)
            except Exception:  # un fil illisible ne bloque pas le tirage
                fils[e.numero] = None
                echecs.append(e.numero)
            appels += 1
        deja = len(jetes)
        for e in cibles:
            if fils.get(e.numero):
                code = _redecrire(e, ouvertes, parents, ctx, fils[e.numero],
                                  tapis_rapide)
                if code is not None:
                    jetes.append({"numero": e.numero, "code": code,
                                  "motif": e.motif})
        if len(jetes) == deja:
            break  # file stable : les verifies sont tous restes servables
        file = tapis_rapide.ordonner(tous, lane, maintenant, nb_grains, graine)
    stats = {"appels": appels, "secondes": round(time.monotonic() - debut, 1),
             "jetes": jetes, "echecs": echecs, "borne": borne}
    return file, stats
