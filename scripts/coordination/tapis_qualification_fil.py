#!/usr/bin/env python3
"""La qualification d un grain PRIS EN CHARGE, cote CONSOMMATEUR.

Le consommateur (le claim) possede deja le FIL COMPLET de l issue : la
qualification se decide dessus, sans appel reseau, avec le MEME organe
que le tirage (`tapis_rapide.etats`). Ce module porte ce pas ;
l appelant (`scripts/check_lane_claim.py`) n en garde qu un shim.

Extrait de `scripts/check_lane_claim.py` (#27242) : le cliquet de taille des
scripts exige que le gros du bloc sorte du script de 8500 lignes.
"""
from __future__ import annotations

from datetime import UTC, datetime

#: Les regles de la qualification **decidables sur l'issue seule** (corps,
#: labels, fil complet) : le consommateur les rejoue avant tout claim. Les
#: regles qui dependent du POOL (MERGEE, COUVERTE, PLAFOND) restent au
#: tirage et a la qualification (`scripts/coordination/tapis_prise_en_charge.py`,
#: qui lit les citations de merge et les PRs ouvertes) ; RECLAMEE et LIVREE
#: sont deja decidees ici, en plus fin (override, scopes disjoints, etat de
#: la PR qui porte le DELIVERED -- mesuré : 14 tests de la grammaire
#: DELIVERED s'appuient sur ce comportement).
CODES_QUALIFICATION = ("HORSFLOTTE", "LABEL", "GEL", "RELACHEE")


def qualification_grain(payload: dict, my_lane: str,
                         now: datetime | None = None) -> tuple[str, str] | None:
    """La qualification du grain, cote CONSOMMATEUR : le code d'ecart decide
    sur le FIL COMPLET deja lu, ou None.

    Le **meme organe** que le tirage (`tapis_rapide.etats`) : la voie legere
    ne redecide pas, elle alimente la meme decision -- et le consommateur non
    plus. Aucun appel reseau : la lecture du fil complet a deja ete faite
    (`gh issue view --json comments` ou REST pagine), la decision se prend
    dessus.

    C'est ce qui rend la qualification **incontournable** avant l'action : un
    grain ecarte par la qualification ne peut etre ni reclame ni edite.
    """
    from coordination import gh_bulk, tapis_rapide  # import tardif : pas de cycle
    numero = payload.get("number")
    if numero is None:
        return None
    commentaires = [{"created_at": c.get("createdAt") or "",
                     "author": (c.get("author") or {}).get("login") or "",
                     "body": c.get("body") or ""}
                    for c in (payload.get("comments") or [])]
    labels = [(lb.get("name") or "") if isinstance(lb, dict) else str(lb)
              for lb in (payload.get("labels") or [])]
    moment = now or datetime.now(UTC)
    it = {"number": int(numero), "title": payload.get("title") or "",
          "body": payload.get("body") or "",
          "created_at": payload.get("createdAt") or "",
          "labels": labels, "comments_total": len(commentaires),
          "comments": commentaires}
    lec = gh_bulk.Lecture(issues=[it], prs=[], citations={},
                           lu_a=moment.isoformat(), secondes=0.0, appels=0)
    etats = tapis_rapide.etats(lec, my_lane, moment, 45)
    e = etats[0] if etats else None
    if e is not None and e.ecart and e.ecart in CODES_QUALIFICATION:
        return e.ecart, e.motif
    return None
