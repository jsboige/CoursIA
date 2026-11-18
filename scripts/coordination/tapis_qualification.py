#!/usr/bin/env python3
"""La QUALIFICATION d'un grain PRIS EN CHARGE : le corps, le fil complet, sa decision.

C'est le temps d'**action** du tapis : le tirage propose un ordre sur toutes les
issues ouvertes (rotation universelle, metadonnees seules, `coordination.tapis_leger`),
et la lane qualifie le grain qu'elle engage a prendre, avant de le reclamer.

La qualification lit :

- le **corps** de l'issue (une lecture ciblee, une requete par lot) ;
- son **fil complet**, par l'organe REST `gh_snapshot` (pagination complete) --
  jamais la fenetre des 12 derniers commentaires de la lecture groupee, qui peut
  cacher le marqueur qui ecarte un grain (constat de #27179) ;
- et rejoue les **neuf regles d'ecart** de `tapis_rapide.etats` : la voie legere
  ne redecide pas, elle alimente la meme decision.

Usage (prise en charge d'un grain) :

    python scripts/coordination/tapis_qualification.py --issue 17397

Usage (prise en charge d'une file, le premier servable gagne) :

    python scripts/coordination/tapis_qualification.py --issues 17397 27241 17545
"""
from __future__ import annotations

import sys
import time
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk, gh_selection, tapis_fil_complet, tapis_rapide
from coordination.tapis_marqueurs import _iso

#: Candidats par lot de lecture (une requete GraphQL pour le lot).
LOT = 50


def _lec(issues: list[dict], prs: list[dict], citations: dict,
         maintenant: datetime, appels: int = 0) -> gh_bulk.Lecture:
    """La lecture des seuls candidats qualifies : c'est elle qui est rejouee
    par `tapis_rapide.etats` (les neuf regles d'ecart)."""
    return gh_bulk.Lecture(issues=issues, prs=prs, citations=citations,
                           lu_a=_iso(maintenant), secondes=0.0, appels=appels)


def _fenetre(candidats: list[int], run, issues: dict[int, dict],
             echecs: list[int]) -> int:
    """Lit le corps et la fenetre des candidats (un lot GraphQL), et les ajoute
    au contexte. Rend le nombre de lots lus."""
    if not candidats:
        return 0
    try:
        lus = gh_selection.qualifier(run, gh_bulk.DEPOT_GH, candidats)
    except gh_bulk.LectureIncomplete:
        echecs.extend(candidats)
        return 0
    issues.update(lus)
    return 1


def qualifier(candidats: list[int], lane: str, maintenant: datetime, jours: int,
              prs: list[dict], citations: dict, run,
              echeance: float | None = None, lot: int = LOT,
              horloge=time.monotonic) -> tuple[list, dict, list[int], bool, int]:
    """Qualifie les candidats PRIS EN CHARGE, dans l'ordre donne.

    Rend `(servis, ecartees, echecs, arrete, appels)` :

    - `servis` : les grains servables, dans l'ordre donne ;
    - `ecartees` : `{numero: {code, motif}}` -- les exclusions **affichees**,
      jamais retirees en silence ;
    - `echecs` : les numeros illisibles (corps ou fil) ;
    - `arrete` : le mur global a ete atteint ;
    - `appels` : le nombre d'appels de la qualification.
    """
    issues: dict[int, dict] = {}
    confirmes: dict[int, object] = {}
    ecartees: dict[int, dict] = {}
    echecs: list[int] = []
    exclus: set[int] = set()
    arrete = False
    appels = 0
    i = 0
    while i < len(candidats):
        if echeance is not None and horloge() > echeance:
            arrete = True
            break
        tranche = candidats[i:i + lot]
        i += lot
        appels += _fenetre(tranche, run, issues, echecs)
        lec = _lec(list(issues.values()), prs, citations, maintenant, appels)
        etats = tapis_rapide.etats(lec, lane, maintenant, jours)
        for e in etats:
            if e.ecart and e.numero not in ecartees:
                ecartees[e.numero] = {"numero": e.numero, "code": e.ecart,
                                      "motif": e.motif}
        retenus = [e for e in etats if e.ecart is None and e.numero not in exclus
                   and e.numero not in confirmes]
        if not retenus:
            continue
        conf, rejet, rates, n = tapis_fil_complet.confirmer(
            retenus, lec, lane, maintenant, jours, echeance, horloge)
        appels += n
        echecs.extend(rates)
        for e in conf:
            confirmes[e.numero] = e
        for r in rejet:
            exclus.add(r["numero"])
            ecartees[r["numero"]] = r
    servis = [confirmes[n] for n in candidats if n in confirmes]
    return servis, ecartees, echecs, arrete, appels
