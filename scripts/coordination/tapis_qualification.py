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

**fail-CLOSED.** Une decision qui n'a pas pu etre prise REFUSE le grain : un
fil illisible, un mur de lectures atteint, une echeance depassee -- le grain
porte alors son code de refus (`FIL_ILLISIBLE`, `MUR_EPUISE`, `ECHEANCE`) et
son motif, il n'est pas servi. Un grain non qualifie ne s'engage pas.

Ce que rend `qualifier` :

- `servis` : les grains servables, dans l'ordre donne ;
- `ecartees` : `{numero: {code, motif, fenetre_suffit}}` -- les exclusions
  **affichees**, jamais retirees en silence ; un code de lecture y figure
  aussi : le grain est REFUSE, pas decide ;
- `echecs` : les numeros illisibles (corps ou fil) ;
- `arrete` : le mur global a ete atteint ;
- `appels` : le nombre d'appels de la qualification ;
- `chrono` : `{secondes, premier_servable_s}` -- le temps jusqu'au **premier
  grain servable**, distinct de la latence du classement (celle du tirage,
  dans son propre rapport).

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
from coordination import gh_bulk, gh_selection, tapis_fenetre
from coordination import tapis_fil_complet, tapis_rapide
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
              horloge=time.monotonic, debut: float | None = None
              ) -> tuple[list, dict, list[int], bool, int, dict]:
    """Qualifie les candidats PRIS EN CHARGE, dans l'ordre donne.

    Rend `(servis, ecartees, echecs, arrete, appels, chrono)` -- le detail de
    chaque cle est dans le module : les exclusions portent leur code et leur
    motif, et `chrono` separe le temps jusqu'au **premier grain servable** de
    la latence du classement, qui est celle du tirage.
    """
    issues: dict[int, dict] = {}
    confirmes: dict[int, object] = {}
    ecartees: dict[int, dict] = {}
    echecs: list[int] = []
    exclus: set[int] = set()
    arrete = False
    appels = 0
    premier: float | None = None
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
                                      "motif": e.motif,
                                      "fenetre_suffit": tapis_fenetre.suffit(
                                          issues.get(e.numero))}
        retenus = [e for e in etats if e.ecart is None and e.numero not in exclus
                   and e.numero not in confirmes]
        if not retenus:
            continue
        conf, rejet, rates, n = tapis_fil_complet.confirmer(
            retenus, lec, lane, maintenant, jours, echeance, horloge)
        appels += n
        echecs.extend(rates)
        for e in conf:
            tapis_fenetre.noter(e, issues.get(e.numero))
            confirmes[e.numero] = e
            if premier is None and debut is not None:
                premier = horloge() - debut
        for r in rejet:
            exclus.add(r["numero"])
            ecartees[r["numero"]] = {**r, "fenetre_suffit": False}
    servis = [confirmes[n] for n in candidats if n in confirmes]
    chrono = {"secondes": round(horloge() - debut, 1) if debut is not None else None,
              "premier_servable_s": round(premier, 1) if premier is not None else None}
    return servis, ecartees, echecs, arrete, appels, chrono
