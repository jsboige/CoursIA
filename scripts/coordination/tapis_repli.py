#!/usr/bin/env python3
"""Le REPLI CHRONOLOGIQUE du tirage : hors reseau, le cache local fait foi.

L'invariant I2 du contrat du picker (#28114) : « un repli chronologique ».
Hors reseau, la voie legere (`tapis_leger`) ne rend **rien** -- la lecture de
selection echoue et le point d'entree sort en 3. Ce module rend la main : il
lit le **cache** local -- le meme fichier que le tirage rapide
(`lecture-<N>j.json`) -- et sert le pool dans l'**ordre de creation**.

Le cache peut etre **perime** : c'est la panne du reseau qui le rend seul
disponible, et un pool d'il y a quelques heures vaut mieux qu'un tirage vide.
Au-dela de `TTL_S`, il ne vaut plus rien : le repli rend alors l'echec de
lecture, comme avant ce module.

Le **curseur** du repli est persiste dans le dossier du cache : sans lui,
chaque tour rendrait les memes grains et le pool ne serait jamais couvert.
"""
from __future__ import annotations

import json
import os
import tempfile
from datetime import datetime
from pathlib import Path

from coordination import (
    gh_bulk,
    gh_selection,
    tapis_age,
    tapis_ancre,
    tapis_occupation,
    tapis_origami,
    tapis_repli_cache,
    tapis_rotation,
    tapis_universel,
)


def _fichier_curseur(dossier: Path, lane: str) -> Path:
    """Le fichier du curseur : un par lane (le repli est par lane)."""
    return dossier / f"repli-{lane.replace(':', '-').replace('/', '-')}.json"


def curseur(dossier: Path, lane: str) -> int:
    """Le nombre de blocs deja servis par le repli (persiste sur disque)."""
    try:
        brut = json.loads(_fichier_curseur(dossier, lane).read_text(encoding="utf-8"))
        return max(0, int(brut.get("servis", 0)))
    except (OSError, ValueError, TypeError, AttributeError):
        return 0


def avancer(dossier: Path, lane: str, blocs: int) -> None:
    """Le curseur avance d'un bloc : le tour suivant prend la suite du pool."""
    chemin = _fichier_curseur(dossier, lane)
    try:
        chemin.parent.mkdir(parents=True, exist_ok=True)
        fd, tmp = tempfile.mkstemp(dir=chemin.parent, suffix=".tmp")
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump({"lane": lane, "servis": int(blocs)}, fh, ensure_ascii=False)
        os.replace(tmp, chemin)
    except (OSError, TypeError, ValueError):
        pass  # un curseur non ecrit ne change pas le tirage : l'echec est ignore


def _publier(lane: str, graine: str, maintenant: datetime, metas: list[dict],
             etats_: list, file: list, prs: list[dict], origami: dict,
             fenetre: dict, occupation: dict, repli: dict, cap: dict) -> dict:
    """Le RAPPORT du repli : la voie, la cause en tete, les exclusions publiees.

    L'occupation publiee porte les exclusions **effectives** et la
    **reintroduction** (fail-OPEN) : le rapport ne confond plus un grain
    ecarte avec un grain revenu (review du coordinateur du 25/11 sur
    #28435).
    """
    from coordination import tapis_leger
    rapport = tapis_leger._rapport(lane, graine, maintenant, metas, 0.0, 0.0,
                                   gh_selection.MUR_GLOBAL_S, etats_, file, prs,
                                   origami, {"repli": True}, fenetre,
                                   occupation=occupation)
    rapport["voie"] = "repli"
    rapport["repli"] = repli
    # La cause en TETE du rapport : c'est ce qu'on cherche quand on lit un
    # tirage degrade (le rapport est lu par un humain et par les organes).
    rapport["cause_repli"] = repli.get("cause") or {}
    rapport["cap_livraisons"] = cap
    return rapport


def replir(lane: str, grains: int, maintenant: datetime, jours: int, graine: str,
           depot, cause: dict | None = None) -> tuple[dict, int]:
    """Le repli : (rapport, 0) -- ou l'echec de lecture, leve.

    Sans cache local (absent, illisible, trop vieux), le repli est IMPOSSIBLE :
    l'echec de lecture reste l'echec de lecture. Le repli ne lit **jamais**
    le reseau : le cap de livraisons y est donc INERTE. Le service est
    **chronologique** : l'ordre de creation, et le curseur fait defiler le
    pool de bloc en bloc.

    `cause` : **pourquoi** le repli a ete declenche. Le rapport la publie
    (`repli.cause` et `cause_repli`) : un repli sans motif nomme est un
    tirage degrade qu'on ne peut pas expliquer (dispatch `c0035b`).
    """
    dossier = gh_bulk.dossier_cache_defaut()
    cache = tapis_repli_cache.lire(dossier, jours)
    if not cache:
        raise gh_bulk.LectureIncomplete("selection", "repli",
                                        "ni cache local exploitable")
    metas = tapis_repli_cache.metas_de(cache)
    if not metas:
        raise gh_bulk.LectureIncomplete("selection", "repli", "cache local vide")
    citations = tapis_repli_cache.citations_de(cache)
    prs = list(cache.get("prs") or [])
    etats_ = tapis_universel.etats_leger(metas, citations, maintenant)
    grains_ = [e for e in etats_ if not e.conteneur]
    conteneurs = [e for e in etats_ if e.conteneur]
    # Le grain de HARNAIS ne se sert pas pour une lane worker (dispatch `c0035b`).
    # Les exclusions EFFECTIVES et la REINTRODUCTION (fail-OPEN) sont rendues :
    # deux sorties differentes annoncees comme identiques (review du 25/11).
    grains_, conteneurs, exclus_harnais, reintroduction = tapis_occupation.retirer_harnais(
        grains_, conteneurs, metas, lane)
    ancres = tapis_ancre.lire(lane)
    ages, exclus, _ = tapis_age.tour(grains_, ancres, maintenant, conteneurs)
    part = max(int(grains), 1)
    blocs = max(1, -(-len(grains_) // part))
    servis = curseur(dossier, lane)
    avance = servis % blocs
    file, fenetre = tapis_rotation.bloc(grains_, conteneurs, grains, grains, lane,
                                         maintenant, bloc_suivant=avance,
                                         ancres=ancres, ages_g=ages, exclus_g=exclus)
    avancer(dossier, lane, servis + 1)
    lec = gh_bulk.Lecture(issues=[], prs=prs, citations=citations,
                           lu_a=str(cache.get("lu_a") or ""), secondes=0.0, appels=0)
    _, origami = tapis_origami.mesurer(lec, reseau=False)
    from coordination import tapis_cap_livraisons
    file, temoins_cap, cap_mesure = tapis_cap_livraisons.passer(
        file, grains_ + conteneurs, lane, maintenant, prs,
        run=tapis_cap_livraisons.fetcher_hors_reseau)
    occupation = tapis_occupation.occupation_harnais(metas, lane, exclus_harnais,
                                                      reintroduction)
    repli = {"cache": str(tapis_repli_cache.chemin_cache(dossier, jours)),
             "avance": avance, "blocs": blocs, "servis": len(file),
             "curseur": servis, "cause": cause or {},
             "reintroduction": reintroduction}
    cap = {"mesure": cap_mesure, "ecartes": temoins_cap,
           "fenetre_j": tapis_cap_livraisons.FENETRE_J}
    return _publier(lane, graine, maintenant, metas, etats_, file, prs, origami,
                     fenetre, occupation, repli, cap), 0
