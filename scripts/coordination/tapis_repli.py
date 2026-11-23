#!/usr/bin/env python3
"""Le REPLI CHRONOLOGIQUE du tirage : hors reseau, le cache local fait foi.

L'invariant I2 du contrat du picker (#28114) : « un repli chronologique ».
Hors reseau, la voie legere (`tapis_leger`) ne rend **rien** -- la lecture de
selection echoue et le point d'entree sort en 3. Ce module rend la main : il
lit le **cache** local -- le meme fichier que le tirage rapide
(`lecture-<N>j.json`, ecrit par `gh_cache_fichier.ecrire`) -- et sert le pool
dans l'**ordre de creation**.

Le cache du repli peut etre **perime** : c'est la panne du reseau qui le rend
seul disponible, et un pool d'il y a quelques heures vaut mieux qu'un tirage
vide. Au-dela de `TTL_S`, il ne vaut plus rien : le repli rend alors l'echec
de lecture, comme avant ce module.

Le **curseur** du repli est persiste dans le dossier du cache : sans lui,
chaque tour rendrait les memes grains et le pool ne serait jamais couvert.
"""
from __future__ import annotations

import json
import os
import tempfile
import time
from datetime import datetime
from pathlib import Path

from coordination import (
    gh_bulk,
    gh_selection,
    tapis_age,
    tapis_ancre,
    tapis_origami,
    tapis_rotation,
    tapis_universel,
)

#: Un cache de plus de sept jours ne vaut plus rien : le pool a trop change.
TTL_S = 7 * 24 * 3600


def chemin_cache(dossier: Path, jours: int) -> Path:
    """Le fichier de cache du tirage rapide : le meme nom, le meme dossier."""
    return dossier / f"lecture-{jours}j.json"


def lire(dossier: Path, jours: int, ttl_s: int = TTL_S) -> dict | None:
    """Le cache local, lu meme perime (c'est un repli), ou None.

    Un cache absent, illisible ou trop vieux rend None : l'appelant rend
    alors l'echec de lecture, comme avant.
    """
    try:
        brut = json.loads(chemin_cache(dossier, jours).read_text(encoding="utf-8"))
        age = time.time() - float(brut.get("_epoch", 0))
    except (OSError, ValueError, TypeError, AttributeError):
        return None
    return None if age > ttl_s else brut


def metas_de(cache: dict) -> list[dict]:
    """Les metadonnees du cache : la forme que rend `gh_selection.metadonnee`."""
    metas: list[dict] = []
    for it in cache.get("issues") or []:
        try:
            numero = int(it["number"])
        except (KeyError, TypeError, ValueError):
            continue
        metas.append({"number": numero, "title": it.get("title") or "",
                      "created_at": it.get("created_at") or "",
                      "updated_at": it.get("updated_at") or "",
                      "labels": [str(l) for l in (it.get("labels") or [])]})
    return metas


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


def replir(lane: str, grains: int, maintenant: datetime, jours: int, graine: str,
           depot) -> tuple[dict, int]:
    """Le repli : (rapport, 0) -- ou l'echec de lecture, leve.

    Sans cache local (absent, illisible, trop vieux), le repli est IMPOSSIBLE :
    l'echec de lecture reste l'echec de lecture, comme avant ce module.

    Le repli ne lit **jamais** le reseau : il n'a pas de `run`. Le cap de
    livraisons y est donc INERTE (`fetcher_hors_reseau`), temoin `mesure: false`.

    Le service est **chronologique** : l'ordre de creation, la plus ancienne
    d'abord, et le curseur fait defiler le pool de bloc en bloc -- des
    tirages successifs couvrent le pool entier sans le repeter.
    """
    dossier = gh_bulk.dossier_cache_defaut()
    cache = lire(dossier, jours)
    if not cache:
        raise gh_bulk.LectureIncomplete("selection", "repli",
                                        "ni cache local exploitable")
    metas = metas_de(cache)
    if not metas:
        raise gh_bulk.LectureIncomplete("selection", "repli", "cache local vide")
    citations: dict[int, list] = {}
    for cle, valeur in (cache.get("citations") or {}).items():
        try:
            citations[int(cle)] = valeur
        except (TypeError, ValueError):
            continue
    prs = list(cache.get("prs") or [])
    etats_ = tapis_universel.etats_leger(metas, citations, maintenant)
    grains_ = [e for e in etats_ if not e.conteneur]
    conteneurs = [e for e in etats_ if e.conteneur]
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
    from coordination import tapis_cap_livraisons, tapis_leger
    file, temoins_cap, cap_mesure = tapis_cap_livraisons.passer(
        file, grains_ + conteneurs, lane, maintenant, prs,
        run=tapis_cap_livraisons.fetcher_hors_reseau)
    rapport = tapis_leger._rapport(lane, graine, maintenant, metas, 0.0, 0.0,
                                   gh_selection.MUR_GLOBAL_S, etats_, file, prs,
                                   origami, {"repli": True}, fenetre)
    rapport["voie"] = "repli"
    rapport["repli"] = {"cache": str(chemin_cache(dossier, jours)), "avance": avance,
                        "blocs": blocs, "servis": len(file), "curseur": servis}
    rapport["cap_livraisons"] = {"mesure": cap_mesure, "ecartes": temoins_cap,
                                 "fenetre_j": tapis_cap_livraisons.FENETRE_J}
    return rapport, 0
