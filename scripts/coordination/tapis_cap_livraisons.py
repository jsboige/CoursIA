#!/usr/bin/env python3
"""Cap de livraisons EPIC branche sur la voie de tirage courante (#21067).

Le cap arbitre par le coordinateur (charge EN VOL : PRs ouvertes + livraisons
mergees sur 7 jours, item K=2 / famille K=4, arbitrage 2026-11-06T12:14Z,
implante par #24968) ne vivait que dans ``pick_idle_grain.py`` -- retire du
tirage depuis #26926. Le replay 14 j du 2026-11-21 l'a mesure : la saturation
effective ne baissait pas (42 -> 48 couples (lane, EPIC) au-dessus de K),
parce que le garde gardait un outil qu'on n'utilise plus.

Ce module rebranche l'organe EXISTANT, sans le reimplementer :
``epic_lane_load_counts`` et ``epic_lane_delivery_cause`` sont importes de
``pick_idle_grain`` (organ-first -- une reimplementation locale aurait diverge
au premier amendement du seuil). La greffe se fait sur la voie LEGERE du tapis
rapide, qui est la voie de tirage reelle ; la voie lourde (rejeu ``--lecture``,
hors ligne) ne le porte pas : sa mesure reseau echouerait de toute facon et le
fail-OPEN rendrait la file intacte.

Le refus porte sur la LANE, pas sur l'EPIC : les autres lanes voient toujours
l'item. Fail-OPEN sur toute panne de la mesure -- jamais un refus sur une
charge qu'on n'a pas pu lire.
"""
from __future__ import annotations

import sys
from datetime import datetime, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from pick_idle_grain import (  # noqa: E402
    EPIC_FAMILY_DELIVERY_CAP_DEFAULT,
    EPIC_LANE_DELIVERY_CAP_DEFAULT,
    epic_lane_delivery_cause,
    epic_lane_load_counts,
)

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))
from fetch_merged_prs_since import fetch as fetch_mergees  # noqa: E402

#: Meme fenetre que l'ardoise de lane de l'organe (LANE_RECORD_WINDOW_DAYS).
FENETRE_J = 7
#: Le code d'ecart porte par l'Etat ; le motif conserve celui de l'organe.
CODE = "PLAFOND_LIVRAISONS"


def charge_en_vol(lane: str, maintenant: datetime, prs_ouvertes: list[dict] | None,
                  run=None) -> dict[int, int] | None:
    """``{issue: charge en vol de `lane`}``, ou ``None`` si la mesure echoue.

    La charge = PRs ouvertes de la lane (deja lues par le tirage, passees en
    argument -- aucun appel de plus) + livraisons mergees sur la fenetre, lues
    par le fetcher anti-troncature de ``ci/`` (une seule passe groupee par
    tranches de dates). Le compte suit le TAG de lane des corps, jamais
    ``--author`` : le compte GitHub est partage sur ce depot.
    """
    try:
        depuis = (maintenant - timedelta(days=FENETRE_J)).date().isoformat()
        mergees = fetch_mergees(depuis, run=run, today=maintenant.date())
        return epic_lane_load_counts(mergees, lane, open_prs=prs_ouvertes,
                                     now=maintenant)
    except Exception:  # noqa: BLE001 - une mesure qui rate n'ecarte rien
        return None


def _adapte(e) -> dict:
    """L'Etat du tapis, vu comme l'item dict que lit l'organe de pick_idle_grain.

    ``is_consolidation`` (appele par ``epic_lane_delivery_cause``) lit le
    label ; les trois formes d'etiquette y sont tolerees, la liste de chaines
    nues du tapis en est une.
    """
    return {"number": e.numero, "parent": e.parent, "labels": e.labels}


def passer(file: list, ordre: list, lane: str, maintenant: datetime,
           prs_ouvertes: list[dict] | None, run=None,
           cap: int = EPIC_LANE_DELIVERY_CAP_DEFAULT,
           family_cap: int = EPIC_FAMILY_DELIVERY_CAP_DEFAULT
           ) -> tuple[list, list[dict], bool]:
    """Ecarte de la FILE les items plafonnes pour CETTE lane, complete par les
    suivants de l'ORDRE complet (grains puis conteneurs), meme longueur rendue.

    Rend ``(file, temoins, mesure)`` : les temoins nomment chaque item ecarte
    avec le motif de l'organe ; ``mesure`` distingue « garde evalue, rien a
    ecarter » de « mesure en panne, file intacte » (fail-OPEN). Un
    remplacant potentiel est re-verifie contre le meme cap : un item de la
    meme famille plafonnee ne remplace pas un ecarte par son propre motif.
    """
    charge = charge_en_vol(lane, maintenant, prs_ouvertes, run=run)
    if charge is None:
        return file, [], False

    def plafonne(e) -> str | None:
        return epic_lane_delivery_cause(_adapte(e), charge, cap, lane,
                                        family_cap=family_cap)

    temoins: list[dict] = []
    gardes = []
    for e in file:
        motif = plafonne(e)
        if motif:
            e.ecart, e.motif = CODE, motif
            temoins.append({"numero": e.numero, "motif": motif})
        else:
            gardes.append(e)
    if not temoins:
        return file, [], True
    pris = {e.numero for e in gardes}
    cible = len(file)
    for e in ordre:
        if len(gardes) >= cible:
            break
        if e.numero in pris or e.ecart is not None or plafonne(e):
            continue
        gardes.append(e)
        pris.add(e.numero)
    return gardes, temoins, True
