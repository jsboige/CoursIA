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

import subprocess
import sys
import threading
import time
from datetime import datetime, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk  # noqa: E402
from pick_idle_grain import (  # noqa: E402
    EPIC_FAMILY_DELIVERY_CAP_DEFAULT,
    EPIC_LANE_DELIVERY_CAP_DEFAULT,
    epic_lane_delivery_cause,
    epic_lane_load_counts,
)

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))
import fetch_merged_prs_since  # noqa: E402
from fetch_merged_prs_since import fetch as fetch_mergees  # noqa: E402

#: Meme fenetre que l'ardoise de lane de l'organe (LANE_RECORD_WINDOW_DAYS).
FENETRE_J = 7
#: Le code d'ecart porte par l'Etat ; le motif conserve celui de l'organe.
CODE = "PLAFOND_LIVRAISONS"


def fetcher_hors_reseau(since: str, until: str) -> list[dict]:
    """Le fetteur **INERTE** : le cap ne lit jamais le reseau quand on le demande.

    Le contrat de `fetch_merged_prs_since.fetch` est
    ``(since, until) -> list[dict]``. Ce fetteur leve : `charge_en_vol` rattrape
    l'echec et rend `None`, le cap n'est donc **pas evalue** -- temoin
    `mesure: false` dans le rapport. Fail-OPEN, comme le veut le module : on
    ne refuse jamais un item sur une charge qu'on n'a pas su lire.
    """
    raise RuntimeError("hors reseau : le cap de livraisons n'est pas evalue")


def _fetteur_cap(run_commande=None, echeance: float | None = None):
    """Le fetteur du cap : le contrat ``(since, until) -> list[dict]``.

    Deux contrats cohabitent dans la commande : celui de la COMMANDE
    (`gh_bulk.run_defaut` : ``(argv, timeout) -> str``) et celui du FETTEUR
    (``(since, until) -> list[dict]``). Ils sont adaptes ici, au point de
    contact, et l'adaptation passe par l'ARGUMENT du fetteur
    (`fetch_merged_prs_since.run_gh`) : ni le fetteur ni son argv ne sont
    reimplementes.

    Chaque tranche est bornee par le TEMPS RESTANT : le cap consomme le
    budget de la commande, il ne s'en donne pas un neuf (#28114, I6).
    """
    def slice_run(since: str, until: str) -> list[dict]:
        restant = None if echeance is None else echeance - time.monotonic()
        if restant is not None and restant <= 0:
            raise subprocess.TimeoutExpired(cmd="gh pr list", timeout=restant)
        return fetch_merged_prs_since.run_gh(
            since, until, fetch_merged_prs_since.DEFAULT_FIELDS,
            timeout=restant, run=run_commande)
    return slice_run


def _sous_echeance(lecture, echeance: float | None):
    """La lecture sous l'echeance : sa valeur, ou `None` si le delai passe.

    La borne est **structurelle** : elle ne suppose pas que l'appel respecte
    le timeout qu'il recoit. Un appel lent (reseau lent, runner lent) est
    abandonne au passage de l'echeance, et la mesure vaut `None` -- le cap
    n'ecarte rien (fail-OPEN). Le fil de lecture est un daemon : il ne retarde
    pas la fin du processus.
    """
    if echeance is None:
        return lecture()
    restant = echeance - time.monotonic()
    if restant <= 0:
        return None
    boite: list = []

    def cible() -> None:
        try:
            boite.append(("ok", lecture()))
        except BaseException as exc:  # noqa: BLE001 - propage au demandeur
            boite.append(("err", exc))

    fil = threading.Thread(target=cible, name="cap-livraisons", daemon=True)
    fil.start()
    fil.join(restant)
    if not boite:
        return None  # echeance passee : la mesure est perdue
    genre, valeur = boite[0]
    if genre == "err":
        raise valeur
    return valeur


def passer_et_replir(file: list, ordre: list, lane: str, maintenant: datetime,
                     prs_ouvertes: list[dict] | None, run=None,
                     repli=None, pool_ouvert: bool = False,
                     echeance: float | None = None, run_commande=None):
    """Le cap, puis -- s'il a VIDE la file -- le repli qui rend la main.

    Le cap de livraisons est la derniere etape de la selection : quand il
    ecarte tous les items, la file sort VIDE et la lane ne recoit RIEN --
    l'invariant I1 ("une file sans fin") est rompu par les filtres eux-memes.
    La voie chronologique prend alors le relais : le cache local rend une
    file, servie par date de creation.

    `repli` : l'appelable de repli, **injecte** (le module du repli importe
    celui-ci : l'injection evite l'import circulaire). `pool_ouvert` : le
    pool porte-t-il des candidats ? Sans candidat, il n'y a rien a servir.

    `run` : le FETTEUR du cap, au contrat `(since, until) -> list[dict]`.
    `None` : le cap lit le reseau par son propre organe, avec le `run` de la
    commande (`run_commande`) comme lanceur, sous l'`echeance` partagee.

    Rend `(file, temoins, mesure, rendu)` : `rendu` est le `(rapport, code)`
    du repli quand il a rendu la main, `None` sinon.
    """
    file, temoins, mesure = passer(file, ordre, lane, maintenant, prs_ouvertes,
                                   run=run, echeance=echeance,
                                   run_commande=run_commande)
    if file or not pool_ouvert or repli is None:
        return file, temoins, mesure, None
    try:
        return file, temoins, mesure, repli()
    except gh_bulk.LectureIncomplete:
        return file, temoins, mesure, None  # pas de cache local : file vide


def charge_en_vol(lane: str, maintenant: datetime, prs_ouvertes: list[dict] | None,
                  run=None, echeance: float | None = None,
                  run_commande=None) -> dict[int, int] | None:
    """``{issue: charge en vol de `lane`}``, ou ``None`` si la mesure echoue.

    La charge = PRs ouvertes de la lane (deja lues par le tirage, passees en
    argument -- aucun appel de plus) + livraisons mergees sur la fenetre, lues
    par le fetcher anti-troncature de ``ci/`` (une seule passe groupee par
    tranches de dates). Le compte suit le TAG de lane des corps, jamais
    ``--author`` : le compte GitHub est partage sur ce depot.

    La lecture est **sous l'echeance** de la commande : elle partage le
    budget de la selection et de la qualification au lieu d'en obtenir un
    neuf, et une lecture trop lente est abandonnee (fail-OPEN : la mesure
    vaut `None`, le cap n'ecarte rien) -- #28114, I6.
    """
    try:
        depuis = (maintenant - timedelta(days=FENETRE_J)).date().isoformat()
        fetteur = run if run is not None else _fetteur_cap(run_commande, echeance)
        mergees = _sous_echeance(
            lambda: fetch_mergees(depuis, run=fetteur, today=maintenant.date()),
            echeance)
        if mergees is None:
            return None
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
           family_cap: int = EPIC_FAMILY_DELIVERY_CAP_DEFAULT,
           echeance: float | None = None, run_commande=None
           ) -> tuple[list, list[dict], bool]:
    """Ecarte de la FILE les items plafonnes pour CETTE lane, complete par les
    suivants de l'ORDRE complet (grains puis conteneurs), meme longueur rendue.

    Rend ``(file, temoins, mesure)`` : les temoins nomment chaque item ecarte
    avec le motif de l'organe ; ``mesure`` distingue « garde evalue, rien a
    ecarter » de « mesure en panne, file intacte » (fail-OPEN). Un
    remplacant potentiel est re-verifie contre le meme cap : un item de la
    meme famille plafonnee ne remplace pas un ecarte par son propre motif.
    """
    charge = charge_en_vol(lane, maintenant, prs_ouvertes, run=run,
                           echeance=echeance, run_commande=run_commande)
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
