#!/usr/bin/env python3
"""Les formes `[INFO]` qui valent une VISITE (#27590, dispatch c2014).

Le secretariat et l'adjoint rendent compte d'une visite par une ligne
`[INFO]` : sans elle, `visit_coverage` ne voit pas leurs visites et passe
pour jamais servies les issues qu'ils ont regardees. Une lecture n'est pas
une avancee : `avancee()` reste inchangee.
"""
from __future__ import annotations

import sys
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))

from coordination import gh_bulk, tapis_equilibre, visit_coverage  # noqa: E402
from coordination.tapis_marqueurs import VISITE, evenements  # noqa: E402
from coordination.tapis_rapide import Etat  # noqa: E402
from coordination.tapis_visites import evenements_info  # noqa: E402

QUAND = "2026-11-18T09:00:00Z"
MAINTENANT = datetime(2026, 11, 20, 12, 0, tzinfo=UTC)
SECRETARIAT = ("[INFO] Visite de cycle (secrétariat myia-po-2028:CoursIA-3) — "
               "les deux conditions de la décision mai")


def _comment(body: str) -> list[dict]:
    return [{"created_at": QUAND, "body": body}]


def _visites(body: str):
    """Les evenements de visite d'un commentaire (ceux que le tapis compte)."""
    return evenements_info(_comment(body))


def test_la_forme_du_secretariat_vaut_une_visite():
    """La forme exacte du secretariat (#4427, #13410, #13902)."""
    evts = _visites(SECRETARIAT)
    assert [e.marque for e in evts] == ["VISITE-INFO"]
    assert evts[0].lane == "myia-po-2028:CoursIA-3"
    assert "VISITE-INFO" in VISITE


def test_candidate_delivered_vaut_une_visite():
    """La forme du secretaire sur une livraison constatee (#16775, #20403)."""
    evts = _visites(
        "[INFO] candidate-delivered — lane `myia-po-2028:CoursIA` — #20403 "
        "(EPIC Riemann 200). Les quatre criteres sont couverts sur l'arbre.")
    assert [e.marque for e in evts] == ["VISITE-INFO"]
    assert evts[0].lane == "myia-po-2028:CoursIA"


def test_une_ligne_info_quelconque_ne_compte_pas():
    """Controle negatif : une ligne `[INFO]` quelconque n'est pas une visite.

    Mesure du 20/11 sur 7 jours : 119 lignes `[INFO] lane ...`, 35
    `[INFO] candidate-delivered`, 4 `[INFO] visite ...`. Seules les deux
    dernieres formes sont des visites.
    """
    assert _visites(
        "[INFO] lane myia-ai-01:CoursIA-2 — bloc de synthese, 12 issues releues") == []


def test_le_mot_visite_doit_suivre_le_tag():
    """Un renvoi qui parle d'une visite n'en est pas une."""
    assert _visites(
        "[INFO] renvoi — la visite du dossier 12/11 reste ouverte") == []


def test_les_marqueurs_usuels_restent_intacts():
    """`[CLAIMED]` et `[DELIVERED]` gardent leur marqueur et leur voie."""
    comments = _comment(
        "[CLAIMED] lane myia-po-2026:CoursIA -- paths: a/**" + chr(10) +
        "[INFO] Visite de cycle (secrétariat myia-po-2028:CoursIA-3) — etat")
    evts = sorted(evenements(comments) + evenements_info(comments),
                  key=lambda e: e.quand)
    assert [e.marque for e in evts] == ["CLAIMED", "VISITE-INFO"]


def test_le_compteur_de_visites_voit_la_forme_info():
    """Une visite comptee comme seance : l'issue n'est plus a zero visite."""
    evts = _visites(SECRETARIAT)
    derniere, total, tour = tapis_equilibre.compter(evts, [], MAINTENANT)
    assert total == 1
    assert tour == 1
    assert derniere is not None


def test_une_visite_ne_vaut_pas_une_avancee():
    """`avancee()` reste inchangee : une lecture n'est pas une livraison."""
    etat = Etat(numero=4427, titre="EPIC", labels=[], cree_le="2026-06-27",
                parent=None, famille=0, conteneur=False, consolidation=False)
    lecture = gh_bulk.Lecture(
        issues=[{"number": 4427, "comments": _comment(SECRETARIAT)}], prs=[])
    assert visit_coverage.avancee(etat, lecture, MAINTENANT) is None
