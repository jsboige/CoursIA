#!/usr/bin/env python3
"""Les formes `[INFO]` qui valent une VISITE (#27590, dispatch c2014).

Le secretariat et l'adjoint rendent compte d'une visite par une ligne
`[INFO]` : sans elle, `visit_coverage` ne voit pas leurs visites et passe
pour jamais servies les issues qu'ils ont regardees. Une lecture n'est pas
une avancee : `avancee()` reste inchangee.
"""
from __future__ import annotations

import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))

from coordination import gh_bulk, tapis_dernier_grain, tapis_equilibre, visit_coverage  # noqa: E402
from coordination.tapis_marqueurs import MARQUEUR_GRAIN, VISITE, evenements  # noqa: E402
from coordination.tapis_rapide import Etat, _plafond  # noqa: E402
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


# --------------------------------------------------------------------------
# Les trois effets de l'elargissement de `VISITE` (revue du 21/11)
# --------------------------------------------------------------------------

def test_une_lecture_ne_devient_pas_une_prise_en_charge():
    """Effet 1 : une lecture (`VISITE-INFO`) ne fait pas un grain.

    L'etat de grain distingue la prise en charge de la lecture : une
    qualification est une lecture, pas une prise en charge (doctrine de
    `tapis_dernier_grain`). C'est pourquoi `_marqueurs_grain` lit
    `MARQUEUR_GRAIN`, et non `VISITE`.
    """
    evts = _visites(SECRETARIAT)
    assert "VISITE-INFO" in VISITE
    assert "VISITE-INFO" not in MARQUEUR_GRAIN
    assert tapis_dernier_grain._marqueurs_grain(evts) == []
    etat = tapis_dernier_grain.depuis_evenements(
        evts, [], numero=4427, fil_complet=True)
    assert etat.etat != tapis_dernier_grain.GRAIN
    assert etat.etat == tapis_dernier_grain.JAMAIS
    assert etat.grains == 0


def test_la_lecture_compte_comme_une_visite():
    """Effet 2 : `compter_grains` compte la lecture comme une visite.

    Le compteur de visites du tour (l'unite de l'equilibrage) voit la lecture
    d'une lane : l'issue n'est plus au niveau zero.
    """
    evts = _visites(SECRETARIAT)
    derniere, total, tour = tapis_dernier_grain.compter_grains(
        evts, MAINTENANT - timedelta(days=7))
    assert derniere is not None
    assert total == 1
    assert tour == 1


def test_un_info_visite_ecarte_le_conteneur_chaud():
    """Effet 3 : une lecture d'une autre lane declenche le plafond #22500.

    Un conteneur recemment regarde par une autre lane est un conteneur chaud :
    le tapis ne le sert pas pendant la fenetre du plafond.
    """
    etat = Etat(numero=27543, titre="EPIC", labels=[], cree_le="2026-10-01",
                parent=None, famille=0, conteneur=True, consolidation=False)
    evts = _visites(SECRETARIAT)
    motif = _plafond(etat, evts, [], "myia-ai-01:CoursIA-2", MAINTENANT)
    assert motif is not None
    assert "plafond EPIC" in motif
    # La meme visite, le long de la fenetre : plus de plafond.
    assert _plafond(etat, evts, [], "myia-ai-01:CoursIA-2",
                     MAINTENANT + timedelta(days=30)) is None


def test_une_ligne_qui_repond_aux_deux_formes_ne_compte_qu_une_fois():
    """Mineur 1 : la deduplication se fait par ligne, pas par fragment.

    Une ligne `[INFO] Visite ... candidate-delivered` repond aux deux formes :
    elle ne doit produire qu'un evenement, pas deux.
    """
    evts = _visites(
        "[INFO] Visite de cycle -- candidate-delivered, lane "
        "`myia-po-2028:CoursIA-3` (#20403)")
    assert [e.marque for e in evts] == ["VISITE-INFO"]


def test_une_visite_annulee_ne_compte_pas():
    """Mineur 2 : une visite annulee n'est pas une visite."""
    assert _visites(
        "[INFO] Visite annulee -- la lecture n'a pas eu lieu, lane "
        "`myia-po-2028:CoursIA-3`") == []
