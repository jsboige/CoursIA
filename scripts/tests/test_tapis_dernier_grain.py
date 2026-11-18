"""Tests du raccord au classement : le DERNIER GRAIN (#27242, c3274).

Ce que ces tests verrouillent :

  - une **prise en charge nominative** (`[CLAIMED]`, `[DELIVERED]` d'une lane
    nommee) est un **grain** ;
  - une simple **citation Git** est un **passage** : elle ne rajeunit **pas**
    le dernier grain ;
  - l'absence de marqueur n'etablit une absence que si le fil est
    **complet** : sinon l'absence est **non mesurable** ;
  - une **qualification** ou une **apparition dans une liste** ne rajeunit
    rien ;
  - le classement place l'absence etablie avant l'absence non mesurable, et
    une issue servie en dernier ;
  - les **exceptions de rotation** (marathon) restent hors equilibration.

Chaque test a son **controle negatif** : la forme d'avant doit etre signalee
par le meme predicat.
"""

from __future__ import annotations

import json
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

from coordination import tapis_dernier_grain as tdg
from coordination import tapis_equilibre

FIXTURE = (Path(__file__).resolve().parent / "fixtures" / "tapis"
           / "dernier_grain_7j.json")

NOW = datetime(2026, 11, 18, 22, 38, tzinfo=timezone.utc)


def _evt(marque: str, lane: str | None, quand: datetime):
    from coordination.tapis_marqueurs import Evt
    return Evt(quand, marque, lane, None, "")


def _citation(quand: datetime):
    return {"date": quand.strftime("%Y-%m-%dT%H:%M:%SZ"), "sha": "deadbeef"}


# ---------------------------------------------------------------- les etats

def test_un_claim_nominatif_est_un_grain():
    evts = [_evt("CLAIMED", "myia-po-2027:CoursIA-2", NOW - timedelta(days=1))]
    etat = tdg.depuis_evenements(evts, [], numero=1)
    assert etat.etat == tdg.GRAIN
    assert etat.dernier_grain is not None
    assert etat.rajeunit is True


def test_une_citation_git_seule_est_un_passage_et_non_un_grain():
    """CONTROLE NEGATIF de la confusion mesuree : une citation Git n'est pas
    une prise en charge. C'est le defaut que ce raccord retire."""
    evts = []
    citations = [_citation(NOW - timedelta(days=1))]
    etat = tdg.depuis_evenements(evts, citations, numero=2)
    assert etat.etat == tdg.PASSAGE
    assert etat.dernier_grain is None, "une citation ne doit pas rajeunir le grain"
    assert etat.dernier_passage is not None
    assert etat.rajeunit is False


def test_un_marqueur_sans_lane_nomee_n_est_un_grain_de_personne():
    """Sans lane, personne n'est responsable : le marqueur ne dit rien de
    l'historique de l'issue."""
    evts = [_evt("CLAIMED", None, NOW - timedelta(days=1))]
    etat = tdg.depuis_evenements(evts, [], numero=3)
    assert etat.etat != tdg.GRAIN
    assert etat.dernier_grain is None


def test_un_released_n_est_pas_un_grain():
    """`[RELEASED]` rend la main : ce n'est pas une prise en charge."""
    evts = [_evt("RELEASED", "myia-po-2027:CoursIA-2", NOW - timedelta(days=1))]
    etat = tdg.depuis_evenements(evts, [], numero=4)
    assert etat.etat != tdg.GRAIN


def test_le_fil_partiel_donne_une_absence_non_measurable():
    """Aucun marqueur lisible + fil partiel : l'absence n'est pas etablie."""
    etat = tdg.depuis_evenements([], [], numero=5, fil_complet=False)
    assert etat.etat == tdg.NON_MESURABLE
    assert etat.etat != tdg.JAMAIS


def test_le_fil_complet_donne_une_absence_etablie():
    etat = tdg.depuis_evenements([], [], numero=6, fil_complet=True)
    assert etat.etat == tdg.JAMAIS


def test_un_grain_ancien_ne_rajeunit_pas_le_classement():
    """Le tour est une FENETRE : un grain de 30 jours ne rajeunit rien."""
    evts = [_evt("CLAIMED", "myia-po-2027:CoursIA-2", NOW - timedelta(days=30))]
    etat = tdg.depuis_evenements(evts, [], numero=7,
                                 depuis=NOW - timedelta(days=7))
    assert etat.etat == tdg.JAMAIS
    assert etat.dernier_grain is None


def test_le_classement_place_l_absence_etablie_devant_l_absence_non_measurable():
    assert tdg.RANG[tdg.JAMAIS] < tdg.RANG[tdg.NON_MESURABLE]
    assert tdg.RANG[tdg.NON_MESURABLE] < tdg.RANG[tdg.GRAIN]
    assert tdg.RANG[tdg.JAMAIS] < tdg.RANG[tdg.PASSAGE]


# ----------------------------------------------------- le releve groupe (7 j)

@pytest.fixture(scope="module")
def releve() -> dict:
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def test_le_releve_mesure_les_trois_etats(releve):
    """La population mesuree : 454 issues ouvertes au 18/11 22:38Z.

    Les 45 issues qui n'ont qu'une mention Git ne sont **pas** des issues
    servies : c'est la population que le classement historique comptait a tort.
    """
    rapport = tdg.classer_releve(releve["rows"])
    assert rapport["issues"] == 454
    assert rapport["compteurs"][tdg.GRAIN] == 327
    assert rapport["compteurs"][tdg.PASSAGE] == 45
    assert rapport["compteurs"][tdg.JAMAIS] == 82
    # L'etat « absence non mesurable » est VIDE dans ce releve : les 24 fils
    # tronques portent tous un marqueur (22) ou une mention Git (2) lisible,
    # donc l'absence n'y est pas non plus etablie. L'etat reste requis (il
    # existe dans le code, et un fil tronque SANS marqueur lisible y tombe) :
    # il est mesure a zero, pas suppose.
    assert rapport["compteurs"].get(tdg.NON_MESURABLE, 0) == 0
    assert rapport["sans_grain_etat_etabli"] == 82
    assert rapport["non_measurable"] == 0
    tronques = [r for r in releve["rows"] if r["fil_tronque"]]
    assert len(tronques) == 24
    assert all(r["marqueurs"] or r["mentions_git"] for r in tronques)


def test_le_rejeu_ne_rajeunit_rien(releve):
    """CONTROLE NEGATIF : une apparition dans une liste ne rajeunit pas le
    dernier grain. Rejouer le releve deux fois ne change aucun etat."""
    a = tdg.classer_releve(releve["rows"])
    b = tdg.classer_releve(releve["rows"])
    assert a["etats"] == b["etats"]
    etats = {e["numero"]: e["etat"] for e in a["etats"]}
    # les issues du releve sans marqueur n'ont aucun grain
    sans = [r for r in releve["rows"] if not r["marqueurs"]][:20]
    for r in sans:
        assert etats[r["n"]] != tdg.GRAIN


def test_les_45_issues_a_mention_git_seule_sont_des_candidats(releve):
    """Les 45 issues comptees comme « visitees » par le classement
    historique sont des candidats sans grain : c'est la population que le
    raccord remet dans le pool."""
    rapport = tdg.classer_releve(releve["rows"])
    candidates = set(rapport["candidats_sans_grain"])
    rows = {r["n"]: r for r in releve["rows"]}
    mentions = {n for n, r in rows.items() if r["mentions_git"] and not r["marqueurs"]}
    assert len(mentions) == 45
    assert mentions <= candidates


# ------------------------------------------------- le compteur et le classement

def test_le_compteur_ignore_les_citations_en_mode_grain(monkeypatch):
    """Le compteur du classement ne compte plus une citation comme une
    visite ; le mode historique (defaut) reste disponible."""
    from coordination.tapis_marqueurs import Evt
    evts: list[Evt] = []
    citations = [_citation(NOW - timedelta(days=1))]
    _d, total_historique, _v = tapis_equilibre.compter(evts, citations, NOW)
    assert total_historique == 1, "le mode historique compte les citations"
    _d, total_grain, _v = tapis_equilibre.compter(
        evts, citations, NOW, grains_seulement=True)
    assert total_grain == 0, "en mode grain, une citation n'est pas une visite"


def test_une_issue_servie_passe_en_derniere_du_classement():
    """La cle de tri tient compte de l'etat de grain quand il est connu."""
    from coordination.tapis_rapide import Etat

    jamais = Etat(1, "t", [], NOW.strftime("%Y-%m-%dT%H:%M:%SZ"), None, 1,
                  False, False, etat_grain=tdg.JAMAIS)
    mesure = Etat(2, "t", [], NOW.strftime("%Y-%m-%dT%H:%M:%SZ"), None, 2,
                  False, False, etat_grain=tdg.NON_MESURABLE)
    servie = Etat(3, "t", [], NOW.strftime("%Y-%m-%dT%H:%M:%SZ"), None, 3,
                  False, False, etat_grain=tdg.GRAIN)
    cles = [tapis_equilibre._cle_tri(e) for e in (jamais, mesure, servie)]
    assert cles == sorted(cles), "l'ordre doit etre jamais, non mesurable, servie"


def test_les_exceptions_de_rotation_sont_conservees():
    """Les marathons sortent de l'equilibrage : le raccord ne les change pas."""
    from coordination.tapis_rapide import Etat
    marathon = Etat(26070, "[Marathon] C#", [], NOW.strftime("%Y-%m-%dT%H:%M:%SZ"),
                    None, 26070, False, False, etat_grain=tdg.JAMAIS)
    assert tapis_equilibre.est_marathon(marathon) is True
    assert tapis_equilibre.niveau(marathon, set(), NOW) == float("inf")


# ------------------------------------------------- le rejeu (preuve demandee)

def test_le_rejeu_remonte_un_ancien_grain_sans_servir_un_grain_occupe():
    """LE REJEU DEMANDE (coordinateur, c2048) : un grain **ancien** mais
    disponible remonte dans le classement, et un grain **occupe** (claim
    vivant) ou **livre** ne remonte pas.

    Les quatre cas, dans une seule lecture :
      #1 un grain de 60 j   -> disponible, hors fenetre -> il REMONTE ;
      #2 un claim de 2 h    -> occupe par une autre lane -> ecarte ;
      #3 une livraison      -> livree -> ecartee ;
      #4 un grain de 3 j    -> servi recemment -> il passe en DERNIER.
    """
    from coordination import tapis_rapide as tr
    from scripts.tests.test_tapis_rapide import (  # les helpers de la suite du tapis
        AUTRE, LANE, NOW as NOW_TAPIS, com, etat, issue, lecture)

    lec = lecture([
        issue(1, comments=[com(24 * 60, f"[CLAIMED] lane {AUTRE} -- grain ancien")]),
        issue(2, comments=[com(2, f"[CLAIMED] lane {AUTRE} -- je prends")]),
        issue(3, comments=[com(10, f"[DELIVERED] lane {AUTRE} -- PR #900")]),
        issue(4, comments=[com(24 * 3, f"[CLAIMED] lane {AUTRE} -- grain recent")]),
    ])
    e1, e2, e3, e4 = (etat(lec, n) for n in (1, 2, 3, 4))
    # les etats de grain
    assert e1.etat_grain == tdg.JAMAIS, "un grain de 60 j est hors fenetre"
    assert e4.etat_grain == tdg.GRAIN
    # les exclusions : occupe et livre ne sont pas servis
    assert e1.ecart is None
    assert e2.ecart == "RECLAMEE"
    assert e3.ecart == "LIVREE"
    # l'ordre du classement : le grain ancien remonte, le recent passe en dernier
    servables = [e for e in tr.etats(lec, LANE, NOW_TAPIS) if e.ecart is None]
    assert [e.numero for e in servables] == [1, 4]
