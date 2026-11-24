"""Tests de la CLE DE SERVICE (19/11) : le lien canonique, la cle, et le
departage a niveau egal.

Trois briques, trois familles de tests :

- la **forme canonique** (`coordination.tapis_canon`) : un lien, pas une
  mention ;
- la **cle** (`coordination.tapis_cle`) : la date de la derniere PR qui
  couvre le grain ; le hub suit son enfant, pas son frere ;
- le **departage** (`coordination.tapis_age`, `coordination.tapis_equilibre`) :
  a classe egale, la cle decide -- elle ne primarise pas, l'invariant de
  couverture du 16/11 (#27590) reste le premier critere.

Aucun test ne touche le reseau.
"""
import importlib.util
from pathlib import Path

from coordination import tapis_age
from coordination import tapis_canon, tapis_cle
from coordination import tapis_equilibre as te
from coordination import tapis_rapide as tr

# Les fabriques de test_tapis_rapide.py, chargees par chemin : sous
# `--import-mode importlib`, `tests.` designe le premier paquet `tests` collecte
# (scripts/genai-stack/tests, par exemple), pas ce repertoire.
_SPEC = importlib.util.spec_from_file_location(
    "_fabriques_tapis_rapide", Path(__file__).with_name("test_tapis_rapide.py"))
_fab = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_fab)
LANE, NOW = _fab.LANE, _fab.NOW
issue, lecture, etat = _fab.issue, _fab.lecture, _fab.etat


def pr(numero: int, corps: str, date: str = "2026-11-20T10:00:00Z") -> dict:
    """Une PR ouverte, telle que la lecture les porte."""
    return {"number": numero, "body": corps, "title": f"PR {numero}",
            "created_at": date, "updated_at": date}


# --- la forme canonique -------------------------------------------------------

def test_le_lien_canonique_ne_se_confond_avec_une_mention():
    assert tapis_canon.est_canonique("See #12", 12)
    assert tapis_canon.est_canonique("Part of #12", 12)
    assert tapis_canon.est_canonique("Closes #12", 12)
    assert tapis_canon.est_canonique("Closes: #12", 12)
    assert tapis_canon.est_canonique("Fix(ci,#12)", 12)
    assert tapis_canon.est_canonique("Fixes #12", 12)
    # une mention n'est pas un lien
    assert not tapis_canon.est_canonique("Le grain #12 avance", 12)
    assert not tapis_canon.est_canonique("Refs #12", 12)
    assert not tapis_canon.est_canonique("cf. #12", 12)
    assert not tapis_canon.est_canonique("See #13", 12)


def test_les_prs_canoniques_se_lisent_par_grain():
    couvert = tapis_canon.des_prs_canoniques(
        [pr(900, "See #1\nPart of #2"), pr(901, "aucun lien")])
    assert set(couvert) == {1, 2}
    assert couvert[1][0]["pr"] == 900
    assert couvert[1][0]["date"] == "2026-11-20T10:00:00Z"


# --- la cle -------------------------------------------------------------------

def test_la_cle_vient_du_lien_canonique_de_la_pr():
    lec = lecture([issue(1)], prs=[pr(900, "See #1")])
    e = etat(lec, 1)
    assert e.cle_service == "2026-11-20T10:00:00Z"
    assert e.cle_origine == "PR #900"


def test_une_mention_en_prose_ne_donne_pas_de_cle():
    lec = lecture([issue(1)], prs=[pr(900, "Le grain #1 avance")])
    assert etat(lec, 1).cle_service == ""


def test_la_cle_vient_aussi_des_commits_merges_canoniques():
    lec = lecture([issue(1)], citations={
        1: [{"sha": "abc1234", "date": "2026-11-05T08:00:00Z", "sujet": "Fix(x): y",
              "ferme": False, "canonique": True}]})
    e = etat(lec, 1)
    assert e.cle_service == "2026-11-05T08:00:00Z"
    assert e.cle_origine == "commit abc1234"


def test_une_citation_non_canonique_ne_donne_pas_de_cle():
    lec = lecture([issue(1)], citations={
        1: [{"sha": "abc1234", "date": "2026-11-05T08:00:00Z", "sujet": "Fix(x): y",
              "ferme": False, "canonique": False}]})
    assert etat(lec, 1).cle_service == ""


def test_le_hub_suit_son_enfant_et_pas_son_frere():
    issues = [issue(1, body="Part of #2"), issue(2), issue(3)]
    lec = lecture(issues, prs=[pr(900, "Closes #1")])
    etats_ = tr.etats(lec, LANE, NOW)
    cles = {e.numero: e.cle_service for e in etats_}
    assert cles[1] == "2026-11-20T10:00:00Z"
    assert cles[2] == "2026-11-20T10:00:00Z"  # le hub suit l'enfant
    assert cles[3] == ""  # le frere garde sa propre cle


def test_la_cle_la_plus_recente_gagne():
    lec = lecture([issue(1)], prs=[pr(900, "See #1", "2026-11-01T00:00:00Z"),
                                    pr(901, "See #1", "2026-11-20T00:00:00Z")])
    e = etat(lec, 1)
    assert e.cle_service == "2026-11-20T00:00:00Z"


def test_la_densite_du_hub_est_une_mesure_pas_un_bonus():
    issues = [issue(1, body="Part of #9"), issue(2, body="Part of #9")]
    etats_ = tr.etats(lecture(issues), LANE, NOW)
    assert tapis_cle.densites(etats_) == {9: 2}


# --- le departage -------------------------------------------------------------

def _deux_grains_pries():
    """Deux grains de meme famille, meme niveau, deux dates de service.

    Les services viennent de **commits merges** : une PR **ouverte** qui
    cite le grain l'ecarte du tirage (ecart COUVERTE) -- elle ne decide
    donc pas d'un rang, elle le retire.
    """
    issues = [issue(1, body="Part of #90"), issue(2, body="Part of #90")]
    lec = lecture(issues, citations={
        1: [{"sha": "a1", "date": "2026-10-01T00:00:00Z", "sujet": "Fix(x): y",
              "ferme": False, "canonique": True}],
        2: [{"sha": "b2", "date": "2026-11-01T00:00:00Z", "sujet": "Fix(x): z",
              "ferme": False, "canonique": True}]})
    return tr.etats(lec, LANE, NOW)


def test_a_niveau_egal_la_cle_decide_dans_la_voie_universelle():
    etats_ = _deux_grains_pries()
    servables = [e for e in etats_ if e.ecart is None]
    ordre = te.ordre(etats_, servables, "graine-de-test", NOW, rotation=False)
    # la PR la plus ancienne d'abord : un grain recemment servi recule
    assert [e.numero for e in ordre] == [1, 2]


def test_a_niveau_egal_la_cle_decide_dans_la_voie_legere():
    etats_ = _deux_grains_pries()
    g1, g2 = sorted(etats_, key=lambda e: e.numero)
    assert tapis_age.cle(g1, NOW) < tapis_age.cle(g2, NOW)
    # la creation ne classe plus : c'est le service qui fait l'anciennete
    assert g1.cree_le == g2.cree_le
    assert tapis_age.cle(g1, NOW)[3] == g1.cle_service
