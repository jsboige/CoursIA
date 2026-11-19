"""Tests de `coordination/tapis_equilibre.py` : l'equilibrage des visites du
tapis rapide (mandat user du 2026-11-16).

Chaque regle du mandat a son test positif et son voisin : le compte des
visites en seances, le niveau strict (une issue jamais visitee passe devant
une issue visitee, meme recente), l'anciennete dans un niveau, les deux
exceptions (vieille consolidation, marathons) et la structure du module.
Aucun test ne touche le reseau.
"""
import ast
import importlib.util
from collections import Counter
from datetime import timedelta
from pathlib import Path

import pytest
from coordination import tapis_avantages
from coordination import tapis_equilibre as te
from coordination import tapis_seance
from coordination import tapis_rapide as tr

# Les fabriques de test_tapis_rapide.py, chargees par chemin : sous
# `--import-mode importlib`, `tests.` designe le premier paquet `tests` collecte
# (scripts/genai-stack/tests, par exemple), pas ce repertoire.
_SPEC = importlib.util.spec_from_file_location(
    "_fabriques_tapis_rapide", Path(__file__).with_name("test_tapis_rapide.py"))
_fab = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_fab)
AUTRE, LANE, NOW = _fab.AUTRE, _fab.LANE, _fab.NOW
com, commit, etat, issue, lecture = _fab.com, _fab.commit, _fab.etat, _fab.issue, _fab.lecture

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

TROISIEME = "myia-po-2026:CoursIA"


def claim(heures: float, lane: str = AUTRE, marque: str = "CLAIMED") -> dict:
    return com(heures, f"[{marque}] lane {lane} -- paths: x")


def _servis(issues, grains: int = 8, lane: str = LANE, citations=None,
            prs=()) -> list[int]:
    """L'ordre **fair** (la cle de service), sans la rotation de tete par lane.

    La rotation (`tr.ordonner`) fait tourner la tete du premier groupe pour
    que deux lanes divergent : elle ne se teste pas ici, elle se teste
    ailleurs -- ici on teste la CLE.
    """
    lec = lecture(issues, prs=prs, citations=citations)
    etats_ = tr.etats(lec, lane, NOW)
    servables = [e for e in etats_ if e.ecart is None]
    return [e.numero for e in te.ordre(etats_, servables, "graine", NOW,
                                        rotation=False)]


# --- le compte des visites ---------------------------------------------------

def test_une_seance_par_lane_et_par_jour():
    # claim puis livraison de la meme lane a 5 h d'ecart : une seance
    assert etat(lecture([issue(1, comments=[claim(80), claim(75, marque="DELIVERED")])]), 1
                ).visites == 1
    # la meme lane qui revient trois jours plus tard : deux seances
    assert etat(lecture([issue(2, comments=[claim(80), claim(8)])]), 2).visites == 2
    # deux lanes le meme jour : deux visites
    assert etat(lecture([issue(3, comments=[claim(9), claim(8, lane=TROISIEME)])]), 3
                ).visites == 2
    # aucun marqueur : zero, et la derniere visite est absente
    e4 = etat(lecture([issue(4)]), 4)
    assert (e4.visites, e4.derniere_visite) == (0, None)


def test_une_livraison_par_grain_compte_une_visite():
    """Une lane qui enchaîne plusieurs grains du meme umbrella les compte.

    Mesure du 19/11 (#27338) : sept livraisons dans la journee, comptees
    UNE visite -> l'issue reste en tete de classement, et la lane la
    reprend le lendemain. Une livraison vaut une visite.
    """
    marques = []
    for h in (100, 90, 80, 70, 60, 50, 40):
        marques += [claim(h, marque="CLAIMED"), claim(h - 1, marque="DELIVERED")]
    e1 = etat(lecture([issue(1, comments=marques)]), 1)
    assert (e1.visites, e1.visites_total) == (7, 7),         "sept livraisons dans le tour : sept visites"
    # les amendements d'un meme grain ne comptent pas une fois de plus
    un = [claim(100, marque="CLAIMED"), claim(99, marque="CLAIMED-AMEND"),
          claim(98, marque="DELIVERED")]
    assert etat(lecture([issue(2, comments=un)]), 2).visites == 1,         "les amendements d'un meme grain ne comptent pas une fois de plus"


def test_les_commits_ne_doublent_pas_la_seance_de_leur_claim():
    # un claim, puis le merge de sa PR le lendemain : une visite, pas deux
    lec = lecture([issue(1, comments=[claim(40)])], citations={1: [commit("a" * 12, 20)]})
    assert etat(lec, 1).visites == 1
    # des commits sans marqueur comptent : trois jours distincts, trois visites
    lec = lecture([issue(2)], citations={2: [commit("b" * 12, h) for h in (10, 80, 150)]})
    assert etat(lec, 2).visites == 3


# --- le niveau strict et l'anciennete ---------------------------------------

def test_la_cle_de_service_prime_l_anciennete():
    """Mandat du 19/11 : l'ordre est la date de la derniere PR qui **couvre**
    le grain ; sans PR, la creation du grain. L'issue qui n'a jamais recu de
    travail passe donc devant celle qui en a recu recemment."""
    servie = issue(1, cree="2026-01-15T00:00:00Z")
    issues = [servie, issue(2, cree="2026-05-01T00:00:00Z"),
              issue(3, cree="2026-11-10T00:00:00Z")]
    # #1 a ete servie par une PR de mars : sa cle est mars, pas sa creation.
    cites = {1: [{"sha": "a" * 12, "date": "2026-06-01T00:00:00Z",
                  "sujet": "Closes #1", "ferme": True, "canonique": True}]}
    # #1 a ete servie en juin : elle attend depuis juin, donc apres #2 (creee
    # en mai, jamais servie) -- c'est l'equite du 16/11, lue dans la cle.
    assert _servis(issues, citations=cites) == [2, 1, 3]


def test_le_compte_des_visites_ne_classe_plus():
    """Les visites se comptent toujours (et s'informent), mais elles ne
    **classent plus** : quatre visites sur une issue ancienne ne la placent
    pas devant une issue jamais servie. C'est le mandat du 19/11 : une voix
    par issue, la cle de service."""
    vieilles = [claim(h, lane=lane) for h, lane in
                ((700, AUTRE), (500, TROISIEME), (400, AUTRE), (300, TROISIEME))]
    issues = [issue(1, cree="2026-03-01T00:00:00Z", comments=vieilles),
              issue(2, cree="2026-11-10T00:00:00Z", comments=[claim(55)]),
              issue(3, cree="2026-11-12T00:00:00Z")]
    assert _servis(issues) == [1, 2, 3]  # par creation : la cle n'est pas une PR
    e1 = etat(lecture(issues), 1)
    assert (e1.visites, e1.visites_total) == (0, 4)


def test_la_cle_range_les_grains_par_creation_quand_aucune_pr_ne_couvre():
    """Sans PR qui couvre, la cle est la **creation** du grain : les plus
    anciens passent d'abord. Le decalage de tete par lane fait tourner la
    fenetre sur les memes grains, jamais sur une liste apprise par coeur."""
    issues = [issue(100 + k, cree=(NOW - timedelta(days=200 - 5 * k)).strftime(
        "%Y-%m-%dT%H:%M:%SZ")) for k in range(30)]
    etats_ = tr.etats(lecture(issues), LANE, NOW)
    vus: Counter = Counter()
    for g in range(300):
        vus.update(e.numero for e in tr.ordonner(etats_, LANE, NOW, 8, graine=f"g{g}"))
    # les 8 plus anciens (200 j, 195 j, ... 165 j) : la cle est la creation
    assert set(vus) <= {100 + k for k in range(24)}
    assert {100 + k for k in range(8)} <= set(vus)
    assert min(vus.values()) > 0  # le decalage par lane couvre toute la fenetre


def test_deux_lanes_ne_recoivent_pas_la_meme_tete():
    issues = [issue(100 + k) for k in range(30)]
    etats_ = tr.etats(lecture(issues), LANE, NOW)
    tetes = {lane: tr.ordonner(etats_, lane, NOW, 8)[0].numero
             for lane in (LANE, AUTRE, TROISIEME, "myia-po-2025:CoursIA-2")}
    assert len(set(tetes.values())) > 1, tetes


# --- les exceptions du mandat -----------------------------------------------

def test_la_consolidation_est_mesuree_mais_ne_classe_plus():
    """Mandat du 18/11 : « une autre legere priorite pour les issues de
    consolidation ». Mandat du 19/11 : le bonus **ne classe plus** -- il se
    mesure et s'annonce. L'ordre est la cle de service."""
    deux = [claim(150), claim(60, lane=TROISIEME)]
    issues = [issue(1, labels=["consolidation"], cree="2026-06-01T00:00:00Z", comments=deux),
              issue(2, labels=["consolidation"], cree="2026-11-01T00:00:00Z", comments=deux),
              issue(3, cree="2026-08-01T00:00:00Z", comments=[claim(50)])]
    # sans PR, la cle est la creation : #1 (juin), #3 (aout), #2 (novembre)
    assert _servis(issues) == [1, 3, 2]
    lec = lecture(issues)
    conso = te.familles_consolidation(tr.etats(lec, LANE, NOW))
    assert te.raisons(etat(lec, 1), conso, NOW) == [
        "2 visite(s) en 7 j (2 au total)",
        "cle de service : aucune PR -- creation 2026-06-01T00:00:00Z"]
    assert te.raisons(etat(lec, 2), conso, NOW) == [
        "2 visite(s) en 7 j (2 au total)",
        "cle de service : aucune PR -- creation 2026-11-01T00:00:00Z"]


def test_le_bonus_de_consolidation_se_calcule_encore_mais_ne_se_dit_plus():
    """La fille herite toujours le bonus de sa racine -- il se calcule, il ne
    se dit plus dans le rapport : le rapport annonce la CLE, pas une
    priorite qui ne classe plus."""
    issues = [issue(10, titre="[EPIC] Padding", labels=["consolidation"],
                    cree="2026-03-01T00:00:00Z"),
              issue(11, body="Part of #10", cree="2026-04-01T00:00:00Z",
                    comments=[claim(150), claim(60, lane=TROISIEME)]),
              issue(12, cree="2026-02-01T00:00:00Z", comments=[claim(50)])]
    lec = lecture(issues)
    conso = te.familles_consolidation(tr.etats(lec, LANE, NOW))
    bonus = tapis_avantages.bonus(etat(lec, 11), conso, NOW)
    assert any("consolidation" in m for m in bonus[1])
    assert "priorite de consolidation" not in te.raisons(etat(lec, 11), conso, NOW)[1]


def test_les_marathons_passent_apres_le_pool_equilibre():
    """Les marathons C# et Rust recoivent le travail du harnais sk-agent : ils
    sortent de l'equilibrage, jamais visites ou non."""
    trois = [claim(150), claim(120, lane=TROISIEME), claim(60, lane="myia-po-2028:CoursIA")]
    issues = [issue(26070, titre="[EPIC] Marathon de parite II", cree="2026-11-12T00:00:00Z"),
              issue(26510, titre="[Epic Origami] Parite Rust", cree="2026-11-14T00:00:00Z"),
              issue(26604, titre="Marathon II -- Voice Leading en C#", cree="2026-01-01T00:00:00Z"),
              issue(26700, titre="[Marathon II] Jumeau C# RL07b", cree="2026-01-02T00:00:00Z"),
              issue(26701, body="Part of #26510", cree="2026-01-03T00:00:00Z"),
              issue(5, titre="Fix(coordination): sert des issues Marathon II",
                    cree="2026-11-15T00:00:00Z", comments=trois)]
    servis = _servis(issues)
    # les marathons sortent de l'equilibrage : ils passent apres le pool
    assert set(servis[-5:]) == {26070, 26510, 26604, 26700, 26701}
    assert 5 in servis[:-5]
    lec = lecture(issues)
    assert te.raisons(etat(lec, 26604), set(), NOW) == [
        "marathon : hors equilibrage (harnais sk-agent)"]
    assert not te.est_marathon(etat(lec, 5))  # « Marathon » hors tete de titre


def test_le_rapport_porte_les_raisons_du_rang():
    lec = lecture([issue(1, comments=[claim(50)]), issue(2)])
    etats_ = tr.etats(lec, LANE, NOW)
    r = tr.rapport(lec, etats_, tr.ordonner(etats_, LANE, NOW, 8), LANE, NOW, "g")
    assert [(g["numero"], g["priorite"]) for g in r["grains"]] == [
        (1, ["1 visite(s) en 7 j (1 au total)",
             "cle de service : aucune PR -- creation 2026-10-01T00:00:00Z"]),
        (2, ["0 visite(s) en 7 j (0 au total)",
             "cle de service : aucune PR -- creation 2026-10-01T00:00:00Z"])]
    assert r["lecture"]["familles"] == 2


# --- les deux avantages legers (mandat du 18/11) -----------------------------

def test_le_bonus_total_reste_sous_une_visite():
    """« Toute issue doit etre visitee au moins une fois avant qu'une autre le
    soit deux fois » : le bonus ne vaut jamais une visite entiere, donc une
    issue a 0 visite passe devant une issue a 1 visite, meme la plus
    ancienne et la plus consolidee."""
    issues = [issue(1, labels=["consolidation"], cree="2020-01-01T00:00:00Z"),
              issue(2, cree="2026-11-12T00:00:00Z", comments=[claim(50)])]
    assert _servis(issues) == [1, 2]  # 0 visite (bonus 0,9) devant 1 visite
    lec = lecture(issues)
    conso = te.familles_consolidation(tr.etats(lec, LANE, NOW))
    assert te.niveau(etat(lec, 1), conso, NOW) == -0.9
    assert te.niveau(etat(lec, 2), conso, NOW) == 1.0


def test_les_deux_avantages_sont_distincts_et_cumulables():
    """Une vieille consolidation cumule l'age ET la consolidation : le bonus
    de consolidation n'est jamais efface par celui de l'age (le plafonnement
    porte sur la somme, pas sur la contribution)."""
    issues = [issue(1, labels=["consolidation"], cree="2026-01-01T00:00:00Z")]
    lec = lecture(issues)
    conso = te.familles_consolidation(tr.etats(lec, LANE, NOW))
    e = etat(lec, 1)
    assert te.raisons(e, conso, NOW) == [
        "0 visite(s) en 7 j (0 au total)",
        "cle de service : aucune PR -- creation 2026-01-01T00:00:00Z"]
    assert te.niveau(e, conso, NOW) == -0.9


def test_l_age_est_compte_en_jours_pleins():
    """La bande d'age ne classe plus (mandat du 19/11) : la cle est la date
    de creation, elle ne bouge pas au milieu d'une tranche de quatre heures."""
    cree = "2026-08-25T23:30:00Z"  # 81 jours avant NOW (13/11 12:00)
    debut = NOW.replace(hour=12, minute=0)
    issues = [issue(1, cree=cree), issue(2, cree="2026-11-01T00:00:00Z")]
    un = _servis(issues)
    autre = _servis(issues)
    assert un == autre == [1, 2]


# --- structure ---------------------------------------------------------------

def test_module_pur_et_borne():
    """Fonctions pures : aucun import de processus ni de reseau. Plafond releve
    a la livraison ; un depassement se paie en extrayant, pas en relevant."""
    for module, plafond in ((te, 160), (tapis_seance, 60)):
        texte = (Path(module.__file__)).read_text(encoding="utf-8")
        assert len(texte.splitlines()) <= plafond
    arbre = ast.parse(texte)
    importes = {a.name for n in ast.walk(arbre) if isinstance(n, ast.Import) for a in n.names}
    importes |= {n.module or "" for n in ast.walk(arbre) if isinstance(n, ast.ImportFrom)}
    assert not importes & {"subprocess", "coordination.gh_bulk", "urllib.request"}
    for noeud in ast.walk(arbre):
        if isinstance(noeud, ast.FunctionDef):
            assert noeud.end_lineno - noeud.lineno + 1 <= 60, noeud.name
