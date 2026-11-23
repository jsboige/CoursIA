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
from coordination import tapis_equilibre as te
from coordination import tapis_rapide as tr
from coordination import tapis_seance
from coordination.tapis_marqueurs import Evt

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


def _servis(issues, grains: int = 8, lane: str = LANE, citations=None) -> list[int]:
    lec = lecture(issues, citations=citations)
    return [e.numero for e in tr.ordonner(tr.etats(lec, lane, NOW), lane, NOW, grains)]


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


def _evt(marque: str, heures: float, lane: str = AUTRE) -> Evt:
    """Un marqueur pose a NOW - `heures` heures."""
    return Evt(NOW - timedelta(hours=heures), marque, lane, None, "")


def test_la_voie_legere_compte_comme_le_classement():
    """UNE SEULE REGLE DE SEANCE (#27338) : la voie legere appelle l'organe
    natif (`tapis_seance.par_lane`), elle ne le reimplemente pas. Sept
    livraisons dans la journee : sept visites, dans les deux voies."""
    evts = []
    for h in (100, 90, 80, 70, 60, 50, 40):
        evts += [_evt("CLAIMED", h), _evt("DELIVERED", h - 1)]
    _d, total, _v = te.compter(evts, [], NOW)
    assert total == 7, "sept livraisons dans la journee : sept visites"


def test_les_commits_ne_doublent_pas_la_seance_de_leur_claim():
    """Une citation Git n'est PAS une visite : le classement ne la compte
    plus (c3274). Le compte HISTORIQUE -- marqueurs et citations -- reste
    disponible pour la voie legere, qui ne lit pas le fil."""
    # un claim, puis le merge de sa PR le lendemain : une visite, pas deux
    lec = lecture([issue(1, comments=[claim(40)])], citations={1: [commit("a" * 12, 20)]})
    assert etat(lec, 1).visites == 1
    # des commits SANS marqueur : un PASSAGE (activite autour de l'issue),
    # pas des visites de l'issue
    lec = lecture([issue(2)], citations={2: [commit("b" * 12, h) for h in (10, 80, 150)]})
    e2 = etat(lec, 2)
    assert e2.visites == 0, "une citation Git n'est pas une visite"
    assert e2.etat_grain == "passage_seul"
    # le compte historique garde l'ancien comportement
    cites = [commit("b" * 12, h) for h in (10, 80, 150)]
    _d, total, _v = te.compter([], cites, NOW)
    assert total == 3, "le compte historique compte les citations"


# --- le niveau strict et l'anciennete ---------------------------------------

def test_jamais_visitee_recente_devant_visitee_ancienne():
    """« Toute issue doit etre visitee au moins une fois avant qu'une autre le
    soit deux fois » : le niveau prime l'anciennete."""
    issues = [issue(1, cree="2026-01-01T00:00:00Z", comments=[claim(150), claim(60)]),
              issue(2, cree="2026-05-01T00:00:00Z", comments=[claim(100)]),
              issue(3, cree="2026-11-10T00:00:00Z")]
    assert _servis(issues) == [3, 2, 1]


def test_le_tour_et_non_la_vie_entiere():
    """« Les issues recentes ne devraient pas recevoir plus de visites que les
    anciennes » : le niveau compte les visites du tour (FENETRE_J jours). Une
    ancienne visitee quatre fois il y a longtemps passe devant une recente
    visitee hier ; une recente jamais visitee recoit d'abord sa premiere.

    Mandat du 18/11 : l'age est une priorite LEGERE. L'ancienne jamais
    visitee du tour passe donc devant la recente jamais visitee -- mais la
    visitee reste derriere les deux : l'equite du 16/11 tient."""
    vieilles = [claim(h, lane=lane) for h, lane in
                ((700, AUTRE), (500, TROISIEME), (400, AUTRE), (300, TROISIEME))]
    issues = [issue(1, cree="2026-03-01T00:00:00Z", comments=vieilles),
              issue(2, cree="2026-11-10T00:00:00Z", comments=[claim(55)]),
              issue(3, cree="2026-11-12T00:00:00Z")]
    assert _servis(issues) == [1, 3, 2]
    e1 = etat(lecture(issues), 1)
    assert (e1.visites, e1.visites_total) == (0, 4)


def test_dans_un_niveau_les_recentes_attendent_les_anciennes():
    """Trente grains jamais visites : le bonus d'age les range par bandes, et
    les servis sont pris parmi les plus anciens. La bande est un multiple de
    0,1 : les issues se regroupent par niveau (c'est ce qui fait tourner la
    tete d'une lane a l'autre) et les plus recentes attendent que les
    anciennes aient recu leur visite."""
    issues = [issue(100 + k, cree=(NOW - timedelta(days=200 - 5 * k)).strftime(
        "%Y-%m-%dT%H:%M:%SZ")) for k in range(30)]
    etats_ = tr.etats(lecture(issues), LANE, NOW)
    vus: Counter = Counter()
    for g in range(300):
        vus.update(e.numero for e in tr.ordonner(etats_, LANE, NOW, 8, graine=f"g{g}"))
    # 5 issues de plus de 180 j (bande 0,5) puis 12 de 120 a 179 j (bande 0,4)
    assert set(vus) == {100 + k for k in range(17)}
    assert min(vus.values()) > 0  # le decalage par lane couvre toute la fenetre


def test_deux_lanes_ne_recoivent_pas_la_meme_tete():
    issues = [issue(100 + k) for k in range(30)]
    etats_ = tr.etats(lecture(issues), LANE, NOW)
    tetes = {lane: tr.ordonner(etats_, lane, NOW, 8)[0].numero
             for lane in (LANE, AUTRE, TROISIEME, "myia-po-2025:CoursIA-2")}
    assert len(set(tetes.values())) > 1, tetes


# --- les exceptions du mandat -----------------------------------------------

def test_la_consolidation_recoit_une_priorite_legere_a_tout_age():
    """Mandat du 18/11 : « une autre legere priorite pour les issues de
    consolidation ». Le bonus joue a TOUT age (la division par 3 des
    consolidations de plus de 60 jours, plus forte qu'une priorite legere,
    disparait) et il est borne : deux visites priment toujours sur lui."""
    deux = [claim(150), claim(60, lane=TROISIEME)]
    issues = [issue(1, labels=["consolidation"], cree="2026-06-01T00:00:00Z", comments=deux),
              issue(2, labels=["consolidation"], cree="2026-11-01T00:00:00Z", comments=deux),
              issue(3, cree="2026-08-01T00:00:00Z", comments=[claim(50)])]
    # #3 (1 visite) passe devant #1 (2 visites) : le bonus ne vaut pas une visite
    assert _servis(issues) == [3, 1, 2]
    lec = lecture(issues)
    conso = te.familles_consolidation(tr.etats(lec, LANE, NOW))
    assert te.raisons(etat(lec, 1), conso, NOW) == [
        "2 visite(s) en 7 j (2 au total)",
        "priorite d age : -0.3 visite (plafonnee : la consolidation passe devant)",
        "priorite de consolidation : -0.6 visite"]
    assert te.raisons(etat(lec, 2), conso, NOW) == [
        "2 visite(s) en 7 j (2 au total)", "priorite d age : -0.1 visite",
        "priorite de consolidation : -0.6 visite"]


def test_la_fille_d_une_racine_de_consolidation_herite_la_priorite():
    issues = [issue(10, titre="[EPIC] Padding", labels=["consolidation"],
                    cree="2026-03-01T00:00:00Z"),
              issue(11, body="Part of #10", cree="2026-04-01T00:00:00Z",
                    comments=[claim(150), claim(60, lane=TROISIEME)]),
              issue(12, cree="2026-02-01T00:00:00Z", comments=[claim(50)])]
    lec = lecture(issues)
    conso = te.familles_consolidation(tr.etats(lec, LANE, NOW))
    # la fille herite la priorite de consolidation de sa racine
    assert "priorite de consolidation : -0.6 visite" in te.raisons(
        etat(lec, 11), conso, NOW)
    assert "priorite de consolidation : -0.6 visite" not in te.raisons(
        etat(lec, 12), conso, NOW)


def test_la_consolidation_passe_devant_l_anciennete_dans_l_etage_rapide():
    """Invariant I7 du contrat du picker (#28114, 22/11) : l'ordre des etages
    fins est « consolidation, puis anciennete ».

    AVANT, les deux bonus s'additionnaient : l'age plein (0,5) l'emportait sur
    la consolidation (0,4), et l'invariant etait viole dans l'etage rapide.
    Mesure sur `main` au 23/11 : une issue ordinaire de 170 j et une
    consolidation recente tombaient au meme niveau (-0,4), et l'anciennete
    l'emportait -- l'ordre rendu etait [6001, 6002].

    AUJOURD'HUI, la consolidation est posee EN PREMIER : son bonus depasse le
    bonus d'age plein, donc elle passe devant a visites egales ; l'age
    n'arbitre plus qu'entre issues de meme statut."""
    issues = [issue(6001, cree="2026-05-27T00:00:00Z"),          # 170 j, ordinaire
              issue(6002, labels=["consolidation"], cree="2026-11-01T00:00:00Z")]
    lec = lecture(issues)
    conso = te.familles_consolidation(tr.etats(lec, LANE, NOW))
    assert te.niveau(etat(lec, 6002), conso, NOW) < te.niveau(etat(lec, 6001), conso, NOW), \
        "la consolidation a un niveau plus bas que l'ordinary la plus agee"
    assert _servis(issues) == [6002, 6001], "la consolidation passe devant l'anciennete"


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
    assert servis[0] == 5  # trois visites, mais equilibree : avant les marathons
    lec = lecture(issues)
    assert te.raisons(etat(lec, 26604), set(), NOW) == [
        "marathon : hors equilibrage (harnais sk-agent)"]
    assert not te.est_marathon(etat(lec, 5))  # « Marathon » hors tete de titre


def test_le_rapport_porte_les_raisons_du_rang():
    lec = lecture([issue(1, comments=[claim(50)]), issue(2)])
    etats_ = tr.etats(lec, LANE, NOW)
    r = tr.rapport(lec, etats_, tr.ordonner(etats_, LANE, NOW, 8), LANE, NOW, "g")
    assert [(g["numero"], g["priorite"]) for g in r["grains"]] == [
        (2, ["0 visite(s) en 7 j (0 au total)", "priorite d age : -0.2 visite"]),
        (1, ["1 visite(s) en 7 j (1 au total)", "priorite d age : -0.2 visite"])]
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
    """Une vieille consolidation cumule l'age ET la consolidation : les deux
    motifs restent nommes, et ils somment au bonus effectif.

    La part de l'age est PLANNONNEE (0,3 visite) quand la consolidation est
    presente : la consolidation passe devant l'anciennete (I7), donc l'age ne
    peut pas manger le budget de la premiere. Le rapport le dit -- un motif
    plafonne ne se presente pas comme le bonus plein."""
    issues = [issue(1, labels=["consolidation"], cree="2026-01-01T00:00:00Z")]
    lec = lecture(issues)
    conso = te.familles_consolidation(tr.etats(lec, LANE, NOW))
    e = etat(lec, 1)
    assert te.raisons(e, conso, NOW) == [
        "0 visite(s) en 7 j (0 au total)",
        "priorite d age : -0.3 visite (plafonnee : la consolidation passe devant)",
        "priorite de consolidation : -0.6 visite"]
    assert te.niveau(e, conso, NOW) == -0.9


def test_l_age_est_compte_en_jours_pleins():
    """La bande d'age ne doit pas changer au milieu d'une tranche de quatre
    heures : l'age est compte en jours pleins, et les tranches ne franchissent
    pas minuit."""
    cree = "2026-08-25T23:30:00Z"  # 81 jours avant NOW (13/11 12:00)
    debut = NOW.replace(hour=12, minute=0)
    issues = [issue(1, cree=cree), issue(2, cree="2026-11-01T00:00:00Z")]
    un = _servis(issues)
    lec = lecture(issues)
    etats_ = tr.etats(lec, LANE, NOW)
    autre = [e.numero for e in tr.ordonner(etats_, LANE, debut.replace(hour=15, minute=59), 8)]
    assert un == autre


# --- structure ---------------------------------------------------------------

def test_module_pur_et_borne():
    """Fonctions pures : aucun import de processus ni de reseau. Plafond releve
    a la livraison ; un depassement se paie en extrayant, pas en relevant."""
    for module, plafond in ((te, 160), (tapis_seance, 60)):
        texte = (Path(module.__file__)).read_text(encoding="utf-8")
        assert len(texte.splitlines()) <= plafond
    # La purete et la taille des fonctions se verifient sur le module du
    # classement : le dernier lu par la boucle n'est pas ce module.
    texte = (Path(te.__file__)).read_text(encoding="utf-8")
    arbre = ast.parse(texte)
    importes = {a.name for n in ast.walk(arbre) if isinstance(n, ast.Import) for a in n.names}
    importes |= {n.module or "" for n in ast.walk(arbre) if isinstance(n, ast.ImportFrom)}
    assert not importes & {"subprocess", "coordination.gh_bulk", "urllib.request"}
    for noeud in ast.walk(arbre):
        if isinstance(noeud, ast.FunctionDef):
            assert noeud.end_lineno - noeud.lineno + 1 <= 60, noeud.name
