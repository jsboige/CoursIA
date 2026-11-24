"""Tests de la voie LEGERE du tirage (`coordination/tapis_leger.py`) -- #27225.

La bascule separe deux temps, et chacun se verifie ici :

1. le **tirage** ne lit que des metadonnees -- ni corps, ni commentaires : il
   tourne la tete de niveau sur TOUTES les issues ouvertes et rend l'**etat**
   de chaque grain et l'**action** a faire ;
2. la **qualification** (prise en charge) lit le corps et le **FIL COMPLET**
   (l'organe REST `gh_snapshot`), jamais la fenetre des 12 derniers
   commentaires de la lecture groupee, et **rejoue les neuf regles** de la
   voie lourde -- dont elle affiche le code et le motif.

Aucun test ne touche le reseau : `run` est un faux, le fil est monkeypatche.
"""
import json
import re
import subprocess
import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk, gh_issues, gh_selection, tapis_ancre
from coordination import tapis_fenetre, tapis_rotation, tapis_verdict
from coordination import tapis_leger, tapis_rapide
from coordination import tapis_qualification as tq
from coordination import tapis_universel as tu

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 18, 9, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"


def _noeud(n: int, titre: str = "", cree: str = "2026-11-01T00:00:00Z",
           labels=()) -> dict:
    return {"number": n, "title": titre or f"Grain {n}", "createdAt": cree,
            "updatedAt": cree, "labels": {"nodes": [{"name": lab} for lab in labels]}}


def _page_metas(nodes: list[dict], suivant: bool = False) -> str:
    return json.dumps({"data": {"repository": {"issues": {
        "pageInfo": {"hasNextPage": suivant, "endCursor": "c"},
        "nodes": nodes}}}})


def _page_issues_multiples(requete: str) -> str:
    """La reponse au lot : un alias par issue demandee (`i0`, `i1`, ...)."""
    alias: dict[str, dict] = {}
    for k, n in re.findall(r"i(\d+):\s*issue\(number:(\d+)\)", requete):
        alias[f"i{k}"] = {"number": int(n), "title": f"Grain {n}",
                          "body": f"Part of #{n}", "createdAt": "2026-11-01T00:00:00Z",
                          "updatedAt": "2026-11-01T00:00:00Z", "labels": {"nodes": []},
                          "comments": {"totalCount": 0, "nodes": []}}
    return json.dumps({"data": {"repository": alias}})


def _run_faux(appels: list[list[str]] | None = None, nb: int = 4):
    """Un faux `run` : metadonnees, lecture ciblee, citations (vide), PRs (vides)."""
    def run(argv, timeout):
        if appels is not None:
            appels.append(list(argv))
        requete = " ".join(argv)
        if "graphql" in requete:
            # Une requete mal formee (accolade de trop) ne se voit qu'aupres
            # de GitHub : le faux la refuse ici, pour que le defaut soit vu
            # par les tests, pas par la flotte.
            if requete.count("{") != requete.count("}"):
                raise AssertionError(f"requete GraphQL mal formee : {requete[:160]}")
        if "issue(number:" in requete:
            return _page_issues_multiples(requete)
        if "graphql" in requete:
            return _page_metas([_noeud(7 + k) for k in range(nb)])
        if argv[0] == "git":
            return ""  # aucune citation : personne n'a visite ces issues
        return "[]"  # aucune PR ouverte

    return run


# --- le tirage ne lit que des metadonnees -------------------------------------

def test_le_classement_ne_lit_que_des_metadonnees():
    """Le classement ne demande ni corps ni commentaires : la requete le dit."""
    appels: list[list[str]] = []
    gh_selection.lire_metadonnees_issues(_run_faux(appels))
    requete = " ".join(appels[0])
    assert "body" not in requete and "comments" not in requete


def test_le_tirage_leger_ne_decide_aucun_ecart(monkeypatch):
    """Le tirage n'ecarte rien : les neuf regles ne sont pas decidables sur
    des metadonnees, elles se decident a la prise en charge.

    Une exclusion decidable sur metadonnees (le label `candidate-delivered`)
    ne doit donc PAS disparaitre du classement : elle est rendue avec son
    etat, et l'action qui va avec.
    """
    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "g", Path("."),
                                       _run_faux(nb=6))
    assert code == 0
    assert rapport["voie"] == "leger"
    assert rapport["pool"] == 6
    for g in rapport["grains"]:
        assert "action" in g and g["action"]
        assert g["action"].startswith("qualifier #")


def test_le_tirage_leger_sert_une_file_plus_longue_que_le_nombre_de_grains():
    """La file sert plus de grains que demande : la qualification ecarte au
    moment de l'action, et la file doit rester pleine."""
    rapport, _ = tapis_leger.tirage(LANE, 2, NOW, 45, "g", Path("."),
                                    _run_faux(nb=12))
    assert len(rapport["grains"]) > 2


def test_un_conteneur_ne_passe_jamais_devant_un_grain(monkeypatch):
    """Un EPIC est un conteneur : il ne passe jamais devant un grain (#26926).

    La detection se fait sur les metadonnees (titre `[EPIC ...]`, labels), donc
    elle ne peut pas attendre la lecture du corps.
    """
    def run_epic(argv, timeout):
        requete = " ".join(argv)
        if "graphql" in requete and "issue(number:" not in requete:
            return _page_metas([_noeud(7), _noeud(8, titre="[EPIC] Cadre"),
                                _noeud(9)])
        return _run_faux()(argv, timeout)

    rapport, _ = tapis_leger.tirage(LANE, 3, NOW, 45, "g", Path("."), run_epic)
    numeros = [g["numero"] for g in rapport["grains"]]
    if 8 in numeros:
        autres = [i for i, n in enumerate(numeros) if n != 8]
        assert numeros.index(8) > max(autres), \
            "un conteneur ne passe jamais devant un grain"


# --- la fenetre qui avance sur le pool -----------------------------------------

def test_la_fenetre_avance_sur_le_pool():
    """La fenetre servie avance d'un bloc par tranche de 4 h.

    Sans elle, la tete du classement reste figee et la liste `3 x grains`
    ecrase les issues jamais visitees : mesure du 18/11 (pool de 441
    issues), **38 issues couvertes sur 12 tours**, dont 114 jamais visitees
    hors de portee. Ici la propriete est verifiere hors ligne :

    - un tour complet du pool tient en `ceil(pool / taille)` tranches ;
    - les blocs sont DISJOINTS : toute issue est proposee une fois avant
      qu'une autre le soit deux fois ;
    - les issues jamais visitees sont donc atteintes.
    """
    pool, taille = 120, 24
    metas = [{"number": 1000 + k, "title": f"Grain {k}",
              "created_at": "2026-11-01T00:00:00Z", "labels": []}
             for k in range(pool)]
    base = datetime(2026, 11, 18, 0, 0, tzinfo=UTC)
    blocs: list[set[int]] = []
    for t in range(12):
        maintenant = base + timedelta(hours=4 * t)
        etats_ = tu.etats_leger(metas, {}, maintenant)
        grains_, conteneurs = tapis_leger._ordre(etats_, LANE, maintenant, f"g{t}")
        file, fenetre = tapis_rotation.bloc(grains_, conteneurs, 8, taille,
                                             LANE, maintenant)
        assert len(file) == taille
        blocs.append({e.numero for e in file})
    union = set().union(*blocs)
    assert union == {m["number"] for m in metas}, "le pool entier doit etre couvert"
    tour = -(-pool // taille)  # ceil(pool / taille) : les blocs d'un tour complet
    for i, a in enumerate(blocs[:tour]):
        for b in blocs[i + 1:tour]:
            assert not (a & b), "les blocs d'un tour doivent etre disjoints"
    assert len(set().union(*blocs[:tour])) == pool
    assert blocs[0] != blocs[1], "la fenetre doit avancer"


def test_le_tour_avance_par_numero_meme_si_le_classement_change():
    """Le classement BOUGE d'un tour a l'autre (les visites s'accumulent) :
    le tour doit pourtant couvrir le pool entier.

    C'est la rotation par NUMERO qui le garantit -- une rotation qui suit la
    POSITION dans le classement fait passer des issues a travers le bloc.
    Mesure du 19/11 : **380 issues sur 440** atteintes en un tour, un tour
    complet en demandait 440.
    """
    pool, taille = 60, 12
    metas = [{"number": 1000 + k, "title": f"Grain {k}",
              "created_at": "2026-11-01T00:00:00Z", "labels": []}
             for k in range(pool)]
    base = datetime(2026, 11, 18, 0, 0, tzinfo=UTC)
    blocs: list[set[int]] = []
    for t in range(5):
        maintenant = base + timedelta(hours=4 * t)
        etats_ = tu.etats_leger(metas, {}, maintenant)
        grains_, conteneurs = tapis_leger._ordre(etats_, LANE, maintenant, f"g{t}")
        # Le classement change : les grains deja servis DESCENDENT.
        vus = set().union(*blocs) if blocs else set()
        grains_ = sorted(grains_, key=lambda g: (g.numero in vus, g.numero))
        file, fenetre = tapis_rotation.bloc(grains_, conteneurs, 8, taille,
                                             LANE, maintenant)
        blocs.append({e.numero for e in file})
    tour = -(-pool // taille)
    assert set().union(*blocs[:tour]) == {m["number"] for m in metas}, (
        "le tour par numero doit couvrir le pool entier")


def test_le_tour_publie_son_delai_maximal():
    """Le delai maximal de requalification est borne par la duree du tour,
    et il est publie avec le bloc : il ne se deduit pas du tableau de bord."""
    pool, taille = 60, 12
    grains = [type("G", (), {"numero": 1000 + k})() for k in range(pool)]
    _, fen = tapis_rotation.bloc(grains, [], 8, taille, LANE,
                                  datetime(2026, 11, 18, 0, 0, tzinfo=UTC))
    assert fen["ordre"] == "numero"
    assert fen["delai_max_h"] == 4 * 5, "5 blocs de 4 h : le tour dure 20 h"


# --- la qualification de la prise en charge -----------------------------------

def test_la_requete_de_qualification_est_bien_formee():
    """La requete de qualification doit etre ACCEPTEE par GraphQL.

    Defaut deja mesure : un bloc de champs qui se ferme lui-meme produit une
    accolade de trop, et l'erreur n'apparait qu'aupres de GitHub, en
    `Expected one of SCHEMA, SCALAR, TYPE...`.
    """
    appels: list[list[str]] = []
    tq.qualifier([7, 8], LANE, NOW, 45, [],_run_faux(appels))
    requete = " ".join(appels[0])
    assert requete.count("{") == requete.count("}")
    assert requete.count("issue(number:") == 2


def test_un_lot_partiel_donne_un_verdict_a_chaque_numero(monkeypatch):
    """Un numero demande ne disparait jamais sans verdict.

    Le lot revient avec une issue absente (son alias etait nul) : le numero
    absent sort en `ecartees` avec son code et son motif -- il ne disparait
    pas du tirage en silence (revue du 19/11)."""
    def faux_qualifier(run, depot, numeros=None):
        return {7: {"number": 7, "title": "Grain 7", "body": "",
                    "created_at": "2026-11-01T00:00:00Z",
                    "comments": [], "comments_total": 0, "labels": []},
                8: None}

    monkeypatch.setattr(tq.tapis_lot.gh_selection, "qualifier", faux_qualifier)
    issues: dict = {}
    echecs: list = []
    ecartees: dict = {}
    assert tq.tapis_lot.fenetre([7, 8], None, issues, echecs, ecartees) == 1
    assert 7 in issues, "le numero lu est rendu"
    assert 8 not in issues, "le numero absent n'est pas lu"
    assert ecartees[8]["code"] == "ABSENT"
    assert ecartees[8]["motif"]
    assert 8 not in echecs, "un numero absent n'est pas un echec de lecture"


def test_la_qualification_lit_le_fil_complet(monkeypatch):
    """Le fil qualifie n'est PAS la fenetre des 12 derniers commentaires.

    C'est la condition de la bascule : le marqueur qui ecarte un grain peut
    etre plus vieux que la fenetre (constat de #27179).
    """
    vus: list[int] = []

    def faux_fil(repo, number):
        vus.append(number)
        return [{"createdAt": "2026-11-17T00:00:00Z",
                 "author": {"login": "jsboige"},
                 "body": f"[CLAIMED] lane myia-po-2025:CoursIA-2 -- commentaire {k}"} for k in range(40)]

    monkeypatch.setattr(tq.tapis_fenetre.gh_snapshot, "fetch_issue_comments", faux_fil)
    # La fenetre annonce 40 commentaires, la lecture ciblee n'en rend que 12 :
    # le fil complet est donc requis, et c'est lui qui tranche.
    def run_tronque(argv, timeout):
        requete = " ".join(argv)
        if "issue(number:" in requete:
            alias: dict[str, dict] = {}
            for k, n in re.findall(r"i(\d+):\s*issue\(number:(\d+)\)", requete):
                alias[f"i{k}"] = {"number": int(n), "title": f"Grain {n}", "body": "",
                                  "createdAt": "2026-11-01T00:00:00Z",
                                  "updatedAt": "2026-11-01T00:00:00Z",
                                  "labels": {"nodes": []},
                                  "comments": {"totalCount": 40, "nodes": []}}
            return json.dumps({"data": {"repository": alias}})
        return _run_faux()(argv, timeout)

    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [],run_tronque)
    assert not echecs
    assert vus == [7], "le fil complet doit etre relu"
    assert len(servis) == 0, "un claim vivant d'une autre lane ecarte le grain"
    assert ecartees[7]["code"] == "RECLAMEE"


def test_un_fil_illisible_refuse_la_qualification(monkeypatch):
    """Un fil illisible REFUSE le grain (fail-CLOSED) : la decision n'a pas
    pu etre prise, donc le grain n'est pas servi -- il porte son code.

    Le temps d'action engage un grain dont le fil a ete lu ; un grain dont
    la lecture a echoue n'est pas servi en catimini.
    """
    def faux_fil(repo, number):
        raise RuntimeError("fil indisponible")

    monkeypatch.setattr(tq.tapis_fenetre.gh_snapshot, "fetch_issue_comments", faux_fil)

    def run_tronque(argv, timeout):
        requete = " ".join(argv)
        if "issue(number:" in requete:
            alias: dict[str, dict] = {}
            for k, n in re.findall(r"i(\d+):\s*issue\(number:(\d+)\)", requete):
                alias[f"i{k}"] = {"number": int(n), "title": f"Grain {n}", "body": "",
                                  "createdAt": "2026-11-01T00:00:00Z",
                                  "updatedAt": "2026-11-01T00:00:00Z",
                                  "labels": {"nodes": []},
                                  "comments": {"totalCount": 13, "nodes": []}}
            return json.dumps({"data": {"repository": alias}})
        return _run_faux()(argv, timeout)

    servis, ecartees, echecs,arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [],run_tronque)
    assert not servis, "un fil illisible ne se sert pas en catimini"
    assert ecartees[7]["code"] == "FIL_ILLISIBLE"
    assert ecartees[7]["motif"]
    assert 7 in echecs


def test_le_marqueur_decisif_hors_fenetre_ecarte_le_grain(monkeypatch):
    """Frontiere 12/13 : le marqueur decisif est HORS de la fenetre, et il
    pese quand meme.

    La fenetre de la lecture groupee porte les 12 derniers commentaires ;
    l'issue en porte 13. Le marqueur qui ecarte le grain est le PREMIER
    commentaire -- hors fenetre. Le fil complet (pagine) doit le trouver :
    c'est la condition de la bascule.
    """
    vus: list[int] = []
    bruit = [{"createdAt": "2026-11-16T00:00:00Z", "author": {"login": "jsboige"},
              "body": f"bruit {k}"} for k in range(12)]
    decisif = {"createdAt": "2026-11-17T00:00:00Z", "author": {"login": "jsboige"},
               "body": "[CLAIMED] lane myia-po-2025:CoursIA-2 -- paths: a/**"}

    def faux_fil(repo, number):
        vus.append(number)
        return [decisif] + bruit  # 13 commentaires : le decisif est le premier

    monkeypatch.setattr(tq.tapis_fenetre.gh_snapshot, "fetch_issue_comments", faux_fil)

    def run_fenetre(argv, timeout):
        requete = " ".join(argv)
        if "issue(number:" in requete:
            alias: dict[str, dict] = {}
            for k, n in re.findall(r"i(\d+):\s*issue\(number:(\d+)\)", requete):
                alias[f"i{k}"] = {"number": int(n), "title": f"Grain {n}", "body": "",
                                  "createdAt": "2026-11-01T00:00:00Z",
                                  "updatedAt": "2026-11-01T00:00:00Z",
                                  "labels": {"nodes": []},
                                  "comments": {"totalCount": 13, "nodes": bruit}}
            return json.dumps({"data": {"repository": alias}})
        return _run_faux()(argv, timeout)

    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [],run_fenetre)
    assert vus == [7], "le fil complet doit etre relu (13 > 12)"
    assert not servis
    assert ecartees[7]["code"] == "RECLAMEE"
    assert ecartees[7]["fenetre_suffit"] is False


def test_l_echeance_refuse_la_prise_en_charge(monkeypatch):
    """L'echeance depassee REFUSE la prise en charge : le grain n'est pas
    servi en catimini, il porte son code de refus."""
    def faux_fil(repo, number):
        raise AssertionError("le fil ne doit pas etre lu apres l'echeance")

    monkeypatch.setattr(tq.tapis_fenetre.gh_snapshot, "fetch_issue_comments", faux_fil)
    lec = gh_bulk.Lecture(issues=[{
        "number": 7, "title": "Grain 7", "body": "", "created_at": "2026-11-01T00:00:00Z",
        "updated_at": "2026-11-01T00:00:00Z", "labels": [], "comments_total": 40,
        "comments": []}], prs=[], citations={}, lu_a="2026-11-18T08:00:00Z")
    etats = tapis_rapide.etats(lec, LANE, NOW)
    confirmes, rejetes, echecs, appels = tq.tapis_fil_complet.confirmer(
        etats, lec, LANE, NOW, 45, echeance=0.0, horloge=lambda: 10.0)
    assert not confirmes
    assert rejetes[0]["code"] == "ECHEANCE"
    assert rejetes[0]["motif"]


def test_le_mur_de_lectures_refuse_la_prise_en_charge(monkeypatch):
    """Le mur de lectures REST atteint REFUSE aussi : un grain dont le fil
    n'a pas etre lu n'est pas servi."""
    def faux_fil(repo, number):
        raise AssertionError("le fil ne doit pas etre lu apres le mur")

    monkeypatch.setattr(tq.tapis_fenetre.gh_snapshot, "fetch_issue_comments", faux_fil)
    lec = gh_bulk.Lecture(issues=[{
        "number": 7, "title": "Grain 7", "body": "", "created_at": "2026-11-01T00:00:00Z",
        "updated_at": "2026-11-01T00:00:00Z", "labels": [], "comments_total": 40,
        "comments": []}], prs=[], citations={}, lu_a="2026-11-18T08:00:00Z")
    etats = tapis_rapide.etats(lec, LANE, NOW)
    confirmes, rejetes, echecs, appels = tq.tapis_fil_complet.confirmer(
        etats, lec, LANE, NOW, 45, appels_max=0)
    assert not confirmes
    assert rejetes[0]["code"] == "MUR_EPUISE"


def test_les_ecarts_sont_affiches_avec_leur_code_et_leur_motif():
    """Une exclusion n'est jamais silencieuse : elle porte son code et son motif."""
    claim = {"created_at": "2026-11-17T00:00:00Z", "author": "jsboige",
             "body": "[CLAIMED] lane myia-po-2025:CoursIA-2 -- paths: a/**"}
    lec = gh_bulk.Lecture(issues=[{
        "number": 7, "title": "Grain 7", "body": "", "created_at": "2026-11-01T00:00:00Z",
        "updated_at": "2026-11-01T00:00:00Z", "labels": [], "comments_total": 1,
        "comments": [claim]}],
        prs=[], citations={}, lu_a="2026-11-18T08:00:00Z")
    etats_ = tapis_rapide.etats(lec, LANE, NOW)
    assert etats_[0].ecart == "RECLAMEE"
    assert etats_[0].motif


def test_la_qualification_rejoue_les_memes_regles_que_la_voie_lourde():
    """Les neuf ecarts de `tapis_rapide.etats` sont inchanges : la voie leger
    ne redecide pas, elle ALIMENTE la meme decision sur un grain qualifie."""
    autre = "myia-po-2025:CoursIA-2"
    claim = {"created_at": "2026-11-17T00:00:00Z", "author": "jsboige",
             "body": f"[CLAIMED] lane {autre} -- paths: a/**"}
    lec = gh_bulk.Lecture(issues=[{
        "number": 7, "title": "Grain 7", "body": "", "created_at": "2026-11-01T00:00:00Z",
        "updated_at": "2026-11-01T00:00:00Z", "labels": [], "comments_total": 1,
        "comments": [claim]}],
        prs=[], citations={}, lu_a="2026-11-18T08:00:00Z")
    etats_ = tapis_rapide.etats(lec, LANE, NOW)
    assert etats_[0].ecart is not None, "un claim vivant d'une autre lane ecarte"
    lec2 = gh_bulk.Lecture(issues=[{
        "number": 7, "title": "Grain 7", "body": "", "created_at": "2026-11-01T00:00:00Z",
        "updated_at": "2026-11-01T00:00:00Z", "labels": [], "comments_total": 1,
        "comments": [claim]}],
        prs=[], citations={}, lu_a="2026-11-18T08:00:00Z")
    etats2 = tapis_rapide.etats(lec2, LANE, NOW)
    assert etats2[0].ecart == etats_[0].ecart
    assert etats2[0].motif == etats_[0].motif


# --- la bascule : le tirage par defaut est leger -------------------------------

def test_le_tirage_par_defaut_est_leger(monkeypatch, capsysbinary):
    """Sans `--voie`, le tirage passe par la voie LEGERE.

    Le test le prouve par l'absence : la lecture lourde du pool entier
    (`gh_bulk.lire_tout`) ne doit jamais etre appelee.
    """
    def run_interdite(*a, **k):
        raise AssertionError("la voie lourde ne doit pas lire le pool entier")

    monkeypatch.setattr(gh_bulk, "lire_tout", run_interdite)
    code = tapis_rapide.main(["--lane", LANE, "--json"], run=_run_faux(),
                              maintenant=NOW)
    sortie = json.loads(capsysbinary.readouterr().out.decode("utf-8"))
    assert code == 0
    assert sortie["voie"] == "leger"
    assert sortie["qualification"]["organe"].endswith("tapis_prise_en_charge.py")


def test_un_rejeu_reste_sur_la_voie_lourde(monkeypatch, tmp_path, capsysbinary):
    """Le rejeu `--lecture` est hors ligne : il reste sur la voie lourde,
    seule voie qui sait relire un dossier de lecture."""
    (tmp_path / "issues.json").write_text(json.dumps([{
        "number": 7, "title": "Grain 7", "body": "", "created_at": "2026-11-01T00:00:00Z",
        "updated_at": "2026-11-01T00:00:00Z", "labels": [], "comments_total": 0,
        "comments": []}]), encoding="utf-8")
    (tmp_path / "prs_ouvertes.json").write_text("[]", encoding="utf-8")
    (tmp_path / "meta.json").write_text(json.dumps({"fetched_at": "2026-11-18T08:00:00Z"}),
                                        encoding="utf-8")
    code = tapis_rapide.main(["--lane", LANE, "--lecture", str(tmp_path), "--json"],
                              run=_run_faux(), maintenant=NOW)
    sortie = json.loads(capsysbinary.readouterr().out.decode("utf-8"))
    assert code == 0
    assert "voie" not in sortie, "un rejeu ne porte pas la voie leger"


def test_la_voie_lourde_reste_explicite(monkeypatch, capsysbinary):
    """`--voie lourd` garde l'ancienne lecture : elle est demandee, elle sert."""
    monkeypatch.setattr(gh_bulk, "lire_tout", lambda *a, **k: gh_bulk.Lecture(
        issues=[], prs=[], citations={}, lu_a="2026-11-18T08:00:00Z"))
    monkeypatch.setattr(tapis_leger.tapis_origami, "mesurer", lambda *a, **k: (
        {}, {"active": False, "measured": False, "parked": [], "reason": "test"}))
    code = tapis_rapide.main(["--lane", LANE, "--cache-s", "0", "--json",
                               "--voie", "lourd"], run=_run_faux(), maintenant=NOW)
    assert code == 0
    sortie = json.loads(capsysbinary.readouterr().out.decode("utf-8"))
    assert "voie" not in sortie


def test_la_lecture_incomplete_du_pool_ne_sert_rien(monkeypatch, capsysbinary,
                                                   tmp_path):
    """Sortie 3 : une selection incomplete ne rend aucune liste a moitie.

    Le repli chronologique (I2) ne peut rien servir sans **cache local** : le
    test le neutralise, sinon il dependrait du cache de la machine -- un poste
    qui a deja tire verrait le repli servir, et la sortie 3 ne viendrait
    jamais.
    """
    def run_panne(argv, timeout):
        raise subprocess.TimeoutExpired(argv, timeout)

    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    code = tapis_rapide.main(["--lane", LANE], run=run_panne, maintenant=NOW)
    capture = capsysbinary.readouterr()
    assert code == 3
    assert "Lecture incomplete" in capture.err.decode("utf-8")


# --- la lecture ciblee des issues nommees (gh_issues) --------------------------

def test_la_lecture_ciblee_porte_le_corps_des_issues_nommees():
    """Une seule porte pour tous les lecteurs cibles : le corps rendu est
    celui de l'issue demandee, et rien d'autre n'est lu."""
    lues = gh_issues.lire_champs(_run_faux(), gh_bulk.DEPOT_GH, [7], "number title body",
                                 "corps")
    assert set(lues) == {7}
    assert lues[7]["body"] == "Part of #7"


def test_la_lecture_ciblee_leve_sur_une_reponse_illisible():
    """Une reponse illisible ne rend pas une liste a moitie : elle leve."""
    def run_illisible(argv, timeout):
        return "pas du json"

    with pytest.raises(gh_bulk.LectureIncomplete) as exc:
        gh_issues.lire_champs(run_illisible, gh_bulk.DEPOT_GH, [7], "number", "corps")
    assert exc.value.lecture == "corps"


def test_la_lecture_ciblee_nomme_une_issue_absente():
    """Une issue ABSENTE de la reponse sort avec un verdict : `None`.

    Avant, le numero disparaisait du resultat sans que personne sache
    pourquoi -- il disparaisait aussi du classement (revue du 19/11)."""
    def run_absente(argv, timeout):
        return json.dumps({"data": {"repository": {"i0": None}}})

    assert gh_issues.lire_champs(run_absente, gh_bulk.DEPOT_GH, [7], "number",
                                  "corps") == {7: None}


def test_la_lecture_ciblee_refuse_un_alias_absent_de_la_reponse():
    """Un alias ABSENT de la reponse n'est pas une absence : la reponse est
    incomplete, et le lot est refuse (fail-CLOSED)."""
    def run_tronque(argv, timeout):
        return json.dumps({"data": {"repository": {}}})

    with pytest.raises(gh_bulk.LectureIncomplete) as exc:
        gh_issues.lire_champs(run_tronque, gh_bulk.DEPOT_GH, [7], "number", "corps")
    assert exc.value.lecture == "corps"


# --- la requalification separe la trace du travail (revue du 19/11) -----------

def _issue(n: int, labels=(), commentaires: int = 0) -> dict:
    return {"number": n, "title": f"Grain {n}", "body": "",
            "created_at": "2026-11-01T00:00:00Z",
            "comments": [], "comments_total": commentaires,
            "labels": list(labels)}


def test_le_label_d_urne_ne_prouve_pas_la_livraison(monkeypatch):
    """Un label `candidate-delivered` est une ROUTE, pas une preuve.

    Il dit que l'issue est dans l'urne de cloture du coordinateur et de
    l'adjoint ; il ne dit pas que la tranche est livree. Retirer le grain sur
    cette seule foi, ce serait heriter d'une exclusion que personne n'a
    prouvee : la lane qui le rencontre verifie la preuve sur l'artefact, puis
    rend la main (#15069)."""
    def faux_qualifier(run, depot, numeros=None):
        return {7: _issue(7, labels=["candidate-delivered"])}

    monkeypatch.setattr(tq.tapis_lot.gh_selection, "qualifier", faux_qualifier)
    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [], _run_faux([]))
    assert [e.numero for e in servis] == [7], "le label ne retire pas le grain"
    assert any("urne" in n for n in servis[0].notes), "l'urne reste dite"
    assert 7 not in ecartees, "le label n'est pas une exclusion"


def test_une_pr_ouverte_qui_cite_est_un_signal_pas_un_verdict(monkeypatch):
    """Une PR ouverte qui cite l'issue est une couverture, pas une livraison.

    Le verdict `COUVERTE` retirait le grain sur cette seule foi. Dans la
    requalification, la couverture reste DITE -- en note -- et le grain reste
    servable."""
    def faux_qualifier(run, depot, numeros=None):
        return {7: _issue(7)}

    monkeypatch.setattr(tq.tapis_lot.gh_selection, "qualifier", faux_qualifier)
    prs = [{"number": 99, "title": "Fix(coordination): un ajustement #7",
            "body": "Grain: LIGHT/guard -- lane myia-po-2025:CoursIA-2\n\nRefs #7"}]
    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, prs, _run_faux([]))
    assert [e.numero for e in servis] == [7], "une couverture ne retire pas le grain"
    assert any("#99" in n for n in servis[0].notes), "la couverture reste dite"


def test_la_prise_en_charge_ne_lit_plus_les_citations(monkeypatch):
    """La requalification decide sur le FIL : elle ne relit plus `origin/main`.

    Les citations de commit sont une activite *autour* de l'issue ; elles ne
    prouvent aucune livraison, et leur lecture coutait un `git log` a chaque
    prise en charge (revue du 19/11, #27242)."""
    from coordination import tapis_prise_en_charge as tpe

    def interdiction(*args, **kwargs):
        raise AssertionError("les citations ne doivent pas etre lues")

    def faux_qualifier(run, depot, numeros=None):
        return {7: _issue(7)}

    monkeypatch.setattr(tpe.gh_bulk, "lire_citations_mergees", interdiction)
    monkeypatch.setattr(tpe.gh_bulk, "lire_prs_ouvertes", lambda run: [])
    monkeypatch.setattr(tq.tapis_lot.gh_selection, "qualifier", faux_qualifier)
    rapport = tpe.main(["--issue", "7", "--lane", LANE], run=_run_faux([]))
    assert rapport == 0


# --- L'ANCRE : elle n'avance que sur un verdict TERMINAL (peer, 19/11) ------

def test_un_tirage_seul_ne_fait_pas_avancer_l_ancre(tmp_path, monkeypatch):
    """Le tirage PROPOSE ; il ne qualifie pas. Un tirage sans action laisse
    l'ancre en place.

    Avancer l'ancre a la PROPOSITION ferait declarer visite un numero que
    personne n'a decide : le tour se fermerait sur une couverture qui n'a pas
    eu lieu (peer, 19/11)."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "g", Path("."),
                                       _run_faux(nb=6))
    assert code == 0
    etat = tapis_ancre.lire(LANE)
    assert etat["grains"]["ancre"] is None,         "un tirage sans action ne fait pas avancer l'ancre"
    assert etat["grains"]["attente"], "les numeros tires restent EN ATTENTE"
    assert all(not v for v in etat["grains"]["attente"].values()),         "un numero propose n'est pas un numero qualifie"


def test_un_lot_partiel_ne_fige_pas_la_couverture(tmp_path, monkeypatch):
    """Un numero ILLISIBLE n'est pas un verdict : il est PARKE.

    Le lot lit #7 et #9 ; le #8 est ABSENT de la reponse. L'echec de lecture
    n'est pas une decision : le #8 n'est donc pas acquitte, mais il ne FIGE
    pas le curseur -- la couverture continue sur #9, et le #8 est re-servi au
    tour suivant (contre-exemple du 19/11)."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))

    def faux_qualifier(run, depot, numeros=None):
        return {7: _issue(7), 8: None, 9: _issue(9)}

    monkeypatch.setattr(tq.tapis_lot.gh_selection, "qualifier", faux_qualifier)
    tapis_ancre.proposer(LANE, "grains", [7, 8, 9])
    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7, 8, 9], LANE, NOW, 45, [], _run_faux([]))
    assert [e.numero for e in servis] == [7, 9], "les numeros lus sont qualifies"
    assert ecartees[8]["code"] == "ABSENT", "le numero absent sort avec son code"
    etat = tapis_ancre.lire(LANE)
    assert etat["grains"]["ancre"] == 9, "la couverture continue malgre la lecture en echec"
    assert 8 in etat["grains"]["inconnus"], "le #8 est PARKE, pas perdu"
    assert etat["grains"]["inconnus"][8]["code"] == "ABSENT", "il porte son code"
    # Le #8 est decide plus tard : il quitte le parc des inconnus.
    tapis_verdict.avancer(LANE, {}, {8: {"numero": 8, "code": "GEL"}})
    assert 8 not in tapis_ancre.lire(LANE)["grains"]["inconnus"]


def test_un_refus_de_lecture_n_est_pas_un_verdict():
    """Les codes de REFUS ne sont pas terminaux : ils refusent la lecture."""
    refus = {"numero": 8, "code": "FIL_ILLISIBLE"}
    assert 8 not in tapis_verdict.terminaux({}, {8: refus})
    assert 8 not in tapis_verdict.terminaux({}, {8: {"numero": 8,
                                                       "code": "ABSENT"}})
    assert 8 in tapis_verdict.terminaux({}, {8: {"numero": 8, "code": "GEL"}})
    assert 9 in tapis_verdict.terminaux({9: object()}, {})
    assert 8 in tapis_verdict.inconnus({8: refus}), "le refus est PARKÉ"
    assert 8 not in tapis_verdict.inconnus({8: {"numero": 8, "code": "GEL"}})


# --- LE TOUR QUI BOUCLE (contre-exemple execute du peer, 19/11) --------------

def _tour(nums: list[int], taille: int) -> list[list[int]]:
    """Un tour complet : selection (tirage) puis qualification (verdict)."""
    vus: list[list[int]] = []
    for _ in range(len(nums) // taille):
        ancre = tapis_ancre.lire(LANE)["grains"]["ancre"]
        tranche = tapis_ancre.tranche(nums, ancre, taille, 0)
        tapis_ancre.proposer(LANE, "grains", tranche)
        tapis_ancre.avancer(LANE, set(tranche))
        vus.append(tranche)
    return vus


def test_le_tour_qui_boucle_est_un_tour_de_plus(tmp_path, monkeypatch):
    """Le contre-exemple du peer (19/11) : pool 1..6, taille 2.

    Apres le tour complet, le curseur etait FIGE au plus grand numero et la
    tranche [1, 2] revenait a chaque vague. Un tour qui boucle est un tour
    de PLUS : le second tour couvre le pool, et le compteur de tour avance.
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    nums = list(range(1, 7))
    assert _tour(nums, 2) == [[1, 2], [3, 4], [5, 6]]
    assert _tour(nums, 2) == [[1, 2], [3, 4], [5, 6]], \
        "le second tour couvre le pool au lieu de resservir [1, 2]"
    assert tapis_ancre.tour_de(tapis_ancre.lire(LANE), "grains") == 1, \
        "un tour de plus est compte"


def test_une_tranche_peut_chevaucher_la_fin_du_pool():
    """La tranche est cyclique : elle passe le dernier numero et revient."""
    nums = list(range(1, 7))
    assert tapis_ancre.tranche(nums, 4, 5, 0) == [5, 6, 1, 2, 3], \
        "la tranche chevauche la fin du pool"


def test_un_pending_de_tete_qui_se_ferme_laisse_passer_le_curseur(tmp_path, monkeypatch):
    """Le pending de tete attend sa decision ; quand elle tombe, le curseur
    passe -- et les numeros derriere lui aussi."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    tapis_ancre.proposer(LANE, "grains", [5, 6, 7])
    assert tapis_ancre.lire(LANE)["grains"]["ancre"] is None, \
        "rien n'est decide : le curseur bouge pas"
    tapis_verdict.avancer(LANE, {5: object()}, {})
    assert tapis_ancre.lire(LANE)["grains"]["ancre"] == 5, \
        "le pending de tete qui se ferme libere le curseur"
    tapis_verdict.avancer(LANE, {6: object(), 7: object()}, {})
    assert tapis_ancre.lire(LANE)["grains"]["ancre"] == 7, \
        "les numeros derriere sont couverts"


def test_un_pending_de_tete_illisible_ne_gele_pas_les_autres(tmp_path, monkeypatch):
    """Le pending de tete qui reste ILLISIBLE ne fige pas les autres.

    Le #5 ne sera jamais decide ; il est PARKE. Mais la couverture continue :
    #6 et #7 sont servis, et le #5 revient au tour suivant.
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    tapis_ancre.proposer(LANE, "grains", [5, 6, 7])
    tapis_verdict.avancer(LANE, {6: object(), 7: object()},
                           {5: {"numero": 5, "code": "FIL_ILLISIBLE"}})
    etat = tapis_ancre.lire(LANE)
    assert etat["grains"]["ancre"] == 7, "la couverture des autres n'est pas retiree"
    assert 5 in etat["grains"]["inconnus"], "le #5 est PARKE, il revient"
    assert 5 not in etat["grains"]["attente"], "un PARKÉ n'est plus en attente"
