"""Tests de la voie LEGERE du tirage (`coordination/tapis_leger.py`) -- #27225.

La bascule a trois garanties, et chacune se verifie ici :

1. le **classement** ne lit que des metadonnees -- ni corps, ni commentaires ;
2. la **qualification** du grain servi se fait sur son **FIL COMPLET**
   (l'organe REST `gh_snapshot`), pas sur la fenetre des 12 derniers
   commentaires de la lecture groupee ;
3. le tirage **par defaut** est leger ; la voie lourde reste accessible
   (`--voie lourd`) et le rejeu `--lecture` y reste.

Aucun test ne touche le reseau : `run` est un faux, le fil est monkeypatche.
"""
import json
import re
import subprocess
import sys
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk, gh_issues, gh_selection, tapis_leger, tapis_rapide
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


def _page_corps(n: int) -> str:
    node = {"number": n, "title": f"Grain {n}", "body": f"Part of #{n}",
            "createdAt": "2026-11-01T00:00:00Z", "updatedAt": "2026-11-01T00:00:00Z",
            "labels": {"nodes": []}}
    return json.dumps({"data": {"repository": {"i0": node}}})


def _page_corps_multiples(requete: str) -> str:
    """La reponse au lot : un alias par issue demandee (`i0`, `i1`, ...)."""
    alias: dict[str, dict] = {}
    for k, n in re.findall(r"i(\d+):\s*issue\(number:(\d+)\)", requete):
        alias[f"i{k}"] = {"number": int(n), "title": f"Grain {n}",
                          "body": f"Part of #{n}", "createdAt": "2026-11-01T00:00:00Z",
                          "updatedAt": "2026-11-01T00:00:00Z", "labels": {"nodes": []}}
    return json.dumps({"data": {"repository": alias}})


def _run_faux(appels: list[list[str]] | None = None, nb: int = 2):
    """Un faux `run` : metadonnees, corps, citations (vide) et PRs (vides)."""
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
            return _page_corps_multiples(requete)
        if "graphql" in requete:
            return _page_metas([_noeud(7 + k) for k in range(nb)])
        if argv[0] == "git":
            return ""  # aucune citation : personne n'a visite ces issues
        return "[]"  # aucune PR ouverte

    return run


# --- la qualification lit le FIL COMPLET --------------------------------------

def test_la_qualification_lit_le_fil_complet(monkeypatch):
    """Le fil qualifie n'est PAS la fenetre des 12 derniers commentaires.

    C'est la condition de la bascule : le marqueur qui ecarte un grain peut
    etre plus vieux que la fenetre (constat de #27179).
    """
    vus: list[int] = []

    def faux_fil(repo, number):
        vus.append(number)
        return [{"createdAt": f"2026-11-0{k + 1}T00:00:00Z",
                 "author": {"login": "jsboige"},
                 "body": f"[CLAIMED] lane autre -- commentaire {k}"} for k in range(40)]

    monkeypatch.setattr(tq.gh_snapshot, "fetch_issue_comments", faux_fil)
    issues, echecs = tq.qualifier_candidats([7], _run_faux())
    assert not echecs
    qualifie = issues[0]
    assert len(qualifie["comments"]) == 40, "le fil doit etre complet, pas une fenetre"
    assert qualifie["comments_total"] == 40
    assert vus == [7]


def test_un_fil_illisible_ecarte_le_grain_sans_bloquer_le_tirage(monkeypatch):
    """Un fil illisible ne bloque pas le tirage : le grain est absent de la
    liste qualifiee, le reste du tirage continue (fail-OPEN)."""
    def faux_fil(repo, number):
        raise RuntimeError("fil indisponible")

    monkeypatch.setattr(tq.gh_snapshot, "fetch_issue_comments", faux_fil)
    issues, echecs = tq.qualifier_candidats([7], _run_faux())
    assert issues == [] and echecs == [7]


def test_la_requete_du_corps_est_bien_formee():
    """La requete du corps doit etre ACCEPTEE par GraphQL : ses accolades
    sont equilibrees, et chaque alias porte une issue.

    Defaut deja mesure : un bloc de champs qui se ferme lui-meme produit une
    accolade de trop -- l'erreur n'apparait qu'aupres de GitHub, en
    `Expected one of SCHEMA, SCALAR, TYPE...`.
    """
    appels: list[list[str]] = []
    tq.lire_corps(_run_faux(appels), gh_bulk.DEPOT_GH, [7, 8, 9])
    requete = " ".join(appels[0])
    assert requete.count("{") == requete.count("}")
    assert requete.count("issue(number:") == 3


def test_le_classement_ne_lit_que_des_metadonnees():
    """Le classement ne demande ni corps ni commentaires : la requete le dit."""
    appels: list[list[str]] = []
    gh_selection.lire_metadonnees_issues(_run_faux(appels))
    requete = " ".join(appels[0])
    assert "body" not in requete and "comments" not in requete


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


def test_la_lecture_ciblee_ne_devine_pas_une_issue_absente():
    """Une issue absente de la reponse est absente du resultat."""
    def run_absente(argv, timeout):
        return json.dumps({"data": {"repository": {}}})

    assert gh_issues.lire_champs(run_absente, gh_bulk.DEPOT_GH, [7], "number",
                                  "corps") == {}


def test_le_plafond_de_qualification_suit_le_nombre_de_grains_demandes(monkeypatch):
    """La ceinture du coordinateur (`--grains 60`) doit rendre 60 grains : le
    plafond de qualification ne peut pas etre un nombre fixe, sinon la bascule
    casserait l'usage le plus large du tapis (le board du coordinateur)."""
    monkeypatch.setattr(tq.gh_snapshot, "fetch_issue_comments",
                        lambda repo, number: [])
    rapport, code = tapis_leger.tirage(LANE, 20, NOW, 45, "g", Path("."),
                                       _run_faux(nb=30))
    assert code == 0
    assert rapport["qualification"]["candidats"] == 20
    assert len(rapport["grains"]) == 20


def test_une_vague_entierement_ecartee_ouvre_la_suivante(monkeypatch):
    """Les neuf ecarts peuvent ecarter TOUS les premiers candidats : la
    qualification ouvre alors la vague suivante.

    Servir 0 grain alors que le pool en contient serait un echec de methode,
    pas un pool vide (mesure du 2026-11-18).
    """
    autre = "myia-po-2025:CoursIA-2"

    vus: list[int] = []

    def faux_fil(repo, number):
        # La premiere VAGUE (12 candidats, dans l'ordre de la rotation) est
        # occupee par une autre lane ; les suivants sont libres.
        vus.append(number)
        if len(vus) <= 12:
            return [{"created_at": "2026-11-17T00:00:00Z", "author": "jsboige",
                     "body": f"[CLAIMED] lane {autre} -- paths: a/**"}]
        return []

    monkeypatch.setattr(tq.gh_snapshot, "fetch_issue_comments", faux_fil)
    rapport, code = tapis_leger.tirage(LANE, 2, NOW, 45, "g", Path("."),
                                       _run_faux(nb=30))
    assert code == 0
    assert rapport["qualification"]["candidats"] > 12, "la vague suivante a ete ouverte"
    assert len(rapport["grains"]) == 2
    assert rapport["grains"][0]["numero"] == vus[12]


# --- la bascule : le tirage par defaut est leger -------------------------------

def test_le_tirage_par_defaut_est_leger(monkeypatch, capsysbinary):
    """Sans `--voie`, le tirage passe par la voie LEGERE.

    Le test le prouve par l'absence : la lecture lourde du pool entier
    (`gh_bulk.lire_tout`) ne doit jamais etre appelee.
    """
    def run_interdite(*a, **k):
        raise AssertionError("la voie lourde ne doit pas lire le pool entier")

    monkeypatch.setattr(gh_bulk, "lire_tout", run_interdite)
    monkeypatch.setattr(tq.gh_snapshot, "fetch_issue_comments",
                        lambda repo, number: [])
    code = tapis_rapide.main(["--lane", LANE, "--json"], run=_run_faux(),
                              maintenant=NOW)
    sortie = json.loads(capsysbinary.readouterr().out.decode("utf-8"))
    assert code == 0
    assert sortie["voie"] == "leger"
    assert sortie["qualification"]["fil"] == "complet"


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
    monkeypatch.setattr(tq.gh_snapshot, "fetch_issue_comments",
                        lambda repo, number: [])
    code = tapis_rapide.main(["--lane", LANE, "--lecture", str(tmp_path), "--json"],
                              run=_run_faux(), maintenant=NOW)
    sortie = json.loads(capsysbinary.readouterr().out.decode("utf-8"))
    assert code == 0
    assert "voie" not in sortie, "un rejeu ne porte pas la voie leger"


def test_la_voie_lourde_restexplicite(monkeypatch, capsysbinary):
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


def test_la_lecture_incomplete_du_pool_ne_sert_rien(monkeypatch, capsysbinary):
    """Sortie 3 : une selection incomplete ne rend aucune liste a moitie."""
    def run_panne(argv, timeout):
        raise subprocess.TimeoutExpired(argv, timeout)

    monkeypatch.setattr(tq.gh_snapshot, "fetch_issue_comments",
                        lambda repo, number: [])
    code = tapis_rapide.main(["--lane", LANE], run=run_panne, maintenant=NOW)
    capture = capsysbinary.readouterr()
    assert code == 3
    assert "Lecture incomplete" in capture.err.decode("utf-8")


# --- les regles de decision sont les memes qu'en voie lourde --------------------

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
    qualifie = tq.qualifier(7, {"title": "Grain 7", "body": "",
                                         "created_at": "2026-11-01T00:00:00Z",
                                         "updated_at": "2026-11-01T00:00:00Z",
                                         "labels": []},
                                     [claim])
    lec2 = gh_bulk.Lecture(issues=[qualifie], prs=[], citations={},
                            lu_a="2026-11-18T08:00:00Z")
    etats2 = tapis_rapide.etats(lec2, LANE, NOW)
    assert etats2[0].ecart == etats_[0].ecart
    assert etats2[0].motif == etats_[0].motif
