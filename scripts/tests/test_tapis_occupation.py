"""Tests de l'OCCUPATION d'un grain (`coordination/tapis_occupation.py`).

TASK c0021 du coordinateur (22/11) : dans la sortie `tapis_rapide.py --lane
<worker>`, ecarter (ou marquer `urne` / `occupee:#PR`) les issues
`candidate-delivered` et celles qu'une PR ouverte occupe deja.

Ce que ces tests verrouillent :

1. les deux marques se decident sur les **metadonnees seules** (labels + PRs
   ouvertes) -- aucun appel reseau de plus dans le tirage ;
2. une lane worker ne sert ni l'urne ni l'issue occupee ; la lane de la PR et
   les lanes qui **gerent** l'urne les gardent ;
3. l'exclusion est **affichee** (numero, marque, motif) : jamais un grain
   perdu en silence.

Aucun test ne touche le reseau : `run` est un faux.
"""
import json
import sys
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_leger, tapis_occupation

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 22, 16, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"
COORD = "myia-ai-01:CoursIA"
ADJOINT = "myia-po-2025:CoursIA-2"


def _noeud(n: int, titre: str = "", labels=()) -> dict:
    return {"number": n, "title": titre or f"Grain {n}",
            "createdAt": "2026-11-01T00:00:00Z", "updatedAt": "2026-11-01T00:00:00Z",
            "labels": {"nodes": [{"name": lab} for lab in labels]}}


def _pr(numero: int, corps: str) -> dict:
    return {"number": numero, "title": f"PR {numero}", "body": corps,
            "created_at": "2026-11-20T00:00:00Z", "updated_at": "2026-11-20T00:00:00Z"}


def _run_faux(nodes: list[dict], prs: list[dict]):
    """Un faux `run` : metadonnees (GraphQL) et PRs ouvertes (REST)."""
    def run(argv, timeout):
        requete = " ".join(argv)
        if "graphql" in requete:
            return json.dumps({"data": {"repository": {"issues": {
                "pageInfo": {"hasNextPage": False, "endCursor": "c"},
                "nodes": nodes}}}})
        if argv[0] == "git":
            return ""
        return json.dumps(prs)

    return run


# --- LES DEUX MARQUES, sur metadonnees seules ------------------------------


def test_l_urne_est_marquee_par_son_label():
    """Le label `candidate-delivered` route l'issue vers l'urne."""
    metas = [{"number": 7, "labels": ["candidate-delivered"]},
             {"number": 8, "labels": ["autre"]}]
    marques = tapis_occupation.marques(metas, [], LANE)
    assert marques == {7: "urne"}
    assert 8 not in marques, "une issue sans label n'est pas a l'urne"


def test_une_pr_ouverte_d_une_autre_lane_occupe_le_grain():
    """La PR qui cite l'issue la tient : la marque nomme la PR."""
    prs = [_pr(99, "Grain: LIGHT/guard -- lane myia-po-2025:CoursIA-2\n\nRefs #7")]
    marques = tapis_occupation.marques([], prs, LANE)
    assert marques == {7: "occupee:#99"}


def test_la_pr_de_la_lane_ne_l_occupe_pas():
    """C'est la lane de la PR qui porte l'issue au merge (P0)."""
    prs = [_pr(99, "Grain: MED/lean -- lane myia-ai-01:CoursIA-2\n\nRefs #7")]
    assert tapis_occupation.marques([], prs, LANE) == {}


def test_une_pr_sans_tag_de_lane_est_traitee_comme_une_autre():
    """Le login est partage : sans tag `lane`, la PR n'est attribuable a
    personne -- elle est donc traitee comme celle d'une autre lane."""
    prs = [_pr(99, "Refs #7")]
    marques = tapis_occupation.marques([], prs, LANE)
    assert marques == {7: "occupee:#99"}


def test_l_urne_lemporte_sur_l_occupation():
    """L'urne est la classe la plus dure : elle prime sur la marque d'occupation."""
    metas = [{"number": 7, "labels": ["candidate-delivered"]}]
    prs = [_pr(99, "Grain: LIGHT/guard -- lane myia-po-2025:CoursIA-2\n\nRefs #7")]
    assert tapis_occupation.marques(metas, prs, LANE) == {7: "urne"}


# --- LE RETRAIT DU TIRAGE --------------------------------------------------


class _Etat:
    def __init__(self, numero: int):
        self.numero = numero


def test_le_tirage_ecarte_l_urne_et_l_occupee():
    """Les deux marques sortent de la tete, et l'exclusion est affichee."""
    grains = [_Etat(7), _Etat(8), _Etat(9)]
    conteneurs = [_Etat(10)]
    occupation = {7: "urne", 8: "occupee:#99"}
    restants, conts, exclus = tapis_occupation.retirer(
        grains, conteneurs, occupation, LANE)
    assert [e.numero for e in restants] == [9]
    assert [e.numero for e in conts] == [10]
    assert [e["numero"] for e in exclus] == [7, 8]
    assert exclus[0]["marque"] == "urne" and "urne" in exclus[0]["motif"]
    assert exclus[1]["marque"] == "occupee:#99" and "#99" in exclus[1]["motif"]


def test_les_lanes_gerantes_gardent_la_tete():
    """Le coordinateur et l'adjoint arbitrent : ils ne perdent aucun grain."""
    grains = [_Etat(7)]
    occupation = {7: "urne"}
    for gerante in (COORD, ADJOINT):
        restants, _, exclus = tapis_occupation.retirer(grains, [], occupation, gerante)
        assert [e.numero for e in restants] == [7]
        assert exclus == []


# --- LE TIRAGE REEL (voie legere, faux `run`) ------------------------------


def test_la_voie_legere_ecarte_l_urne_et_l_occupee_du_tirage():
    """La voie legere : l'urne et l'issue occupee ne sont pas dans la tete,
    et le rapport les affiche (une exclusion n'est jamais silencieuse)."""
    nodes = [_noeud(7, labels=["candidate-delivered"]),
             _noeud(8),
             _noeud(9)]
    prs = [_pr(99, "Grain: LIGHT/guard -- lane myia-po-2025:CoursIA-2\n\nRefs #8")]
    classe = tapis_leger.classer(LANE, NOW, 45, "graine", Path(__file__).resolve().parents[2],
                                  _run_faux(nodes, prs))
    tete = {e.numero for e in classe["grains"]} | {e.numero for e in classe["conteneurs"]}
    assert 7 not in tete, "l'urne n'est pas dans la tete"
    assert 8 not in tete, "l'issue occupee n'est pas dans la tete"
    exclus = classe["occupation"]["exclus"]
    assert {e["numero"] for e in exclus} == {7, 8}
    assert all(e["motif"] for e in exclus), "chaque exclusion porte son motif"


def test_la_voie_legere_garde_la_issue_de_la_lane():
    """La PR de la lane : l'issue reste dans la tete (P0)."""
    nodes = [_noeud(8)]
    prs = [_pr(99, "Grain: MED/lean -- lane myia-ai-01:CoursIA-2\n\nRefs #8")]
    classe = tapis_leger.classer(LANE, NOW, 45, "graine", Path(__file__).resolve().parents[2],
                                  _run_faux(nodes, prs))
    tete = {e.numero for e in classe["grains"]} | {e.numero for e in classe["conteneurs"]}
    assert 8 in tete, "la lane garde l'issue de sa propre PR"
    assert classe["occupation"]["exclus"] == []
