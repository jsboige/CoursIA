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
   perdu en silence ;
4. seule une **forme de cloture** (`Closes #N`) ou le numero du tag `Grain:`
   tient l'issue : `Part of #N` designe un parent, pas un grain servi ;
5. le rendu est **plafonne** (une liste de 284 lignes n'est pas un rapport) et
   les lanes gerantes recoivent une section **courte** a la place.

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
SECRETAIRE = "myia-po-2028:CoursIA-3"


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
    prs = [_pr(99, "Grain: LIGHT/guard -- lane myia-po-2025:CoursIA-2\n\nCloses #7")]
    marques = tapis_occupation.marques([], prs, LANE)
    assert marques == {7: "occupee:#99"}


def test_la_pr_de_la_lane_ne_l_occupe_pas():
    """C'est la lane de la PR qui porte l'issue au merge (P0)."""
    prs = [_pr(99, "Grain: MED/lean -- lane myia-ai-01:CoursIA-2\n\nCloses #7")]
    assert tapis_occupation.marques([], prs, LANE) == {}


def test_une_pr_sans_tag_de_lane_est_traitee_comme_une_autre():
    """Le login est partage : sans tag `lane`, la PR n'est attribuable a
    personne -- elle est donc traitee comme celle d'une autre lane."""
    prs = [_pr(99, "Closes #7")]
    marques = tapis_occupation.marques([], prs, LANE)
    assert marques == {7: "occupee:#99"}


def test_l_urne_lemporte_sur_l_occupation():
    """L'urne est la classe la plus dure : elle prime sur la marque d'occupation."""
    metas = [{"number": 7, "labels": ["candidate-delivered"]}]
    prs = [_pr(99, "Grain: LIGHT/guard -- lane myia-po-2025:CoursIA-2\n\nCloses #7")]
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
    """Le coordinateur, l'adjoint et le secretaire arbitrent : ils ne perdent
    aucun grain. Le secretaire **ferme** l'urne (Q167 b) : sans lui, l'urne
    de cloture n'avait pas de porteur."""
    grains = [_Etat(7)]
    occupation = {7: "urne"}
    for gerante in (COORD, ADJOINT, SECRETAIRE):
        restants, _, exclus = tapis_occupation.retirer(grains, [], occupation, gerante)
        assert [e.numero for e in restants] == [7]
        assert exclus == []


def test_le_secretaire_est_une_lane_gerante():
    """Le secretaire est dans `LANES_PRIVILEGIEES` : il arbitre l'urne au
    lieu de la perdre (Q167 b)."""
    assert tapis_occupation.privilege(SECRETAIRE)
    assert "secretaire" in tapis_occupation.NOTE_URNE
    assert "secretaire" in tapis_occupation.motif("urne")


# --- LE TIRAGE REEL (voie legere, faux `run`) ------------------------------


def test_la_voie_legere_ecarte_l_urne_et_l_occupee_du_tirage():
    """La voie legere : l'urne et l'issue occupee ne sont pas dans la tete,
    et le rapport les affiche (une exclusion n'est jamais silencieuse)."""
    nodes = [_noeud(7, labels=["candidate-delivered"]),
             _noeud(8),
             _noeud(9)]
    prs = [_pr(99, "Grain: LIGHT/guard -- lane myia-po-2025:CoursIA-2\n\nCloses #8")]
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
    prs = [_pr(99, "Grain: MED/lean -- lane myia-ai-01:CoursIA-2\n\nCloses #8")]
    classe = tapis_leger.classer(LANE, NOW, 45, "graine", Path(__file__).resolve().parents[2],
                                  _run_faux(nodes, prs))
    tete = {e.numero for e in classe["grains"]} | {e.numero for e in classe["conteneurs"]}
    assert 8 in tete, "la lane garde l'issue de sa propre PR"
    assert classe["occupation"]["exclus"] == []


# --- QUELLE REFERENCE TIENT LE GRAIN (reserve du coordinateur, 22/11) ------
#
# Une PR qui **cite** une issue ne la tient pas : seule la forme sure de
# `git-workflow.md` (`Closes #N`) -- ou le numero du tag `Grain:` -- la tient.
# `Part of #N`, `Refs #N` et `See #N` designent un parent, un contexte ou une
# issue partagee : les compter marquait l'umbrella OCCUPEE pour TOUTE la
# flotte (mesure du 22/11 sur le corps de #28096 : `Part of #24823`).


def test_part_of_ne_tient_pas_le_grain():
    """`Part of #N` nomme un parent : l'umbrella reste au pool."""
    prs = [_pr(99, "Grain: DEEP/lean -- lane myia-po-2025:CoursIA-2 "
                   "-- prev: MED/lean #25940\n\nPart of #24823")]
    marques = tapis_occupation.marques([], prs, LANE)
    assert 24823 not in marques, "un parent cite n'est pas un grain occupe"
    # Le numero porte par le tag `Grain:` compte (regle du coordinateur).
    # Ici c'est le numero de la PR *precedente* (`prev:`) : PR et issues
    # partagent un compteur, donc il ne designe jamais une issue ouverte --
    # aucun grain du pool n'est ecarte par lui.
    assert 25940 in marques


def test_la_forme_de_cloture_tient_le_grain():
    """`Closes #N` tient le grain : c'est la forme qui ferme l'issue."""
    prs = [_pr(99, "Grain: DEEP/lean -- lane myia-po-2025:CoursIA-2\n\nCloses #24823")]
    marques = tapis_occupation.marques([], prs, LANE)
    assert marques == {24823: "occupee:#99"}


def test_le_numero_du_tag_grain_est_une_reference_legitime():
    """Le tag `Grain:` nomme le grain servi : son numero compte."""
    refs = tapis_occupation.refs_legitimes(
        "Grain: DEEP/lean -- lane myia-po-2025:CoursIA-2 -- prev: MED/lean #25940")
    assert refs == {25940}


def test_refs_legitimes_ignore_les_references_structurelles():
    """Une seule forme compte : les references structurelles ne tiennent rien."""
    texte = ("Grain: MED/docs -- lane myia-po-2025:CoursIA-2\n\n"
             "Part of #24823\nSee #12345\nRefs #999\nFixes #777")
    assert tapis_occupation.refs_legitimes(texte) == {777}


def test_le_mot_de_cloture_doit_preceder_le_numero():
    """`Fix(ci,#22937)` n'est pas une forme de cloture : le mot de cloture
    doit preceder immediatement le numero (`git-workflow.md`)."""
    assert tapis_occupation.refs_legitimes("Fix(ci,#22937): un titre") == set()


# --- LE RENDU : PLAFONNE, ET COURT POUR LES LANES GERANTES ------------------


def test_le_rendu_des_exclusions_est_plafonne():
    """Une exclusion muette est interdite ; une liste de 284 lignes n'est pas
    un rapport. Au-dela du plafond, le **compte** reste affiche."""
    exclus = [{"numero": n, "marque": "urne",
               "motif": tapis_occupation.motif("urne")}
              for n in range(100, 100 + 40)]
    lignes = tapis_occupation.rendre_exclus(exclus)
    assert len(lignes) == tapis_occupation.RENDU_MAX + 1
    assert "28 autre(s) exclusion(s)" in lignes[-1]
    assert lignes[-1].strip().startswith("...")


def test_le_resume_est_court_pour_les_lanes_gerantes():
    """Les lanes gerantes ne perdent aucun grain : elles recoivent une
    section courte (ce qui est a l'urne, ce qui est occupe)."""
    occupation = {7: "urne", 8: "occupee:#99"}
    lignes = tapis_occupation.resume(occupation)
    assert len(lignes) == 2
    assert "urne (1)" in lignes[0] and "#7" in lignes[0]
    assert "occupee (1)" in lignes[1] and "#8 (#99)" in lignes[1]


def test_la_voie_legere_donne_le_resume_aux_lanes_gerantes():
    """La voie legere : la lane gerante garde la tete ET recoit le resume."""
    nodes = [_noeud(7, labels=["candidate-delivered"]), _noeud(8)]
    prs = [_pr(99, "Grain: LIGHT/guard -- lane myia-po-2025:CoursIA-2\n\nCloses #8")]
    depot = Path(__file__).resolve().parents[2]
    classe = tapis_leger.classer(SECRETAIRE, NOW, 45, "graine", depot,
                                 _run_faux(nodes, prs))
    tete = {e.numero for e in classe["grains"]} | {e.numero for e in classe["conteneurs"]}
    assert {7, 8} <= tete, "le secretaire ne perd aucun grain"
    assert classe["occupation"]["exclus"] == []
    assert classe["occupation"]["resume"], "le resume dit ce qui est a l'urne"
