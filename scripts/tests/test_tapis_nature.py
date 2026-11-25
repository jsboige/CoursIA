"""Tests de la NATURE d'un grain (`coordination/tapis_nature.py`).

Dispatch `c0035b` (24/11, coordinateur `myia-ai-01:CoursIA`) : le tirage
leger d'une lane worker servait des issues de **harnais** et de
**coordination**, et la tete du tirage etait une **FAMILLE** (une
consolidation), pas des grains.

Ce que ces tests verrouillent :

1. la **nature** se decide sur les **metadonnees seules** (titre + labels) :
   aucune lecture de corps, aucun appel reseau de plus ;
2. une **racine de famille** (une consolidation declaree comme parent par un
   autre titre) est un **parapluie** : elle passe dans le slot des
   conteneurs, et ses sous-grains restent des grains ;
3. une consolidation **seule** dans le pool reste une **feuille** : la
   priorite de consolidation (invariant I7) tient ;
4. le grain de **harnais** (labels `harnais` / `coordination`) n'est pas servi
   a une lane **worker** ; les lanes qui **gerent** l'urne le gardent ;
5. le repli **nomme sa cause** : un tirage degrade s'explique ;
6. les trois ecarts mesures par la review Hermes du 24/11 restent fermes :
   l'**urne l'emporte** sur le harnais, la forme **large** de la parenthese
   est documentee et verrouillee, et la regle du conteneur declare n'existe
   qu'en un seul endroit.

Aucun test ne touche le reseau : `run` est un faux, le cache est un fake.
"""
import ast
import json
import re
import sys
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import (tapis_ancre, tapis_leger, tapis_nature, tapis_occupation,
                          tapis_rapide, tapis_repli, tapis_repli_cause,
                          tapis_universel)

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 24, 16, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"
COORD = "myia-ai-01:CoursIA"
ADJOINT = "myia-po-2025:CoursIA-2"
SECRETAIRE = "myia-po-2028:CoursIA-3"
DOSSIER_COORD = Path(__file__).resolve().parents[1] / "coordination"


def _meta(numero: int, titre: str = "", labels=(), created: str = "2026-01-01T00:00:00Z") -> dict:
    return {"number": numero, "title": titre or f"Grain {numero}",
            "created_at": created, "updated_at": created,
            "labels": list(labels)}


class _Etat:
    def __init__(self, numero: int):
        self.numero = numero


# --- LE PARENT DECLARE PAR LE TITRE ----------------------------------------


def test_le_parent_de_titre_se_lit_dans_le_crochet_de_tete():
    """Le crochet de tete porte le parent : `[ICT #20298] G4`."""
    assert tapis_nature.parent_de_titre("[ICT #20298] G4 -- une tranche") == 20298
    assert tapis_nature.parent_de_titre("[#20250 phase 3] ...") == 20250
    assert tapis_nature.parent_de_titre("Un titre sans crochet") is None
    assert tapis_nature.parent_de_titre("[GameTheory] ...") is None


def test_un_numero_qui_est_l_issue_ne_declare_nothing():
    """Une issue ne se declare pas elle-meme racine."""
    assert tapis_nature.parent_de_titre("[ICT #7] ...", 7) is None


def test_les_racines_declarees_viennent_des_titres():
    """Les racines sont les numeros nommes par un AUTRE titre : crochet de
    tete, ou parenthese du scope."""
    metas = [_meta(5, "[ICT #20298] G4"), _meta(6, "Fix(tooling,#16231): ...")]
    assert tapis_nature.racines_declarees(metas) == {20298, 16231}
    assert tapis_nature.racines_declarees([_meta(7, "[ICT #7] x")]) == set()


# --- LA NATURE : PARAPLUIE, FEUILLE, CONTENEUR ------------------------------


def test_un_conteneur_declare_est_un_parapluie():
    """Le conteneur DECLARE : label `epic`/`umbrella`, ou un titre qui
    COMMENCE par EPIC sans declarer de parent (`[EPIC #123] ...` declare au
    contraire un PARENT : c'est un sous-grain)."""
    assert tapis_nature.est_parapluie("EPIC du tas", ["epic"], 1, set())
    assert tapis_nature.est_parapluie("EPIC du tas", [], 1, set())
    assert tapis_nature.est_parapluie("Un grain ordinaire", [], 1, set()) is False


def test_une_racine_de_famille_est_un_parapluie():
    """La consolidation DECLAREE comme parent par un autre titre est une
    racine : elle se sert par ses sous-grains."""
    racines = {20298}
    assert tapis_nature.est_parapluie("Consolidation ICT", ["consolidation"],
                                       20298, racines)
    assert not tapis_nature.est_parapluie("Consolidation ICT", ["consolidation"],
                                           20298, set())


def test_une_consolidation_seule_dans_le_pool_reste_une_feuille():
    """I7 : personne ne declare cette consolidation racine -- c'est une
    FEUILLE, et elle garde la priorite de consolidation devant l'anciennete."""
    metas = [_meta(6002, "Consolidation X", ["consolidation"], "2026-01-01T00:00:00Z"),
             _meta(6001, "Un grain ancien", [], "2025-01-01T00:00:00Z")]
    etats = {e.numero: e for e in tapis_universel.etats_leger(metas, {}, NOW)}
    assert etats[6002].conteneur is False, "une consolidation seule est une feuille"
    assert etats[6002].consolidation is True


def test_la_racine_declaree_passe_dans_le_slot_des_conteneurs():
    """Le classement separe : la racine est un conteneur, son enfant un grain."""
    metas = [_meta(20298, "Consolidation ICT", ["consolidation"]),
             _meta(28305, "[ICT #20298] G4 -- un sous-grain")]
    etats = {e.numero: e for e in tapis_universel.etats_leger(metas, {}, NOW)}
    assert etats[20298].conteneur is True, "la racine est un parapluie"
    assert etats[28305].conteneur is False, "le sous-grain reste un grain"
    assert etats[28305].parent == 20298


# --- LE GRAIN DE HARNAIS ----------------------------------------------------


def test_le_grain_de_harnais_est_marque_par_son_label():
    """Les labels `harnais` et `coordination` sont la DONNEE de la nature."""
    metas = [_meta(7423, "Un grain de harnais", ["harnais"]),
             _meta(11554, "Une affaire de coordination", ["coordination"]),
             _meta(8, "Un grain de worker")]
    assert tapis_nature.marques_harnais(metas) == {7423: "harnais", 11554: "harnais"}
    assert tapis_nature.est_harnais(["Harnais"]), "la casse ne compte pas"


def test_le_grain_de_harnais_n_est_pas_serve_a_une_lane_worker():
    """Le travail de harnais appartient aux lanes qui **gerent** l'urne : une
    lane worker rend la main (dispatch `c0035b`)."""
    metas = [_meta(7423, "Un grain de harnais", ["harnais"])]
    restants, _, _, _ = tapis_occupation.retirer_harnais(
        [_Etat(7423), _Etat(8)], [], metas, LANE)
    assert [e.numero for e in restants] == [8]


def test_les_lanes_gerantes_gardent_le_grain_de_harnais():
    """Pour elles, c'est une information, pas une exclusion."""
    metas = [_meta(7423, "Un grain de harnais", ["harnais"])]
    for gerante in (COORD, ADJOINT, SECRETAIRE):
        restants, _, _, _ = tapis_occupation.retirer_harnais(
            [_Etat(7423)], [], metas, gerante)
        assert [e.numero for e in restants] == [7423]


def test_le_repli_garde_le_pool_si_l_exclusion_le_vide():
    """Fail-OPEN : un tirage qui ne sert rien ne sert a rien (I1)."""
    metas = [_meta(7423, "Le seul grain, et il est de harnais", ["harnais"])]
    restants, _, _, _ = tapis_occupation.retirer_harnais(
        [_Etat(7423)], [], metas, LANE)
    assert [e.numero for e in restants] == [7423]


def test_le_motif_du_harnais_est_lisible():
    """L'exclusion n'est jamais silencieuse : elle porte son motif."""
    motif = tapis_occupation.motif(tapis_nature.MARQUE_HARNAIS)
    assert "harnais" in motif and "worker" in motif


# --- LES ECARTS MESURES PAR LA REVIEW HERMES DU 24/11 ------------------------


def test_l_urne_l_emporte_sur_le_harnais():
    """Une issue qui porte les DEUX labels reste a l'urne.

    L'ordre des `update` l'assurait : l'urne passe en dernier, donc elle
    ecrase le harnais. Avant, le harnais ecrasait l'urne et les quatre issues
    qui portent les deux labels (#18763, #21822, #22938, #26337) sortaient de
    la section « urne » du `resume` des lanes gerantes (mesure Hermes)."""
    metas = [_meta(18763, "Les deux labels", ["candidate-delivered", "harnais"]),
             _meta(9, "Harnais seul", ["harnais"]),
             _meta(10, "Urne seule", ["candidate-delivered"])]
    marques = tapis_occupation.marques(metas, [], COORD)
    assert marques[18763] == "urne", "l'urne l'emporte : c'est la classe la plus dure"
    assert marques[9] == "harnais"
    assert marques[10] == "urne"


def test_la_parenthese_du_titre_declare_une_racine():
    """La forme est **large** : toute parenthese qui cite un numero declare
    une racine de famille.

    C'est la regle **documentee et verrouillee** (Hermes, 24/11 : « la regle
    est plus large que sa description »). La forme etroite (le SCOPE seul)
    perdrait #5081 -- dont l'unique enfant (#24224) declare sa mere par
    `(Parcours (#5081))` -- et les formes qui ne sont pas une declaration
    (`(Concern #24179)`, `(inc. #10761)`) ne promeuvent aucune consolidation
    sur le pool reel."""
    metas = [_meta(5, "Une consolidation (soeur de #20298 et #17545)"),
             _meta(6, "Un grain (fille #14446, 3e serie)"),
             _meta(7, "Un grain (Concern #24179)"),
             _meta(8, "Un grain (inc. #10761)")]
    assert tapis_nature.racines_declarees(metas) == {20298, 14446, 24179, 10761}
    scope = [_meta(10, "Fix(tooling,#16231): ...")]
    assert tapis_nature.racines_declarees(scope) == {16231}, "le scope declare"


def test_la_regle_du_conteneur_est_canonique():
    """Une regle dupliquee derive : la voie lourde delègue a la regle
    canonique (`tapis_nature`), au lieu de la recopier (Hermes : 83
    conteneurs a la voie legere, 80 a la voie lourde)."""
    corpus = [
        ("EPIC du tas", []),
        ("[EPIC #123] une tranche", []),
        ("[EPIC du tas]", []),
        ("Un grain ordinaire", []),
        ("Un grain ordinaire", ["epic"]),
        ("Un grain ordinaire", ["umbrella"]),
        ("Une consolidation", ["consolidation"]),
        ("", []),
    ]
    for titre, labels in corpus:
        assert tapis_rapide._conteneur_de(titre, labels) == \
            tapis_nature.est_conteneur_declare(titre, labels), titre


# --- LE REPLI NOMME SA CAUSE ------------------------------------------------


def test_les_causes_du_repli_sont_nommees():
    """Une cause sans code ni motif ne dit rien : les deux builders en
    donnent un."""
    class _Exc:
        lecture, page, cause = "selection", 2, "reseau muet"
    cause = tapis_repli_cause.lecture_incomplete(_Exc())
    assert cause["code"] == "lecture-incomplete"
    assert cause["lecture"] == "selection" and cause["page"] == 2
    assert cause["motif"]
    assert tapis_repli_cause.cap_livraisons(45)["code"] == "cap-livraisons"


def test_le_rapport_du_repli_publie_la_cause(monkeypatch):
    """Le rapport d'un tirage degrade doit dire POURQUOI (dispatch `c0035b` :
    le repli du 24/11 rendait `voie: repli` et `selection_s: 0.0` sans une
    seule raison)."""
    cache = {"issues": [_meta(11, "Un grain du cache")], "citations": {},
             "prs": [], "lu_a": "2026-01-01T00:00:00Z", "_epoch": 0}
    monkeypatch.setattr(tapis_repli.tapis_repli_cache, "lire",
                        lambda dossier, jours, ttl_s=None: cache)
    monkeypatch.setattr(tapis_repli, "curseur", lambda dossier, lane: 0)
    monkeypatch.setattr(tapis_repli, "avancer", lambda dossier, lane, blocs: None)
    cause = {"code": "lecture-incomplete", "motif": "reseau muet"}
    rapport, code = tapis_repli.replir(
        LANE, 2, NOW, 45, "graine", Path(__file__).resolve().parents[2],
        cause=cause)
    assert code == 0
    assert rapport["voie"] == "repli"
    assert rapport["cause_repli"] == cause
    assert rapport["repli"]["cause"] == cause


# --- LE REPLI PUBLIE SES EXCLUSIONS ET SA REINTRODUCTION --------------------


def _repli(monkeypatch, cache: dict, grains: int = 2):
    """Le rapport PUBLIC du repli, sur un cache local factice."""
    monkeypatch.setattr(tapis_repli.tapis_repli_cache, "lire",
                        lambda dossier, jours, ttl_s=None: cache)
    monkeypatch.setattr(tapis_repli, "curseur", lambda dossier, lane: 0)
    monkeypatch.setattr(tapis_repli, "avancer", lambda dossier, lane, blocs: None)
    return tapis_repli.replir(LANE, grains, NOW, 45, "graine",
                              Path(__file__).resolve().parents[2],
                              cause={"code": "lecture-incomplete",
                                     "motif": "reseau muet"})


def test_le_repli_publie_les_exclusions_effectives(monkeypatch):
    """Un grain de harnais ecarte du repli est publie AVEC son motif.

    Review du coordinateur (25/11, #28435) : `retirer_harnais()` jetait
    `_exclus` -- le grain de harnais disparaissait du tirage sans motif, et
    le rapport ne distinguait pas « ecarte » de « jamais vu »."""
    cache = {"issues": [_meta(9001, "Un grain ordinaire"),
                        _meta(9002, "Un grain de harnais", ["harnais"])],
             "citations": {}, "prs": [], "lu_a": "2026-01-01T00:00:00Z",
             "_epoch": 0}
    rapport, code = _repli(monkeypatch, cache)
    assert code == 0
    exclus = rapport["occupations"]["exclus"]
    assert [e["numero"] for e in exclus] == [9002], "le harnais est ecarte"
    assert exclus[0]["marque"] == "harnais"
    assert exclus[0]["motif"], "l'exclusion porte son motif"
    assert [g["numero"] for g in rapport["grains"]] == [9001]
    assert not rapport["repli"]["reintroduction"], "pas de reintroduction ici"


def test_le_repli_signale_la_reintroduction_fail_open(monkeypatch):
    """Le fail-OPEN (l'exclusion vide le pool) est Dit, pas muet.

    Review du coordinateur (25/11, #28435) : avec le SEUL grain de harnais
    dans le cache, le pool revient (fail-OPEN, I1) -- mais le rapport
    l'annoncait comme un tirage ordinaire. Le grain reintroduit doit etre
    qualifie avant d'etre servi."""
    cache = {"issues": [_meta(9002, "Le seul grain, et il est de harnais",
                              ["harnais"])],
             "citations": {}, "prs": [], "lu_a": "2026-01-01T00:00:00Z",
             "_epoch": 0}
    rapport, code = _repli(monkeypatch, cache)
    assert code == 0
    rein = rapport["repli"]["reintroduction"]
    assert rein["numeros"] == [9002], "le pool est REINTRODUIT"
    assert rein["qualification_requise"] is True
    assert rein["motif"], "la reintroduction porte son motif"
    assert rapport["occupations"]["reintroduction"] == rein
    assert [g["numero"] for g in rapport["grains"]] == [9002]


# --- LE TEMOIN AU POINT D'ENTREE PUBLIC (contre-epreuve du 25/11) -----------
#
# Les temoins de #27393 etablissent l'ordre dans l'**etage fin** et la
# rotation sur fixture -- pas la priorite de la file **effectivement servie**
# par le point d'entree public. Ce temoin va jusqu'a la liste servie : une
# consolidation **admissible** (personne ne la declare racine) passe devant
# un grain ordinaire **plus ancien**, et les exclusions restent intactes.


def _noeud(n: int, titre: str, cree: str, labels=()) -> dict:
    return {"number": n, "title": titre, "createdAt": cree, "updatedAt": cree,
            "labels": {"nodes": [{"name": lab} for lab in labels]}}


def _page_metas(nodes: list[dict]) -> str:
    return json.dumps({"data": {"repository": {"issues": {
        "pageInfo": {"hasNextPage": False, "endCursor": "c"},
        "nodes": nodes}}}})


def _page_issues_multiples(requete: str) -> str:
    """La reponse au lot : un alias par issue demandee."""
    alias: dict[str, dict] = {}
    for k, n in re.findall(r"i(\d+):\s*issue\(number:(\d+)\)", requete):
        alias[f"i{k}"] = {"number": int(n), "title": f"Grain {n}", "body": "",
                         "createdAt": "2026-01-01T00:00:00Z",
                         "updatedAt": "2026-01-01T00:00:00Z",
                         "labels": {"nodes": []},
                         "comments": {"totalCount": 0, "nodes": []}}
    return json.dumps({"data": {"repository": alias}})


def test_le_point_d_entree_public_sert_la_consolidation_admissible(
        tmp_path, monkeypatch):
    """La liste **effectivement servie** par le point d'entree public.

    Deux choses, sur la meme lecture :

    - une consolidation **admissible** (personne ne la declare racine : elle
      reste une feuille) passe devant un grain ordinaire **plus ancien** --
      l'invariant I7, mesure jusqu'a la liste servie ;
    - les exclusions restent **intactes** : le grain de harnais n'est pas
      servi, et son exclusion est publiee avec son motif.
    """
    nodes = [_noeud(101, "Un grain ordinaire", "2025-01-01T00:00:00Z"),
             _noeud(102, "Une consolidation admissible", "2026-06-01T00:00:00Z",
                    ["consolidation"]),
             _noeud(103, "Un grain de harnais", "2025-01-01T00:00:00Z",
                    ["harnais"])]

    def run(argv, timeout):
        requete = " ".join(argv)
        if "issue(number:" in requete:
            return _page_issues_multiples(requete)
        if "graphql" in requete:
            return _page_metas(nodes)
        if argv[0] == "git":
            return ""
        return "[]"

    # L'etat de l'ancre est isole : le temoin ne touche pas la rotation
    # reelle de la lane.
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    rapport, code = tapis_leger.tirage(LANE, 4, NOW, 45, "graine", Path("."),
                                       run)
    assert code == 0
    servis = [g["numero"] for g in rapport["grains"]]
    assert 102 in servis and 101 in servis, "les deux grains sont servis"
    assert servis.index(102) < servis.index(101), \
        "la consolidation admissible passe devant le grain plus ancien"
    assert 103 not in servis, "le grain de harnais n'est pas servi"
    exclus = rapport["occupations"]["exclus"]
    assert [e["numero"] for e in exclus] == [103], "l'exclusion est publiee"
    assert exclus[0]["motif"], "elle porte son motif"


# --- les plafonds des organes de ce PR --------------------------------------

# La liste des plafonds des organes du tapis vit dans `test_tapis_rapide.py`,
# un fichier **epingle** (810 lignes, `scripts/ci/script_size_ceilings.json`) :
# toute entree ajoutee le fait grossir au-dela de son plafond, et le ratchet
# (`scripts/tests/test_script_size_ratchet.py`) rougit alors la PR qui l'a
# fait grossir. Les entrees des organes de cette PR vivent donc dans SON
# module de test, qui n'est pas epingle.

@pytest.mark.parametrize(("nom", "plafond"), [("tapis_nature.py", 190),
                                              ("tapis_occupation_rapport.py", 80),
                                              ("tapis_occupation_base.py", 80),
                                              ("tapis_occupation_reintroduction.py", 35),
                                              ("tapis_repli_cause.py", 40),
                                              ("tapis_repli_cache.py", 80)])
def test_plafond_de_lignes(nom, plafond):
    """L'organe tient son plafond de lignes, et aucune de ses fonctions
    n'en depasse 60."""
    texte = (DOSSIER_COORD / nom).read_text(encoding="utf-8")
    assert len(texte.splitlines()) <= plafond
    for noeud in ast.walk(ast.parse(texte)):
        if isinstance(noeud, ast.FunctionDef | ast.AsyncFunctionDef):
            assert noeud.end_lineno - noeud.lineno + 1 <= 60, noeud.name
