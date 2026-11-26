"""La livraison REPARTEE : plusieurs PR livrent chacune une tranche (#24461).

Defaut mesure (25/11, #24461) : la preuve par le diff ne confronte que le
DERNIER `[DELIVERED]` a l'attribution de l'issue. Une issue livree par
plusieurs PR, chacune bornee par sa clause `paths:`, est donc toujours une
tranche : l'ecart LIVREE est leve, et l'issue attestee livree repart dans la
rotation (critere 4 NON TENU, 3 grains sur 24 servis).

Defaut connexe, trouve en verifiant le garde-fou « fil complet seulement » :
sur une fenetre partielle, l'exclusion LIVREE que concluait la voie unique
etait FINALE, alors que le fil complet disait la tranche -- un claim plus
ancien que la fenetre elargit l'attribution. Seuls les ecarts LEVES etaient
relus. Un LIVREE sur fenetre partielle est desormais differe au fil complet :
il en coute une lecture de fil par etat differe, aucune sonde de PR en plus.

Ce que ces tests verrouillent :

1. l'UNION des livraisons prouvees couvre l'attribution : l'ecart LIVREE
   tient, sur la fenetre entiere et sur le fil complet relu ;
2. rien n'est sonde tant que l'attribution n'est pas couverte par les
   perimetres DECLARES (attribution inconnue, globale, melee, en glob) ;
3. chaque livraison est prouvee par le diff ET l'etat de SA PR : une PR
   fermee sans fusion ou un diff partiel ne compte pas ;
4. une fenetre PARTIELLE ne decide pas LIVREE : l'etat est differe au fil
   complet, ni sonde ni decide sur la fenetre ; les autres ecarts suivent la
   voie unique, inchanges ;
5. une retractation desarme les livraisons qui la precedent ;
6. la borne de sondes est dite quand elle arrete la lecture, et rien n'est
   lu au-dela de la couverture ;
7. l'agregat n'ecarte rien par lui-meme : sans attestation, ou livre par une
   seule PR, le grain garde la voie unique ;
8. un ecart leve reprend la decision du grain nu (l'occupation reprend ses
   droits, comme dans `test_tapis_reprise_livree`).

Aucun test ne touche le reseau : `run` et la preuve sont des faux.
"""
from __future__ import annotations

import ast
import sys
from datetime import UTC, datetime
from pathlib import Path
from types import SimpleNamespace

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_qualification as tq
from coordination import tapis_repartie as tr
from coordination.tapis_preuve import Preuve

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 25, 9, 0, tzinfo=UTC)
LANE = "myia-po-2024:CoursIA"
AUTRE = "myia-ai-01:CoursIA-2"
TIERCE = "myia-po-2028:CoursIA"

A, B, C = "scripts/pkg/a.py", "scripts/pkg/b.py", "scripts/pkg/c.py"

#: Trois fenetres, un meme fil de quatre commentaires : entiere (elle suffit
#: et decide), partielle avec les deux livraisons visibles (l'attribution est
#: hors fenetre), partielle avec une seule livraison visible.
FENETRES = pytest.mark.parametrize("visible", [None, 3, 2],
                                   ids=["entiere", "partielle-deux-livraisons",
                                        "partielle-une-livraison"])


def _commentaire(body: str, quand: str) -> dict:
    return {"created_at": quand, "author": "jsboige", "body": body}


def _fil(corps: list[str], premier_jour: int = 10) -> list[dict]:
    """Un fil de dates croissantes, du plus ancien au plus recent."""
    return [_commentaire(body, f"2026-11-{premier_jour + i:02d}T00:00:00Z")
            for i, body in enumerate(corps)]


def _claim(paths, lane: str = AUTRE) -> str:
    ligne = f"[CLAIMED] lane {lane}"
    return ligne if paths is None else f"{ligne} -- paths: {', '.join(paths)}"


def _livree(pr: int, paths, lane: str = AUTRE) -> str:
    return f"[DELIVERED] lane {lane} -- PR #{pr} -- paths: {', '.join(paths)}"


#: L'attestation de la lane : dernier commentaire, elle pose l'ecart LIVREE.
INFO = "[INFO] candidate-delivered lane myia-po-2028:CoursIA -- PR #101 et PR #102 fusionnees"


def _repertorie(attribution=(A, B), livraisons=((101, (A,)), (102, (B,)))) -> list[dict]:
    """Le fil mesure : une attribution, une PR par chemin, une attestation."""
    corps = [_claim(attribution), *(_livree(pr, paths) for pr, paths in livraisons), INFO]
    return _fil(corps)


class Sondes:
    """La preuve fausse : un diff et un etat par PR ; les sondes sont comptees."""

    def __init__(self, par_pr: dict):
        self.par_pr = par_pr
        self.lues: list[int] = []

    def __call__(self, numero):
        if numero not in self.par_pr:
            return None
        fichiers, etat, fusionne = self.par_pr[numero]
        self.lues.append(numero)
        return Preuve(tuple(fichiers), etat, fusionne)


def _deux_pr_fusionnees() -> Sondes:
    """Deux PR fusionnees, un chemin chacune : le cas mesure."""
    return Sondes({101: ((A,), "MERGED", True), 102: ((B,), "MERGED", True)})


def _pr_ouverte(numero: int, lane: str) -> dict:
    """Une PR ouverte qui FERME l'issue : c'est la forme qui la tient."""
    return {"number": numero, "title": f"PR {numero}",
            "body": f"Grain: DEEP/guard -- lane {lane} -- prev: MED/guard #1\n\nCloses #7",
            "created_at": "2026-11-20T00:00:00Z", "updated_at": "2026-11-20T00:00:00Z"}


def _qualifier(monkeypatch, fil: list[dict], sondes: Sondes, visible: int | None = None,
               prs: list[dict] | None = None, lire=None) -> tuple:
    """La qualification de l'issue 7 ; `visible` = derniers commentaires lus.

    `None` : la fenetre porte le fil entier, elle suffit. Un nombre : la
    fenetre ne montre que ces derniers commentaires, le fil est relu. Le
    resultat est celui de `qualifier`, suivi des fils complets lus.
    """
    fenetre = fil if visible is None else fil[-visible:]
    issue = {"number": 7, "title": "Grain 7", "body": "", "labels": [],
             "created_at": "2026-11-01T00:00:00Z", "comments": fenetre,
             "comments_total": len(fil)}
    lus: list[int] = []
    monkeypatch.setattr(tq.tapis_lot.gh_selection, "qualifier",
                        lambda run, depot, numeros=None: {7: issue})
    monkeypatch.setattr(tq.tapis_fenetre, "fil_complet",
                        lire or (lambda numero: lus.append(numero) or fil))
    return (*tq.qualifier([7], LANE, NOW, 45, prs or [], lambda *a: "[]", preuve=sondes),
            lus)


def _etat(ecart="LIVREE") -> SimpleNamespace:
    return SimpleNamespace(numero=7, ecart=ecart, motif="", notes=[])


def _lec(fil: list[dict], visible: int | None = None) -> SimpleNamespace:
    lus = fil if visible is None else fil[-visible:]
    return SimpleNamespace(issues=[{"number": 7, "comments": lus, "comments_total": len(fil)}])


# --- 1 : l'union des diffs prouve la livraison repartie ----------------------


@FENETRES
def test_l_union_des_diffs_prouve_la_livraison_repartie(monkeypatch, visible):
    """LE defaut mesure : deux tranches couvrent l'issue, le tapis la servait.

    Sur la base, chaque PR est une tranche plus etroite que l'attribution :
    l'ecart LIVREE etait leve. L'union de leurs diffs le tient.
    """
    sondes = _deux_pr_fusionnees()
    servis, ecartees, *_ = _qualifier(monkeypatch, _repertorie(), sondes, visible)
    assert servis == [], "une livraison repartie et prouvee n'est pas servie"
    assert ecartees[7]["code"] == "LIVREE"
    motif = ecartees[7]["motif"]
    assert "PR #102" in motif and "PR #101" in motif, "l'ecart nomme les deux PR"
    assert ecartees[7]["fenetre_suffit"] is (visible is None)
    assert set(sondes.lues) == {101, 102}
    assert len(sondes.lues) == 2, "chaque PR est sondee une fois, sur le fil qui decide"


@FENETRES
def test_une_pr_fermee_sans_fusion_laisse_l_issue_dans_la_rotation(monkeypatch, visible):
    """Chaque livraison est prouvee par le diff ET l'etat de SA PR : la PR
    #102 est fermee sans fusion, la moitie du perimetre n'est pas livree."""
    sondes = Sondes({101: ((A,), "MERGED", True), 102: ((B,), "CLOSED", False)})
    servis, ecartees, *_ = _qualifier(monkeypatch, _repertorie(), sondes, visible)
    assert [e.numero for e in servis] == [7], "l'issue reste dans la rotation"
    assert 7 not in ecartees
    notes = [n for n in servis[0].notes if n.startswith("livraison repartie")]
    assert notes and "#102" in notes[0], "la note dit la livraison qui ne prouve pas"


def test_un_diff_partiel_ne_compte_pas(monkeypatch):
    """La PR #102 declare `b.py`, son diff ne le contient pas : une tranche."""
    sondes = Sondes({101: ((A,), "MERGED", True), 102: ((C,), "MERGED", True)})
    servis, ecartees, *_ = _qualifier(monkeypatch, _repertorie(), sondes)
    assert [e.numero for e in servis] == [7], "l'issue reste dans la rotation"
    assert 7 not in ecartees


# --- 2 : rien n'est sonde sans perimetre declare couvrant -------------------


def test_rien_n_est_sonde_sans_perimetre_declare_couvrant():
    """Attribution inconnue, globale, melee, en glob, ou plus large que
    l'union declaree : aucune PR n'est lue."""
    livres = tr.verifiables(_repertorie())
    melee = _repertorie()
    melee.insert(1, _commentaire(_claim(None, TIERCE), "2026-11-10T06:00:00Z"))
    cas = {
        "inconnue": (None, "attribution inconnue"),
        "globale": ([], "attribution globale"),
        "melee": (tr.attribution_du_fil(melee), "attribution globale"),
        "glob": (["scripts/pkg/*.py"], "plus etroit"),
        "plus large": ([A, B, C], f"plus etroit que l'issue -- manque {C}"),
    }
    for nom, (attr, dit) in cas.items():
        sondes = _deux_pr_fusionnees()
        etat, detail = tr.agreger(livres, attr, sondes)
        assert (etat, sondes.lues) == (tr.TRANCHE, []), nom
        assert dit in detail, nom
    assert tr.attribution_du_fil(_repertorie()) == [A, B], "controle : bornee, elle est lue"


def test_une_livraison_declaree_en_glob_ne_compte_pas():
    """La clause en glob couvre l'attribution sur le papier : la PR est lue,
    mais un glob ne certifie jamais la completude."""
    fil = _repertorie(livraisons=((101, (A,)), (102, ("scripts/pkg/*.py",))))
    sondes = Sondes({101: ((A,), "MERGED", True), 102: ((A, B), "MERGED", True)})
    etat, detail = tr.agreger(tr.verifiables(fil), [A, B], sondes)
    assert (etat, sondes.lues) == (tr.TRANCHE, [102, 101])
    assert "1 prouvee(s) par leur diff (PR #101)" in detail


# --- 4 : une fenetre partielle ne decide pas LIVREE --------------------------


def test_la_fenetre_partielle_differe_livree_sans_rien_sonder():
    """Ni l'agregat ni la voie unique ne voient un LIVREE sur fenetre partielle."""
    sondes = _deux_pr_fusionnees()
    partielle = _etat()
    rendus = tr.sur_fenetre([partielle], _lec(_repertorie(), visible=3), sondes)
    assert rendus == ([], [partielle]), "differe, jamais rendu a la voie unique"
    assert (partielle.ecart, sondes.lues) == ("LIVREE", []), "rien n'est decide ni sonde"
    entiere = _etat()
    assert tr.sur_fenetre([entiere], _lec(_repertorie()), sondes) == ([], [])
    assert (entiere.ecart, sondes.lues) == ("LIVREE", [102, 101])


@pytest.mark.parametrize("code", [None, "GEL", "RECLAMEE"], ids=["nu", "gel", "reclamee"])
def test_les_autres_ecarts_suivent_la_voie_unique(code):
    """Seul LIVREE depend d'un fil complet : un autre etat n'est pas differe."""
    etat = _etat(code)
    assert tr.sur_fenetre([etat], _lec(_repertorie(), visible=3), Sondes({})) == ([etat], [])
    assert etat.ecart == code


def _un_seul_livraison(attribution) -> list[dict]:
    """Un fil de quatre commentaires : une PR livre exactement l'attribution."""
    return _fil(["un commentaire quelconque", _claim(attribution),
                 _livree(101, list(attribution)), INFO])


def test_un_claim_cache_par_la_fenetre_ne_prouve_pas_la_livraison(monkeypatch):
    """LE defaut connexe : l'attribution lue sur la fenetre est amputee.

    La fenetre voit un seul claim (`a.py`) et la PR #101 qui le livre : la
    voie unique y concluait COUVRE, et l'exclusion LIVREE etait finale. Le fil
    complete porte aussi le claim de C sur `b.py` : l'issue n'est pas livree.
    """
    fil = _fil([_claim([B], TIERCE), _claim([A]), _livree(101, [A]), INFO])
    sondes = Sondes({101: ((A,), "MERGED", True)})
    servis, ecartees, _, _, _, _, lus = _qualifier(monkeypatch, fil, sondes, visible=3)
    assert [e.numero for e in servis] == [7], "l'issue reste dans la rotation"
    assert 7 not in ecartees
    assert lus == [7], "le fil complet est lu une fois"
    assert sondes.lues == [101], "la PR est sondee une fois, sur le fil complet"


def test_livree_differe_est_confirme_sur_le_fil_complet(monkeypatch):
    """Controle : le fil complet confirme la livraison, l'exclusion tient."""
    sondes = Sondes({101: ((A, B), "MERGED", True)})
    servis, ecartees, _, _, _, _, lus = _qualifier(monkeypatch, _un_seul_livraison([A, B]),
                                                  sondes, visible=3)
    assert servis == [] and ecartees[7]["code"] == "LIVREE"
    assert ecartees[7]["fenetre_suffit"] is False, "l'ecart est du au fil complet"
    assert (lus, sondes.lues) == ([7], [101]), "ni lu ni sonde deux fois"


def test_le_fil_complet_decide_tout_du_grain_differe(monkeypatch):
    """Un [FROZEN] plus ancien que la fenetre : le fil complet l'ecarte, avant
    LIVREE ; aucune PR n'est sondee."""
    fil = _fil([_claim([A]), _livree(101, [A]), INFO])
    fil.insert(0, _commentaire("[FROZEN] en attente d'arbitrage", "2026-11-09T00:00:00Z"))
    sondes = Sondes({101: ((A,), "MERGED", True)})
    servis, ecartees, *_ = _qualifier(monkeypatch, fil, sondes, visible=3)
    assert servis == [] and ecartees[7]["code"] == "GEL"
    assert sondes.lues == []


def test_un_fil_complet_illisible_refuse_le_grain_differe(monkeypatch):
    """fail-CLOSED : sans fil complet rien n'est conclu, ni LIVREE ni service."""

    def illisible(numero):
        raise OSError("lecture impossible")

    def sonde(numero):
        raise AssertionError("aucune PR n'est lue sans fil complet")

    servis, ecartees, *_ = _qualifier(monkeypatch, _un_seul_livraison([A]), sonde,
                                      visible=3, lire=illisible)
    assert servis == [] and ecartees[7]["code"] == "FIL_ILLISIBLE"


def test_au_dela_du_mur_de_lectures_le_grain_differe_est_refuse():
    """Le mur de lectures refuse : la fenetre ne reprend pas ses droits."""
    differe = _etat(None)
    issue = {"number": 7, "title": "Grain 7", "body": "", "labels": [],
             "created_at": "2026-11-01T00:00:00Z",
             "comments": _un_seul_livraison([A])[-3:], "comments_total": 4}
    lec = tq.tapis_lot.lec([issue], NOW, 0)
    sondes = Sondes({101: ((A,), "MERGED", True)})
    confirmes, rejetes, _, appels = tq.tapis_fil_complet.confirmer(
        [differe], lec, LANE, NOW, 45, appels_max=0, preuve=sondes)
    assert confirmes == [] and (appels, sondes.lues) == (0, [])
    assert [(r["numero"], r["code"]) for r in rejetes] == [(7, "MUR_EPUISE")]


# --- 5 : une revocation desarme ce qui la precede ---------------------------


def test_l_instant_de_la_derniere_retractation():
    """Seule une retractation EN TETE DE LIGNE, hors code, est lue."""
    fil = _repertorie()
    assert tr.revocation(fil) == tr._JAMAIS
    fil.insert(3, _commentaire("un commentaire quelconque", "2026-11-13T00:00:00Z"))
    assert tr.revocation(fil) == tr._JAMAIS
    fil[3]["body"] = "> `[NOT-DELIVERED]` : le marqueur, cite, n'est pas une retractation"
    assert tr.revocation(fil) == tr._JAMAIS
    fil[3]["body"] = "[INFO] candidate-delivered-revoked lane myia-po-2028:CoursIA -- PR #102"
    assert tr.revocation(fil) == datetime(2026, 11, 13, tzinfo=UTC)


@pytest.mark.parametrize("revoque", [False, True], ids=["sans-revocation", "revocation"])
def test_une_revocation_desarme_les_livraisons_anterieures(monkeypatch, revoque):
    """Le sens est porte par l'ordre : une retractation posterieure aux deux
    livraisons les desarme. Sans elle, le meme fil est livre."""
    fil = _fil([_claim([A, B]), _livree(101, [A]), _livree(102, [B])])
    if revoque:
        fil.append(_commentaire(f"[NOT-DELIVERED] lane {AUTRE} -- PR #101 et PR #102",
                                "2026-11-13T00:00:00Z"))
    fil.append(_commentaire(INFO, "2026-11-15T00:00:00Z"))
    servis, ecartees, *_ = _qualifier(monkeypatch, fil, _deux_pr_fusionnees())
    if revoque:
        assert [e.numero for e in servis] == [7], "l'issue reste dans la rotation"
        assert 7 not in ecartees
    else:
        assert servis == [] and ecartees[7]["code"] == "LIVREE"


@pytest.mark.parametrize("clause", ["PATHS : {b}", "Paths:  {b}", "paths: {b} -- tranche 2",
                                    "voir paths: {b}"])
def test_une_clause_ecrite_autrement_se_fusionne(clause):
    """Le marqueur fusionne est ecrit sous forme canonique : le debut du
    marqueur le plus recent n'est pas recopie."""
    recent = f"[DELIVERED] lane {AUTRE} -- PR #101 -- {clause.format(b=B)}"
    assert tr.perimetre(recent) == [B], "controle : l'organe des claims lit cette clause"
    livres = tr.verifiables(_fil([_claim([A, B]), _livree(101, [A]), recent]))
    assert [tr.pr_designee(tr._ligne(l)) for l in livres] == [101]
    assert tr.perimetre(tr._ligne(livres[0])) == [A, B], "l'union de ses deux clauses"


def test_une_pr_livree_deux_fois_compte_pour_une():
    """Une clause `paths:` etendue sur la meme PR : un diff, une sonde."""
    fil = _repertorie([A, B, C], ((101, (A,)), (102, (B,)), (102, (C,))))
    livres = tr.verifiables(fil)
    assert [tr.pr_designee(tr._ligne(l)) for l in livres] == [102, 101]
    assert tr.perimetre(tr._ligne(livres[0])) == [B, C], "l'union de ses deux clauses"
    sondes = Sondes({101: ((A,), "MERGED", True), 102: ((B, C), "MERGED", True)})
    attendu = "2 livraisons (PR #102, PR #101) : leurs diffs couvrent le perimetre (3)"
    assert tr.agreger(livres, [A, B, C], sondes) == (tr.COUVRE, attendu)
    assert sondes.lues == [102, 101]


# --- 6 : la borne de sondes et l'arret a la couverture ----------------------


def test_la_borne_de_sondes_est_dite_quand_elle_arrete_la_lecture(monkeypatch):
    """Cinq PR livrent le meme chemin ; les quatre plus recentes sont fermees
    sans fusion, la plus ancienne est fusionnee : elle n'est pas lue."""
    corps = [_claim([B]), *(_livree(pr, [B]) for pr in range(101, 106)), INFO]
    fermee, fusionnee = ((B,), "CLOSED", False), ((B,), "MERGED", True)
    sondes = Sondes({**{pr: fermee for pr in range(102, 106)}, 101: fusionnee})
    livres = tr.verifiables(_fil(corps))
    etat, detail = tr.agreger(livres, [B], sondes)
    assert (etat, sondes.lues) == (tr.TRANCHE, [105, 104, 103, 102])
    assert "1 plus ancienne(s) non lue(s) (borne 4)" in detail
    monkeypatch.setattr(tr, "LIVRAISONS_MAX", 5)
    assert tr.agreger(livres, [B], sondes)[0] == tr.COUVRE, "controle : seule la borne arretait"


def test_l_agregat_s_arrete_des_que_l_attribution_est_couverte():
    """L'attribution est couverte par la seule PR #102 : la #101 n'est pas lue."""
    fil = _repertorie([B], ((101, [A]), (102, [B])))
    sondes = Sondes({101: ((A,), "MERGED", True), 102: ((B,), "MERGED", True)})
    etat, detail = tr.agreger(tr.verifiables(fil), [B], sondes)
    assert (etat, sondes.lues) == (tr.COUVRE, [102])
    assert detail == "1 livraisons (PR #102) : leurs diffs couvrent le perimetre (1)"


# --- 7 : l'agregat n'ecarte rien par lui-meme -------------------------------


def test_sans_attestation_la_voie_unique_est_inchangee():
    """`code` vaut `None` : le grain n'est pas atteste livre. L'agregat ne
    l'ecarte pas -- la voie unique dit la tranche du DERNIER marqueur."""
    sondes = _deux_pr_fusionnees()
    etat = _etat(None)
    assert tr.sur_fil_complet(etat, _repertorie(), None, sondes) is None
    assert etat.ecart is None
    assert sondes.lues == [102], "seule la derniere livraison est lue, comme avant"
    assert not any(n.startswith("livraison repartie") for n in etat.notes)


def test_une_seule_livraison_verifiable_suit_la_voie_unique():
    """Deux marqueurs, une PR : ni la sonde ni l'ecart ne changent."""
    fil = _repertorie([A, B], ((101, [A]), (101, [B])))
    sondes = Sondes({101: ((B,), "MERGED", True)})
    etat = _etat()
    assert tr.sur_fil_complet(etat, fil, "LIVREE", sondes) is None
    assert (sondes.lues, etat.ecart) == ([101], None)
    assert not any(n.startswith("livraison repartie") for n in etat.notes)
    occupe = _etat("OCCUPEE")
    assert tr.sur_fil_complet(occupe, _repertorie(), "OCCUPEE", sondes) == "OCCUPEE"
    assert (sondes.lues, occupe.ecart) == ([101], "OCCUPEE"), "un autre ecart n'est pas touche"


# --- 8 : un ecart leve reprend la decision du grain nu ----------------------


@FENETRES
def test_un_ecart_leve_reprend_la_decision_du_grain_nu(monkeypatch, visible):
    """Comme dans `test_tapis_reprise_livree` : la livraison non prouvee ne
    masque pas l'occupation. Une PR ouverte d'une autre lane tient l'issue."""
    fermees = Sondes({101: ((A,), "CLOSED", False), 102: ((B,), "CLOSED", False)})
    prs = [_pr_ouverte(99, AUTRE)]
    _, marque, *_ = _qualifier(monkeypatch, _repertorie(), fermees, visible, prs)
    _, nu, *_ = _qualifier(monkeypatch, _fil([INFO]), fermees, visible, prs)
    assert marque[7]["code"] == nu[7]["code"] == "OCCUPEE"
    assert marque[7]["motif"] == nu[7]["motif"], "un marqueur ne change que la note"


# --- le module reste borne ---------------------------------------------------


def test_le_module_reste_borne():
    """Le plafond de lignes du module et de ses fonctions, comme ses voisins.

    La liste canonique des plafonds du tapis (`test_tapis_rapide.py`) est un
    point chaud de fusion ; le plafond de CE module vit donc ici, comme celui
    de `tapis_reprise_livree`.
    """
    module = Path(tr.__file__).read_text(encoding="utf-8")
    assert len(module.splitlines()) <= 210
    for noeud in ast.walk(ast.parse(module)):
        if isinstance(noeud, ast.FunctionDef | ast.AsyncFunctionDef):
            assert noeud.end_lineno - noeud.lineno + 1 <= 45, noeud.name
