"""La REPRISE apres LIVREE (`coordination/tapis_reprise_livree.py`).

Defaut mesure le 25/11 (cycle c767, douze grains servis) : un marqueur de
livraison **non prouve** rendait le grain PLUS servable que son absence.

L'ordre des operations en etait la cause. Le marqueur `[DELIVERED]` sans
perimetre posait l'ecart LIVREE ; cet ecart faisait sauter l'exclusion
d'occupation (une PR ouverte d'une autre lane tient l'issue) ; puis la preuve
par le diff retirait LIVREE, puisque le marqueur ne designe aucun perimetre ;
et rien n'etait rejoue derriere. Le grain traversait les regles suivantes et
il etait servi. Sur trois des cinq grains presentes a la porte de claim, le
tapis et `check_lane_claim.py` ne disaient pas la meme chose.

L'invariant que ces tests verrouillent : **la decision d'un grain marque est
celle d'un grain nu, plus la note qui dit la livraison.**

1. un grain tenu par une PR ouverte d'une autre lane est ecarte (OCCUPEE) ;
2. la PR de la lane ne l'ecarte pas : c'est elle qui la porte au merge ;
3. sans PR ouverte, le grain reste dans la rotation : un marqueur non prouve
   ne retire rien ;
4. les deux voies de la qualification (fenetre, fil complet) disent la meme
   chose ;
5. les regles qui suivaient LIVREE sont rejouees, pas seulement l'occupation :
   le claim vivant d'une tierce lane reprend son ecart ;
6. une pause posterieure au marqueur n'a jamais dependu de la reprise (le fil
   est rouvert, elle est decidee avant) : la reprise ne la casse pas.

Aucun test ne touche le reseau : `run` et la preuve sont des faux.
"""
from __future__ import annotations

import ast
import sys
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_qualification as tq
from coordination.tapis_preuve import Preuve

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 25, 9, 0, tzinfo=UTC)
LANE = "myia-po-2024:CoursIA"
AUTRE = "myia-ai-01:CoursIA-2"
TIERCE = "myia-po-2028:CoursIA"
FICHIER = "scripts/coordination/tapis_rapide.py"

#: Le marqueur mesure : il designe une PR, il ne declare aucun perimetre.
MARQUEUR = f"[DELIVERED] lane {AUTRE} -- PR #99"

#: Chaque scenario joue sur les deux voies : la fenetre des douze derniers
#: commentaires, et le fil complet relu quand la fenetre ne suffit pas.
VOIES = pytest.mark.parametrize("fil_complet", [False, True],
                                ids=["fenetre", "fil-complet"])


def _commentaire(body: str, quand: str) -> dict:
    return {"created_at": quand, "author": "jsboige", "body": body}


def _fil(corps: list[str], premier_jour: int = 10) -> list[dict]:
    """Un fil de dates croissantes, du plus ancien au plus recent."""
    return [_commentaire(body, f"2026-11-{premier_jour + i:02d}T00:00:00Z")
            for i, body in enumerate(corps)]


def _pr_ouverte(numero: int, lane: str) -> dict:
    """Une PR ouverte qui FERME l'issue : c'est la forme qui la tient."""
    return {"number": numero, "title": f"PR {numero}",
            "body": f"Grain: DEEP/guard -- lane {lane} -- prev: MED/guard #1\n\nCloses #7",
            "created_at": "2026-11-20T00:00:00Z", "updated_at": "2026-11-20T00:00:00Z"}


def _qualifier(monkeypatch, commentaires: list[dict], prs: list[dict],
               fil_complet: bool = False) -> tuple:
    """La qualification de l'issue 7, `commentaires` pour tout son fil.

    `fil_complet` declare un total superieur au fil lu : la fenetre ne suffit
    pas, le fil est relu et la decision rejouee dessus (`confirmer`).
    """
    issue = {"number": 7, "title": "Grain 7", "body": "", "labels": [],
             "created_at": "2026-11-01T00:00:00Z", "comments": commentaires,
             "comments_total": len(commentaires) + (2 if fil_complet else 0)}
    monkeypatch.setattr(tq.tapis_lot.gh_selection, "qualifier",
                        lambda run, depot, numeros=None: {7: issue})
    monkeypatch.setattr(tq.tapis_fenetre, "fil_complet", lambda numero: commentaires)
    return tq.qualifier([7], LANE, NOW, 45, prs, lambda *a: "[]",
                        preuve=lambda pr: Preuve((FICHIER,), "OPEN", False))


# --- 1 et 2 : l'occupation reprend ses droits --------------------------------


@VOIES
def test_un_grain_tenu_par_une_pr_ouverte_d_une_autre_lane_est_ecarte(monkeypatch, fil_complet):
    """LE defaut mesure : le marqueur non prouve faisait sauter l'occupation.

    La PR #99 est ouverte, elle porte `Closes #7` et elle est d'une autre
    lane : `check_lane_claim.py` la refuse (rc=2), le tapis doit l'ecarter.
    """
    servis, ecartees, *_ = _qualifier(monkeypatch, _fil([MARQUEUR]),
                                      [_pr_ouverte(99, AUTRE)], fil_complet)
    assert servis == [], "un grain tenu par une PR ouverte d'une autre lane n'est pas servi"
    assert ecartees[7]["code"] == "OCCUPEE"
    assert "#99" in ecartees[7]["motif"], "l'exclusion nomme la PR qui tient le grain"
    assert ecartees[7]["fenetre_suffit"] is (not fil_complet)


@VOIES
def test_la_pr_de_la_lane_ne_retire_pas_le_grain(monkeypatch, fil_complet):
    """Controle negatif : la PR de la lane, c'est elle qui la porte au merge."""
    servis, ecartees, *_ = _qualifier(monkeypatch, _fil([MARQUEUR]),
                                      [_pr_ouverte(99, LANE)], fil_complet)
    assert [e.numero for e in servis] == [7]
    assert 7 not in ecartees
    assert any("#99" in n for n in servis[0].notes), "la couverture reste dite en note"


# --- 3 : la reprise ne retire rien que la decision nue retire ----------------


@VOIES
def test_sans_pr_ouverte_le_grain_reste_dans_la_rotation(monkeypatch, fil_complet):
    """Controle negatif : la reprise n'ajoute aucun ecart.

    Le meme grain, sans marqueur, serait servi ; sans PR ouverte, il l'est
    encore. La livraison non prouvee ne retire rien.
    """
    servis, ecartees, *_ = _qualifier(monkeypatch, _fil([MARQUEUR]), [], fil_complet)
    assert [e.numero for e in servis] == [7]
    assert 7 not in ecartees
    assert any("reste dans la rotation" in n for n in servis[0].notes), "la note dit la livraison"


def test_le_grain_marque_recoit_la_decision_du_grain_nu(monkeypatch):
    """L'invariant, mesure comme tel : un marqueur ne change que la note.

    Deux fils identiques hors le marqueur, meme PR ouverte d'une autre lane :
    meme code d'ecart, meme motif.
    """
    prs = [_pr_ouverte(99, AUTRE)]
    _, marque, *_ = _qualifier(monkeypatch, _fil([MARQUEUR]), prs)
    _, nu, *_ = _qualifier(monkeypatch, _fil(["un commentaire quelconque"]), prs)
    assert marque[7]["code"] == nu[7]["code"] == "OCCUPEE"
    assert marque[7]["motif"] == nu[7]["motif"]


# --- 5 : les regles qui suivaient LIVREE sont rejouees ------------------------


def test_le_claim_vivant_d_une_tierce_lane_reprend_son_ecart(monkeypatch):
    """Un marqueur d'une lane B ne ferme pas le claim d'une lane C.

    Sans la reprise, LIVREE masquait le claim vivant de C ; apres son retrait,
    rien ne le rejouait et le grain etait servi alors que la porte de claim
    le refuse. Le fil n'est pas rouvert : le claim PRECEDE la livraison.
    """
    commentaires = [_commentaire(f"[CLAIMED] lane {TIERCE} -- paths: {FICHIER}",
                                 "2026-11-24T10:00:00Z"),
                    _commentaire(MARQUEUR, "2026-11-24T12:00:00Z")]
    servis, ecartees, *_ = _qualifier(monkeypatch, commentaires, [])
    assert servis == [], "un grain revendique par une autre lane n'est pas servi"
    assert ecartees[7]["code"] == "RECLAMEE"
    assert TIERCE in ecartees[7]["motif"], "l'ecart nomme la lane qui tient le claim"


def test_une_pause_posterieure_au_marqueur_garde_son_ecart(monkeypatch):
    """Controle : la pause n'a jamais dependu de la reprise.

    Un marqueur posterieur rouvre le fil (`_rouverte`) : la livraison n'est
    pas retenue et la pause est decidee des la premiere passe. La reprise ne
    doit rien y changer.
    """
    pause = f"[RELEASED] lane {AUTRE} -- attend: Q42"
    servis, ecartees, *_ = _qualifier(monkeypatch, _fil([MARQUEUR, pause]), [])
    assert servis == [], "un grain en pause n'est pas servi"
    assert ecartees[7]["code"] == "PAUSE"
    assert "Q42" in ecartees[7]["motif"], "l'ecart dit ce que le grain attend"

# --- le module reste borne ---------------------------------------------------


def test_le_module_reste_borne():
    """Le plafond de lignes du module et de ses fonctions, comme ses voisins.

    La liste canonique des plafonds du tapis (`test_tapis_rapide.py`) est un
    point chaud de fusion : deux PR ouvertes y touchaient le 25/11 (#27059,
    #27393). Le plafond de CE module vit donc ici ; il rejoindra la liste
    quand le point chaud aura refroidi.
    """
    module = Path(tq.tapis_reprise_livree.__file__).read_text(encoding="utf-8")
    assert len(module.splitlines()) <= 90
    for noeud in ast.walk(ast.parse(module)):
        if isinstance(noeud, ast.FunctionDef | ast.AsyncFunctionDef):
            assert noeud.end_lineno - noeud.lineno + 1 <= 60, noeud.name
