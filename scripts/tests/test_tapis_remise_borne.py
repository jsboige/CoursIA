"""La remise de main BORNEE -- un `[RELEASED]` qui nomme un `paths:` ne rend que lui.

Cas fondeur (27/11, CoursIA#27133) : le `[RELEASED]` du grain Search-11
(verify-reject) a refuse la fournee suivante -- deux grains en 32 s -- dont
MGS-25, un carnet du meme fil que le marqueur ne nommait pas et qui n'avait
jamais echoue.

Aucun test ne touche le reseau : les commentaires sont fabriques.
"""
import ast
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_remise  # noqa: E402
from coordination.tapis_qualification_fil import CODES_QUALIFICATION  # noqa: E402

RAPIDE = Path(__file__).resolve().parents[1] / "coordination" / "tapis_rapide.py"

RENDU = "MyIA.AI.Notebooks/Search/Part1-Foundations/Search-11-Metaheuristics-Rust.ipynb"
VOISIN = ("MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-vs-mealpy/"
          "MGS-25-WhaleOptimisation-vs-Mealpy-Rust.ipynb")
QUAND = "2026-11-27T07:38:01Z"


def _fil(*corps: str) -> list[dict]:
    return [{"created_at": QUAND, "author": "myia-po-2028[bot]", "body": c}
            for c in corps]


def _release(clause: str | None) -> str:
    base = ("[RELEASED] lane myia-po-2028:claudish -- nb_coder: grain ended "
            "without a PR (verify-reject)")
    return f"{base} -- paths: {clause}" if clause else base


def test_une_remise_bornee_ne_rend_pas_un_grain_voisin():
    assert tapis_remise.rendue_ailleurs(_fil(_release(RENDU)), [VOISIN]) is True


def test_une_remise_bornee_rend_le_grain_qu_elle_nomme():
    """On ne se sert pas d'un scope pour lever sa propre remise."""
    assert tapis_remise.rendue_ailleurs(_fil(_release(RENDU)), [RENDU]) is False


def test_une_remise_sans_clause_reste_epic_wide():
    """Sans `paths:`, la semantique historique tient : toute l'issue est rendue."""
    assert tapis_remise.rendue_ailleurs(_fil(_release(None)), [VOISIN]) is False


def test_une_pause_n_est_pas_une_remise_de_trois_jours():
    """Un `[RELEASED]` qui porte une condition est une PAUSE : la borne du
    scope ne s'en mele pas (la pause se decide sur sa cible, ailleurs)."""
    corps = _release(RENDU) + " -- attend: #1234"
    assert tapis_remise.rendue_ailleurs(_fil(corps), [VOISIN]) is False


def test_sans_scope_declare_la_remise_rend_toujours():
    assert tapis_remise.rendue_ailleurs(_fil(_release(RENDU)), None) is False


def test_un_marqueur_posterieur_efface_la_remise():
    """Une prise en charge posterieure rouvre le fil : la borne ne s'applique
    plus, puisqu'il n'y a plus de remise a borner."""
    corps = _fil(_release(RENDU),
                 "[CLAIMED] lane myia-po-2028:claudish -- paths: " + VOISIN)
    assert tapis_remise.rendue_ailleurs(corps, [VOISIN]) is False


def _ordre_des_regles() -> list[str]:
    arbre = ast.parse(RAPIDE.read_text(encoding="utf-8"))
    for noeud in ast.walk(arbre):
        if isinstance(noeud, ast.FunctionDef) and noeud.name == "_decider":
            for sous in ast.walk(noeud):
                cibles = getattr(sous, "targets", None) or []
                if (isinstance(sous, ast.Assign)
                        and any(getattr(t, "id", "") == "regles" for t in cibles)):
                    return [e.elts[0].value for e in sous.value.elts
                            if isinstance(e, ast.Tuple)]
    raise AssertionError("liste `regles` introuvable dans _decider")


def test_relachee_est_le_dernier_code_qualifiant_de_la_chaine():
    """L'appelant ecarte `RELACHEE` quand la remise ne vise pas son scope : cela
    ne vaut que si AUCUN code qualifiant ne vient apres dans la chaine (sinon
    l'ecart reel serait avale). C'est cet ordre qui rend la borne sure."""
    codes = [c for c in _ordre_des_regles() if c in CODES_QUALIFICATION]
    assert codes, "aucun code qualifiant dans la chaine"
    assert codes[-1] == "RELACHEE", codes


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(pytest.main([__file__, "-q"]))
