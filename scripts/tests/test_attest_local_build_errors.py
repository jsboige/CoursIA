#!/usr/bin/env python3
"""Le champ `errors[]` de l'organe d'attestation Lean (#26480, point 3a).

Ce que ces tests tiennent :

1. **Chaque ligne `error:` est extraite**, avec son numero de ligne et le
   CONTEXTE qui suit -- le detail du diagnostic Lean est sur les lignes
   suivantes, pas sur la ligne `error:` elle-meme. Sans ce contexte, l'erreur
   extraite est un titre sans contenu.
2. Une sortie sans erreur ne produit **aucune** erreur (le champ est vide,
   pas absent).
3. L'extraction est une **lecture** : le texte d'origine n'est pas reecrit.
4. Le champ est **borne** : une sortie qui contient des centaines d'erreurs
   n'en fait pas exploser le payload.

Run: python -m pytest scripts/tests/test_attest_local_build_errors.py
"""
from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lean"))

import attest_local_build as alb  # noqa: E402

BUILD_OUTPUT = """\
Replaying 3 reference(s) ...
error: 'Nat.add' has type
  Nat → Nat → Nat
but '_' has type
  Int
error: failed to synthesize `DecidableEq Nat`
  (hint: `Nat.decEq` is a theorem)
"""


def test_chaque_ligne_error_est_extraite():
    found = alb.extract_errors(BUILD_OUTPUT)
    assert len(found) == 2
    assert found[0]["text"].startswith("error: 'Nat.add'")
    assert found[1]["text"] == "error: failed to synthesize `DecidableEq Nat`"


def test_le_contexte_suit_la_ligne_erreur():
    """Le detail du diagnostic est sur les lignes SUIVANTES."""
    found = alb.extract_errors(BUILD_OUTPUT)
    context = found[0]["context"]
    assert context[0].strip() == "Nat → Nat → Nat"
    assert "Nat.decEq" in found[1]["context"][0]


def test_le_numero_de_ligne_est_porte():
    found = alb.extract_errors(BUILD_OUTPUT)
    numbers = [entry["line_number"] for entry in found]
    assert numbers == [2, 6]


def test_une_sortie_sans_erreur_ne_produit_rien():
    assert alb.extract_errors("Build completed successfully.") == []
    assert alb.extract_errors("") == []


def test_le_texte_d_origine_n_est_pas_reecrit():
    """L'extraction est une lecture : rien n'est reecrit dans la sortie."""
    texte = "error: boom\n"
    alb.extract_errors(texte)
    assert texte == "error: boom\n"


def test_le_nombre_d_erreurs_est_borne():
    sortie = "".join("error: e{}\n".format(i) for i in range(200))
    found = alb.extract_errors(sortie, limit=10)
    assert len(found) == 10


def test_le_contexte_est_borne():
    sortie = "error: boom\n" + "".join("l{}\n".format(i) for i in range(50))
    found = alb.extract_errors(sortie, context_lines=2)
    assert len(found[0]["context"]) == 2


def test_le_champ_errors_atteint_le_payload_du_build(monkeypatch):
    """Le champ `errors[]` atteint le payload -- c'est la livraison du point 3a.

    Le build n'est pas lance : `_run` et la lecture des fichiers sont
    remplacees, seule la construction du payload est eprouvee.
    """
    class _Proc:
        returncode = 1
        stdout = "{}"
        stderr = ""

    monkeypatch.setattr(alb, "_run", lambda *a, **k: _Proc())
    monkeypatch.setattr(
        alb, "_read_if_present",
        lambda path: BUILD_OUTPUT if "stderr" in str(path) else "",
    )
    payload = alb.run_lake_build(Path("C:/faux/lake"), 10.0)
    assert len(payload["errors"]) == 2
    assert payload["errors"][0]["text"].startswith("error: 'Nat.add'")
    # La queue reste en place : l'extraction s'y AJOUTE, elle ne la remplace
    # pas (une queue peut contenir le debut du diagnostic).
    assert "error:" in payload["stderr_tail"]
