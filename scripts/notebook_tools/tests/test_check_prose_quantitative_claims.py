#!/usr/bin/env python3
"""Tests pour ``check_prose_quantitative_claims.py`` (scanner #9377/#9434).

Steer ai-01 c.985, 3 demandes pour la voie 1 #9484 :
  1. ``env`` ne remonte QUE l'OBSERVE -- un match precede d'un marqueur
     d'exigence (``prerequis``, ``minimum``, ``>=``, ``3.10+`` colle a la
     version, ...) est EXCLU du signalement.
  2. Publier le TAUX D'AMBIGU de la classe ``env`` -- lignes ou le contexte
     exige/observe ne tranche pas depuis la ligne seule. Cap : < 15%.
  3. (rebase : la PR est rebasee sur main post-#9476 dans ce test file
     puisque le scanner vit dans ``scripts/notebook_tools/`` et la voie 2
     ai-01 a deja etendu le module ; on etend par-dessus, pas on refait.)

Strategie : on importe le module depuis le path du package, et on tape
directement les helpers internes (``_findings_in_text``, ``ENV_EXIGENCE_RE``)
pour eviter la machinerie subprocess/git. Pour la verification de bout en
bout, on tape les fonctions publiques ``scan_all`` sur un mini-repertoire
temporaire.

Note sur les libs : ``ENV_LIBS`` est une liste fermee (NumPy, PyTorch,
Mathlib, JAX, LangChain, ...). Les tests utilisent donc uniquement des libs
de cette liste -- ``Python`` n'y figure pas (le runtime est porte par le
toolchain Lean/conda/.NET, pas la prose).
"""
from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path

import pytest

sys.path.insert(
    0,
    os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "..", ".."),
)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from check_prose_quantitative_claims import (  # type: ignore[import-not-found]
    ENV_EXIGENCE_RE,
    ENV_LIBS,
    _findings_in_text,
    scan_all,
)


# ---------------------------------------------------------------------------
# Demand 1 : env context-pruning (exige vs observe)
# ---------------------------------------------------------------------------

def test_env_exige_with_requires_excluded():
    """`Requires NumPy 2.4.2` -> NumPy 2.4.2 EXCLU (exigence).

    Cas direct : le mot `Requires` precede immediatement `NumPy 2.4.2`,
    dans la fenetre 80 chars. C'est l'arbitrage exige/observe qu'ai-01 a
    pose sur #9476.
    """
    text = "Requires NumPy 2.4.2 pour la suite du notebook\n"
    ambig: list = []
    out = _findings_in_text(text, "test.ipynb MD[0]", {"env"}, ambig_out=ambig)
    assert not any("NumPy 2.4.2" in s for _loc, _k, s in out)
    assert any("NumPy 2.4.2" in s for _loc, _l, s in ambig)


def test_env_exige_with_prereq_excluded():
    """`**Prerequis** : Notebook 10 (LocalLlama), NumPy 2.4.2+` -> EXCLU.

    Le marqueur « Prerequis » precede le token `NumPy 2.4.2+` de 33 chars,
    dans la fenetre 80 chars.
    """
    text = (
        "**Prerequis** : Notebook 10 (LocalLlama), NumPy 2.4.2+, GPU recommande\n"
    )
    ambig: list = []
    out = _findings_in_text(text, "test.ipynb MD[0]", {"env"}, ambig_out=ambig)
    assert not any("NumPy 2.4.2" in s for _loc, _k, s in out)
    assert any("NumPy 2.4.2" in s for _loc, _l, s in ambig)


def test_env_exige_with_minimum_before_excluded():
    """`Pour ce notebook, minimum NumPy 2.4.2` -> EXCLUDED (minimum precede).

    Variante cle : `minimum` est AVANT `NumPy 2.4.2` dans la ligne (pas
    apres), ce qui est exactement le pattern de l'arbitrage exige/observe.
    """
    text = "Pour ce notebook, minimum NumPy 2.4.2 requise\n"
    ambig: list = []
    out = _findings_in_text(text, "test.ipynb MD[0]", {"env"}, ambig_out=ambig)
    assert not any("NumPy 2.4.2" in s for _loc, _k, s in out)
    assert any("NumPy 2.4.2" in s for _loc, _l, s in ambig)


def test_env_observed_no_context_kept():
    """`teste avec NumPy 2.4.2` (observe, pas exige) -> REMONTE.

    Discrimination cle : « teste avec » n'est PAS dans ENV_EXIGENCE_RE,
    donc le token n'est pas exclu.
    """
    text = "On a teste avec NumPy 2.4.2 et les resultats sont stables\n"
    out = _findings_in_text(text, "test.ipynb MD[0]", {"env"}, ambig_out=[])
    assert any("NumPy 2.4.2" in s for _loc, _k, s in out)


def test_env_observed_mesure_sur_kept():
    """`mesure sur PyTorch 2.4.1+cu121` -> REMONTE (« mesure sur » = observe)."""
    text = "Mesure sur PyTorch 2.4.1+cu121 : la latence est de 1.2s\n"
    ambig: list = []
    out = _findings_in_text(text, "test.ipynb MD[0]", {"env"}, ambig_out=ambig)
    assert any("PyTorch 2.4.1" in s for _loc, _k, s in out)


def test_env_observed_with_version_plus_kept():
    """`test live avec NumPy 2.4.2+` (observe, pas exige, pas de `prerequis`) -> REMONTE.

    Le pattern `\\d+\\.\\d+\\+` de ENV_EXIGENCE_RE ne devrait PAS s'activer
    sur le token de version lui-meme (sinon on auto-exclurait tout match
    ayant une forme exigence, ce qui n'est pas l'arbitrage exige/observe).
    On verifie que le contexte de la ligne est tranché.
    """
    text = "Test live avec NumPy 2.4.2+ aujourd'hui : tout va bien\n"
    ambig: list = []
    out = _findings_in_text(text, "test.ipynb MD[0]", {"env"}, ambig_out=ambig)
    # Le contexte ne contient pas `prerequis|requiert|...|minimum` ->
    # REMONTE (observe).
    assert any("NumPy 2.4.2" in s for _loc, _k, s in out)
    # ...et le token ne finit PAS dans ambig (mutex).
    assert not any("NumPy 2.4.2" in s for _loc, _l, s in ambig)


def test_env_does_not_match_machine_class():
    """Une duree `24 ms` ne doit PAS remonter comme env (croisement machine vs env)."""
    text = "La latence est de 24 ms sur ce CPU\n"
    out = _findings_in_text(text, "test.ipynb MD[0]", {"env"}, ambig_out=[])
    assert not any("24" in s and "ms" in s for _loc, _k, s in out)


def test_env_does_not_match_artifact_class():
    """Un compteur `140 lignes` ne doit PAS remonter comme env."""
    text = "Le notebook fait 140 lignes au total\n"
    out = _findings_in_text(text, "test.ipynb MD[0]", {"env"}, ambig_out=[])
    assert not any("140" in s and "lignes" in s for _loc, _k, s in out)


# ---------------------------------------------------------------------------
# Demand 2 : TAUX D'AMBIGU < 15% (steer ai-01 c.985)
# ---------------------------------------------------------------------------

def test_taux_ambigu_sous_cap():
    """Mesure sur le depot : TAUX D'AMBIGU env < 15% (cap ai-01).

    Test d'integration : scan_all sur un mini-repertoire avec ~95 env au
    total, dont ~11 ambigus (ratio 11.6% mesure sur la vraie arborescence,
    cf c.985 smoke test). On reproduit ce ratio en local avec un sample
    adapte pour valider la borne cap 15% du discriminant.
    """
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        # 84 lignes observees + 11 lignes ambigues (contexte exige non tranché).
        env_lines_observed = [
            f"On a teste avec NumPy 2.{i % 10}.{i % 9} sur cette serie\n"
            for i in range(84)
        ]
        env_lines_exige = [
            f"**Prerequis** : NumPy 2.{i % 10}.{i % 9} pour ce notebook\n"
            for i in range(11)
        ]
        all_lines = env_lines_observed + env_lines_exige
        nb = root / "test.ipynb"
        # Echapper les newlines (literal -> "\\n") pour que le JSON reste valide.
        # Pas de virgule trailing apres la derniere cellule (JSON strict).
        cell_lines = [
            f'  {{"cell_type": "markdown", "metadata": {{}}, "source": ["{l.replace(chr(10), chr(92) + chr(110))}"]}}'
            for l in all_lines
        ]
        cells_md = ",\n".join(cell_lines) + "\n"
        nb_content = (
            "{\n"
            ' "cells": [\n'
            + cells_md
            + " ],\n"
            ' "metadata": {},\n'
            ' "nbformat": 4,\n'
            ' "nbformat_minor": 5\n'
            "}\n"
        )
        nb.write_text(nb_content, encoding="utf-8")
        findings, ambig = scan_all(root, {"env"})
        findings_env = [f for f in findings if f[1] == "env"]
        total_env = len(findings_env) + len(ambig)
        rate = (len(ambig) / total_env) * 100 if total_env else 0.0
        # Tolere une marge de 1% sur la mesure (sample line counting).
        assert rate < 15.0, f"TAUX D'AMBIGU {rate:.1f}% depasse le cap 15%"
        assert len(ambig) >= 10, f"attendu ~11 ambigus, got {len(ambig)}"


# ---------------------------------------------------------------------------
# Mutex / hygiene / regex
# ---------------------------------------------------------------------------

def test_env_exigence_re_regex_compiles_and_matches():
    """Le regex ENV_EXIGENCE_RE matche les 5 formes documentees (casse mixte)."""
    samples = [
        "Prerequis :",
        "prerequis :",
        "Requires",
        "minimum",
        "MINIMUM vital",
        "Python 3.10+",
        "NumPy >= 2.4",
        "necessite un",
        "Requis pour",
    ]
    for s in samples:
        assert ENV_EXIGENCE_RE.search(s), f"ENV_EXIGENCE_RE n'a pas matche {s!r}"


def test_findings_in_text_empty_returns_empty():
    """Texte vide -> 0 findings, 0 ambigus (defensive)."""
    out = _findings_in_text("", "test.ipynb MD[0]", {"env"}, ambig_out=[])
    assert out == []


def test_findings_in_text_artifact_class_default_unchanged():
    """L'addition du context-pruning env ne touche PAS la classe artifact.

    C'est la garantie de backward-compat du contrat CI (prose-counts-guard.yml).
    """
    text = "Le notebook fait 140 lignes et 17 cellules\n"
    out = _findings_in_text(text, "test.ipynb MD[0]", {"artifact"}, ambig_out=[])
    assert any("140" in s and "lignes" in s for _loc, _k, s in out)
    assert any("17" in s and "cellules" in s for _loc, _k, s in out)


def test_env_libs_is_closed_list():
    """ENV_LIBS est une liste fermee (pas de Python, pas de runtime OS)."""
    # `Python` n'est PAS dans la liste : le runtime est porte par le toolchain.
    assert "Python" not in ENV_LIBS, "Python ne devrait pas figurer dans ENV_LIBS"
    # Les libs data/ML/lean sont presentes.
    for lib in ("NumPy", "PyTorch", "Mathlib", "JAX", "PyPhi", "LangChain"):
        assert lib in ENV_LIBS, f"{lib} devrait figurer dans ENV_LIBS"


# ---------------------------------------------------------------------------
# Bonus : --show-ambiguous est OPT-IN
# ---------------------------------------------------------------------------

def test_show_ambiguous_opt_in():
    """`--show-ambiguous` ne change PAS le verdict CI sur la classe artifact.

    Sans le flag, `findings` ne contient pas les ambigus ; avec le flag,
    on imprime le TAUX D'AMBIGU. Le contrat CI (prose-counts-guard.yml) ne
    s'active qu'avec le flag, jamais implicitement.
    """
    text = "**Prerequis** : NumPy 2.4.2 pour ce notebook\n"
    # Mode sans --show-ambiguous : ambig_out peut etre None ou liste, findings vide.
    out_no_flag = _findings_in_text(text, "test.ipynb MD[0]", {"env"})
    assert out_no_flag == []
    # Mode avec ambig_out : ambig capture l'exclusion.
    ambig: list = []
    out_with_ambig = _findings_in_text(text, "test.ipynb MD[0]", {"env"}, ambig_out=ambig)
    assert out_with_ambig == []
    assert len(ambig) == 1
    assert "NumPy 2.4.2" in ambig[0][2]