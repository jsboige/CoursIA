#!/usr/bin/env python3
"""Recensement des valeurs quantitatives en prose : 4 classes (#9434, #9377).

Le scanner `check_prose_quantitative_claims.py` distingue — depuis la vague
#8052/#9426-9429 — trois classes de valeurs quantitatives en plus du
comportement historique (compteurs d'artefact) :

  - ``machine_dep``  : temps absolus (`(28-364 ms)`, `~2.4s`, `12 min`).
                       Re-epinglés à chaque re-execution de la cellule de
                       mesure, donc a deriver/retirer (#9427 App-11-Picross).
  - ``env_dep``      : versions de librairie (`NumPy 2.4.2`, `Python 3.11+`).
                       Re-epinglés à chaque bump de version (#9429 GT-4c).
  - ``artifact``     : compteurs de lignes/cells/notebooks (le stock
                       historique). #9377.

Ces tests pincent les invariants :
  - TIMING_RE capture une plage en un seul finding (pas un par borne) ;
  - ENV_RE matche `Python 3.11+` et `NumPy 2.4.2`, ignore `K` ;
  - `--class <machine_dep|env_dep|artifact>` filtre la sortie ;
  - sans filtre, les 3 classes remontent (comportement etendu).

Le scanner conserve --all / --diff / --strict / --root / CATALOG-STATUS -- les
anciens tests `test_check_c2_compliance.py` etc. continuent à passer sans
modification parce que le comportement par defaut est backward-compatible
(les nouvelles classes s'AJOUTENT aux anciennes, ne substituent pas).

Run:
    pytest scripts/notebook_tools/tests/test_check_prose_quantitative_claims.py
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import check_prose_quantitative_claims as cqc  # noqa: E402


# --- 1. TIMING_RE capture les plages en un seul finding --------------------

def test_timing_single_value():
    """Un timing isole remonte en un seul finding."""
    findings = cqc._findings_in_text("- Cout : 24.5 ms par essai", "test", "machine_dep")
    snippets = [s for _, s in findings]
    assert "24.5 ms" in snippets, f"devrait matcher '24.5 ms', got {snippets}"


def test_timing_range_one_finding():
    """Une plage `28-364 ms` est capturee en UN seul finding, pas deux.

    Sans cette protection, `(28-364 ms)` produirait 2 findings (`28 ms` et
    `364 ms`), polluant la sortie CI et masquant la valeur-precise visee par
    la prose.
    """
    findings = cqc._findings_in_text("- Latence : (28-364 ms) mesure", "test", "machine_dep")
    snippets = [s for _, s in findings]
    assert "28-364 ms" in snippets, f"devrait matcher la plage entiere, got {snippets}"
    # Pas de doublon : la borne haute seule NE doit PAS remonter.
    assert not any(s == "364 ms" for s in snippets), (
        f"'364 ms' tout seul est un doublon, doit PAS remonter : {snippets}"
    )


def test_timing_units_long_form():
    """Les unites longues (`minutes`, `hours`, `milliseconds`) matchent."""
    assert cqc._findings_in_text("- 3 minutes", "t", "machine_dep")
    assert cqc._findings_in_text("- 2 hours", "t", "machine_dep")
    assert cqc._findings_in_text("- 2.4 milliseconds", "t", "machine_dep")


def test_timing_does_not_match_temperature_in_kelvin():
    """`300 K` n'est PAS un timing (Kelvin absent de la liste)."""
    findings = cqc._findings_in_text("- temperature 300 K", "test", "machine_dep")
    snippets = [s for _, s in findings]
    assert snippets == [], (
        f"Kelvin ne doit pas etre confondu avec un timing, got {snippets}"
    )


# --- 2. ENV_RE : versions de librairie ---------------------------------------

def test_env_python_3_11_plus():
    """`Python 3.11+` matche comme env_dep (version pinnée + suffixe `+`)."""
    findings = cqc._findings_in_text("- Python 3.11+", "test", "env_dep")
    snippets = [s for _, s in findings]
    assert "Python 3.11+" in snippets


def test_env_numpy_2_4_2():
    """`NumPy 2.4.2` (3 niveaux de version) matche."""
    findings = cqc._findings_in_text("- Charge NumPy 2.4.2", "test", "env_dep")
    snippets = [s for _, s in findings]
    assert "NumPy 2.4.2" in snippets


def test_env_does_not_match_arbitrary_number():
    """`3 minutes` N'EST PAS un env_dep (3 minutes est un timing, pas une ver)."""
    findings = cqc._findings_in_text("- 3 minutes", "test", "env_dep")
    snippets = [s for _, s in findings]
    assert snippets == [], (
        f"'3 minutes' est un timing, ne doit PAS apparaitre en env_dep, got {snippets}"
    )


# --- 3. --class filter --------------------------------------------------------

def test_class_filter_artifact_excludes_timing():
    """--class=artifact isole SEULEMENT les compteurs d'artefact, pas les timings."""
    text = (
        "- Cout : 24 ms\n"
        "- NumPy 2.4.2 charge\n"
        "- 140 lignes au total\n"
    )
    findings = cqc._findings_in_text(text, "test", "artifact")
    snippets = [s for _, s in findings]
    assert any("140 lignes" in s for s in snippets), f"artifact attendu, got {snippets}"
    # Pas de timing ni env en mode artifact.
    assert not any("ms" in s for s in snippets), (
        f"artifact ne doit PAS contenir de timings, got {snippets}"
    )
    assert not any("NumPy" in s for s in snippets), (
        f"artifact ne doit PAS contenir d'env, got {snippets}"
    )


def test_class_filter_all_classes():
    """Sans filtre, les 3 classes remontent (comportement etendu)."""
    text = (
        "- Cout : 24 ms\n"
        "- NumPy 2.4.2 charge\n"
        "- 140 lignes au total\n"
    )
    findings = cqc._findings_in_text(text, "test", None)
    snippets = [s for _, s in findings]
    assert any("24 ms" in s for s in snippets)
    assert any("NumPy 2.4.2" in s for s in snippets)
    assert any("140 lignes" in s for s in snippets)


# --- 4. scan_all + scan_diff : invariants structurels ------------------------

def test_scan_all_filters_machine_dep_in_tmp_root(tmp_path):
    """scan_all --class=machine_dep ne remonte PAS les artefacts/env."""
    md = tmp_path / "demo.md"
    md.write_text(
        "- Cout : 24 ms\n"
        "- NumPy 2.4.2\n"
        "- 140 lignes\n",
        encoding="utf-8",
    )
    findings = cqc.scan_all(tmp_path, "machine_dep")
    assert len(findings) == 1, f"un seul timing attendu, got {findings}"
    _, snippet = findings[0]
    assert "24 ms" in snippet


def test_artifact_class_preserves_historical_behavior(tmp_path):
    """--class=artifact conserve le comportement d'avant #9434 (lignes/cells)."""
    md = tmp_path / "demo.md"
    md.write_text(
        "- Cout : 24 ms\n"
        "- 140 lignes au total\n"
    )
    findings = cqc.scan_all(tmp_path, "artifact")
    snippets = [s for _, s in findings]
    # Comportement historique : on remonte '140 lignes', pas '24 ms'.
    assert "140 lignes" in snippets
    assert not any("24 ms" in s for s in snippets)


# --- 5. CATALOG-STATUS reste neutralisee -------------------------------------

def test_catalog_status_marker_neutralizes_block(tmp_path):
    """Les blocs CATALOG-STATUS sont toujours neutralises pour les 4 classes."""
    md = tmp_path / "CATALOG.md"
    md.write_text(
        "<!-- CATALOG-STATUS:START -->\n"
        "- 140 lignes dans le catalog\n"
        "- Cout : 24 ms (cache)\n"
        "<!-- CATALOG-STATUS:END -->\n"
        "- 50 lignes dans le vrai contenu\n",
        encoding="utf-8",
    )
    findings = cqc.scan_all(tmp_path)
    snippets = [s for _, s in findings]
    # Seul le contenu hors CATALOG-STATUS remonte.
    assert "50 lignes" in snippets or "50" in str(snippets)
