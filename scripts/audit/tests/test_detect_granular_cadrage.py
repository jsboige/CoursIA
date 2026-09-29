"""Tests pour detect_granular_cadrage.py -- issue #15573."""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

# Chargement direct du module (evite les problemes de path avec espaces)
_MODULE_PATH = Path(__file__).resolve().parents[1] / "detect_granular_cadrage.py"
_spec = importlib.util.spec_from_file_location("detect_granular_cadrage", _MODULE_PATH)
_mod = importlib.util.module_from_spec(_spec)
sys.modules["detect_granular_cadrage"] = _mod
_spec.loader.exec_module(_mod)
detect = _mod.detect
PATTERNS = _mod.PATTERNS


def test_cadrage_par_fichier():
    text = "Pour chaque notebook, ajouter une section. Une PR par fichier."
    label, excerpt = detect(text)
    assert label == "cadrage-par-item"
    assert "fichier" in excerpt or "notebook" in excerpt


def test_pour_chaque_lake():
    text = "Appliquer la jonction pour chaque lake du cluster."
    label, excerpt = detect(text)
    assert label == "pour-chaque"
    assert "lake" in excerpt


def test_par_item():
    text = "Le cadrage prescrit un grain par item, sur N entrees."
    label, _ = detect(text)
    assert label == "par-item"


def test_liste_de_prs():
    text = "Les sous-taches apparaissent dans la liste de PRs du tracker."
    label, _ = detect(text)
    assert label == "liste-de-prs"


def test_couper_en_N_pr():
    text = "Couper en 4 PR le sweep de la campagne."
    label, _ = detect(text)
    assert label == "couper-en-N"


def test_sweep_n_fichiers():
    text = "Sweep des referents -- 13 fichiers, mesures avant/apres."
    label, _ = detect(text)
    assert label == "sweep-N-fichiers"


def test_no_match():
    text = "Une issue ordinaire sans cadrage granulaire evident."
    assert detect(text) is None


def test_patterns_non_vides():
    """Garde-fou : si quelqu'un retire un motif, le test echoue."""
    labels = [label for _, label in PATTERNS]
    assert "cadrage-par-item" in labels
    assert "pour-chaque" in labels
    assert "par-item" in labels
    assert "liste-de-prs" in labels


def test_no_double_match():
    """Un texte declenche au plus un motif (premier match gagne)."""
    text = "Pour chaque lake, livrer une PR par lake ; couper en 3 PR."
    label, _ = detect(text)
    assert label in {"pour-chaque", "cadrage-par-item", "couper-en-N"}


def test_case_insensitive():
    text = "UNE PR PAR FICHIER du dossier X."
    label, _ = detect(text)
    assert label == "cadrage-par-item"
