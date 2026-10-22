# -*- coding: utf-8 -*-
"""Tests du coeur du service CFR (hors kernel, hors gateway).

Executables tels quels : ``python test_openspiel_cfr_core.py`` ou ``pytest``.
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

# Le coeur est charge par CHEMIN DE FICHIER, pas par import de paquet : la
# suite partagee de scripts-tests.yml tourne en `--import-mode importlib`
# (pytest.ini addopts), ou le dossier du fichier de test n'est PAS ajoute a
# sys.path -- un `from openspiel_cfr_core import ...` y serait un
# ModuleNotFoundError a la collecte, qui avorte toute la session pytest et
# masque les autres resultats (mode de defaillance contre lequel ce workflow
# existe, cf. commentaire de l'etape "Run tests"). Meme motif que
# test_bg_tree_lock.py (chargement de tree_lock.py par chemin).
_CORE_PATH = Path(__file__).with_name("openspiel_cfr_core.py")
_spec = importlib.util.spec_from_file_location("openspiel_cfr_core", _CORE_PATH)
_core = importlib.util.module_from_spec(_spec)
sys.modules["openspiel_cfr_core"] = _core
_spec.loader.exec_module(_core)

DEFAULT_ITERATIONS = _core.DEFAULT_ITERATIONS
MAX_ITERATIONS = _core.MAX_ITERATIONS
solve_cfr = _core.solve_cfr


def test_kuhn_convergence():
    result = solve_cfr("kuhn_poker", 300)
    assert result["status"] == "ok"
    assert result["exploitability"] < 0.05
    # nash_conv = somme des regrets = 2 x exploitability (jeu a somme nulle,
    # 2 joueurs) ; les deux valeurs sont arrondies a 1e-6.
    assert result["nash_conv"] == pytest.approx(2 * result["exploitability"], abs=2e-6)
    assert result["policy"], "la strategie moyenne ne doit pas etre vide"


def test_more_iterations_improve_convergence():
    low = solve_cfr("kuhn_poker", 20)
    high = solve_cfr("kuhn_poker", 500)
    assert high["exploitability"] < low["exploitability"]


def test_policy_probabilities_sum_to_one():
    result = solve_cfr("kuhn_poker", 100)
    for infoset, actions in result["policy"].items():
        assert actions, infoset
        assert sum(actions.values()) == pytest.approx(1.0, abs=1e-4)


def test_deterministic():
    assert solve_cfr("kuhn_poker", 50) == solve_cfr("kuhn_poker", 50)


def test_matrix_rps_via_transform():
    result = solve_cfr("matrix_rps", 300)
    assert result["status"] == "ok"
    assert result["exploitability"] < 0.01


def test_leduc_runs():
    result = solve_cfr("leduc_poker", 50)
    assert result["status"] == "ok"
    assert len(result["policy"]) > 100


def test_default_iterations():
    assert solve_cfr("kuhn_poker")["iterations"] == DEFAULT_ITERATIONS


@pytest.mark.parametrize("game", ["poker", "", None, 42, "KUHN_POKER"])
def test_invalid_game(game):
    result = solve_cfr(game, 10)
    assert result["status"] == "invalid"
    assert "error" in result


@pytest.mark.parametrize(
    "iterations", [0, -1, MAX_ITERATIONS + 1, 10.5, "100", True]
)
def test_invalid_iterations(iterations):
    result = solve_cfr("kuhn_poker", iterations)
    assert result["status"] == "invalid"
    assert "error" in result


if __name__ == "__main__":
    # ``python test_openspiel_cfr_core.py`` execute la suite sans dependre de
    # la configuration pytest du depot (le module se charge par chemin).
    raise SystemExit(pytest.main([__file__, "-v", "-p", "no:cacheprovider"]))