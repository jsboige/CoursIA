# -*- coding: utf-8 -*-
"""Coeur du service Kernel Gateway CFR (OpenSpiel).

Logique reprise du carnet phare ``GameTheory-13-ImperfectInfo-CFR-Python.ipynb``
(serie GameTheory : CFR -- Counterfactual Regret Minimization -- sur jeu a
information imparfaite via OpenSpiel), adaptee au contrat REST JSON du
service notebook-http (issue #21104, pli 0 de l'Epic #19571).

Contrat :
    POST /gametheory/cfr  {"game": "kuhn_poker", "iterations": 300}
    -> {"status": "ok", "game": ..., "iterations": ...,
        "exploitability": float, "nash_conv": float, "policy": {...}}
"""
from __future__ import annotations

from typing import Any, Dict

import pyspiel

# CFR exige un arbre sequentiel : les jeux a coup simultane (forme normale)
# se chargent via ``turn_based_simultaneous_game``, la transformation
# canonique d'OpenSpiel (l'ordre des coups devient sequentiel, l'information
# reste imparfaite).
GAME_LOADERS = {
    "kuhn_poker": "kuhn_poker",
    "leduc_poker": "leduc_poker",
    "matrix_rps": "turn_based_simultaneous_game(game=matrix_rps())",
}
GAMES = tuple(GAME_LOADERS)
DEFAULT_ITERATIONS = 300
MAX_ITERATIONS = 5000


def _invalid(message: str) -> Dict[str, Any]:
    return {"status": "invalid", "error": message}


def _valid_iterations(value: Any) -> bool:
    # bool est sous-classe de int (True == 1) : exclu explicitement pour que
    # ``{"iterations": true}`` soit une entree invalide, pas 1 iteration.
    return (
        isinstance(value, int)
        and not isinstance(value, bool)
        and 1 <= value <= MAX_ITERATIONS
    )


def serialize_policy(game: Any, policy: Any) -> Dict[str, Dict[str, float]]:
    """Strategie moyenne par etat d'information (parcours de l'arbre).

    Les etats de chance sont traverses sur chaque outcome, les etats
    terminaux ignores, chaque etat d'information n'apparait qu'une fois.
    """
    policy_by_infoset: Dict[str, Dict[str, float]] = {}

    def walk(state: Any) -> None:
        if state.is_terminal():
            return
        if state.is_chance_node():
            for action, _probability in state.chance_outcomes():
                walk(state.child(action))
            return
        key = state.information_state_string()
        if key not in policy_by_infoset:
            probabilities = policy.action_probabilities(state)
            policy_by_infoset[key] = {
                state.action_to_string(action): round(float(probability), 6)
                for action, probability in probabilities.items()
            }
        for action in state.legal_actions():
            walk(state.child(action))

    walk(game.new_initial_state())
    return policy_by_infoset


def solve_cfr(game_name: Any, iterations: Any = None) -> Dict[str, Any]:
    """Resout un jeu par CFR et renvoie strategie moyenne + convergence.

    Retourne ``{"status": "invalid", "error": ...}`` pour toute entree hors
    contrat (jeu non supporte, iterations non entieres ou hors bornes), sans
    lever d'exception.
    """
    if not isinstance(game_name, str) or game_name not in GAME_LOADERS:
        return _invalid(
            "jeu non supporte: {!r} (supportes: {})".format(
                game_name, ", ".join(GAMES)
            )
        )
    if iterations is None:
        iterations = DEFAULT_ITERATIONS
    if not _valid_iterations(iterations):
        return _invalid(
            "iterations invalides: {!r} (entier entre 1 et {})".format(
                iterations, MAX_ITERATIONS
            )
        )

    game = pyspiel.load_game(GAME_LOADERS[game_name])
    solver = pyspiel.CFRSolver(game)
    for _ in range(iterations):
        solver.evaluate_and_update_policy()
    policy = solver.average_policy()
    return {
        "status": "ok",
        "game": game_name,
        "iterations": iterations,
        "exploitability": round(float(pyspiel.exploitability(game, policy)), 6),
        "nash_conv": round(float(pyspiel.nash_conv(game, policy)), 6),
        "policy": serialize_policy(game, policy),
    }