"""Coeur du service MDP — iteration de la valeur (Epic AIMA-Gateway #19571).

Reprise auto-contenue de l'iteration de la valeur du carnet phare
``RL/RL-05-MDP-Programmation-Dynamique-Q-Learning-Python.ipynb`` (
programmation dynamique sur MDP : backups de Bellman + politique gloutonne).
Le service est testable hors kernel et hors notebook : aucun import du carnet.

Contrat  ``POST /rl/mdp-value-iteration``
------------------------------
Corps (JSON) ::

    {
      "states":  ["s0", "s1"],
      "actions": ["a0", "a1"],
      "T":  {"s0": {"a0": {"s0": 0.5, "s1": 0.5},
                   "a1": {"s1": 1.0},
                   ...},
             "s1": {...}},
      "R":  {"s0": {"a0": 1.0, "a1": -1.0},
             "s1": {...}},
      "gamma": 0.9,
      "theta": 1e-6,
      "max_iterations": 1000
    }

- ``states`` : liste de noms d'etats (non vide, sans doublon).
- ``actions`` : liste de noms d'actions (non vide, sans doublon).
- ``T`` : ``T[s][a][s'] = probabilite`` de passer de ``s`` a ``s'`` en jouant ``a``.
  Chaque ``T[s][a]`` doit etre une distribution sur les etats (entrees >= 0,
  somme ~ 1) ; toute paire ``(s, a)`` doit etre presente (MDP complet).
- ``R`` : ``R[s][a] = recompense immediate`` (reel quelconque), presente pour
  toute paire ``(s, a)``.
- ``gamma`` : facteur d'escompte, ``0 <= gamma < 1`` (garantit la convergence
  de l'iteration de la valeur).
- ``theta`` : seuil de convergence (max |V_new - V| < theta), > 0.
- ``max_iterations`` : plafond de securite (nombre maximal de backups).

Reponse (JSON, HTTP 200) ::

    {
      "status": "ok",
      "policy":  {"s0": "a0", "s1": "a1"},
      "value":   {"s0": 8.3, "s1": -5.1},
      "iterations": 47,
      "converged": true,
      "n_states": 2
    }

- ``policy`` : action gloutonne par etat pour la valeur calculee.
- ``value`` : approximation de la fonction de valeur optimale ``V*(s)``.
- ``iterations`` : nombre d'iterations de Bellman effectuees.
- ``converged`` : ``true`` si le seuil ``theta`` est atteint, y compris a la
  derniere iteration autorisee.

Entree hors contrat (cles manquantes, longueurs incoherentes, T non normalise,
gamma hors bornes, probabilite negative) : ``{"status": "invalid", "error": ...}``
pour les erreurs de validation traitees.
"""

from __future__ import annotations

import math
from typing import Any

# Seuil d'egalite flottante pour la normalisation des distributions de T.
TOL = 1e-6


class MdpInputError(ValueError):
    """Entree hors contrat : le service repond ``status: invalid``."""


def _is_number(x: Any) -> bool:
    """Vrai si ``x`` est un reel fini et non un bool."""
    if not isinstance(x, (int, float)) or isinstance(x, bool):
        return False
    try:
        return math.isfinite(x)
    except OverflowError:
        return False


def _check_mdp(
    states: Any,
    actions: Any,
    T: Any,
    R: Any,
    gamma: Any,
) -> None:
    """Valide la forme du MDP ; leve ``MdpInputError`` sinon."""
    if not isinstance(states, list) or not states:
        raise MdpInputError("states: liste de noms d'etats non vide requise")
    if len(set(states)) != len(states):
        raise MdpInputError("states: noms en double")
    if any(not isinstance(s, str) for s in states):
        raise MdpInputError("states: noms de type chaine attendus")

    if not isinstance(actions, list) or not actions:
        raise MdpInputError("actions: liste de noms d'actions non vide requise")
    if len(set(actions)) != len(actions):
        raise MdpInputError("actions: noms en double")
    if any(not isinstance(a, str) for a in actions):
        raise MdpInputError("actions: noms de type chaine attendus")

    if not isinstance(gamma, (int, float)) or isinstance(gamma, bool):
        raise MdpInputError("gamma: facteur d'escompte reel attendu")
    if not (0.0 <= gamma < 1.0):
        raise MdpInputError(f"gamma: {gamma} hors bornes (0 <= gamma < 1 attendu)")

    sset = set(states)

    if not isinstance(T, dict):
        raise MdpInputError("T: dictionnaire etat -> action -> {etat': prob} attendu")
    for s in states:
        if s not in T:
            raise MdpInputError(f"T: etat '{s}' manquant")
        if not isinstance(T[s], dict):
            raise MdpInputError(f"T['{s}']: dictionnaire action -> distribution attendu")
        for a in actions:
            if a not in T[s]:
                raise MdpInputError(f"T['{s}']['{a}']: distribution de transition manquante")
            dist = T[s][a]
            if not isinstance(dist, dict):
                raise MdpInputError(f"T['{s}']['{a}']: dictionnaire etat' -> prob attendu")
            for sp, p in dist.items():
                if sp not in sset:
                    raise MdpInputError(f"T['{s}']['{a}']: etat inconnu '{sp}'")
                if not _is_number(p) or p < 0:
                    raise MdpInputError(f"T['{s}']['{a}']['{sp}']: probabilite reelle >= 0 attendue")
            total = sum(dist.values())
            if abs(total - 1.0) > TOL:
                raise MdpInputError(
                    f"T['{s}']['{a}']: somme = {total:.6f}, distribution normalisee (somme ~ 1) attendue"
                )

    if not isinstance(R, dict):
        raise MdpInputError("R: dictionnaire etat -> action -> recompense attendu")
    for s in states:
        if s not in R:
            raise MdpInputError(f"R: etat '{s}' manquant")
        if not isinstance(R[s], dict):
            raise MdpInputError(f"R['{s}']: dictionnaire action -> recompense attendu")
        for a in actions:
            if a not in R[s]:
                raise MdpInputError(f"R['{s}']['{a}']: recompense manquante")
            if not _is_number(R[s][a]):
                raise MdpInputError(f"R['{s}']['{a}']: recompense reelle attendue")


def value_iteration(
    states: list[str],
    actions: list[str],
    T: dict[str, dict[str, dict[str, float]]],
    R: dict[str, dict[str, float]],
    gamma: float,
    theta: float,
    max_iterations: int,
) -> tuple[dict[str, str], dict[str, float], int, bool]:
    """Iteration de la valeur : backups de Bellman jusqu'a convergence.

    Retourne ``(politique, valeur, iterations, converge)`` ou ``politique[s]``
    est l'action gloutonne pour la valeur calculee, une approximation de ``V*(s)``.
    """
    V = {s: 0.0 for s in states}
    iterations = 0
    converged = False
    for _ in range(max_iterations):
        new_V: dict[str, float] = {}
        for s in states:
            best = -math.inf
            for a in actions:
                exp = R[s][a] + gamma * sum(T[s][a].get(sp, 0.0) * V[sp] for sp in states)
                if exp > best:
                    best = exp
            new_V[s] = best
        delta = max(abs(new_V[s] - V[s]) for s in states)
        V = new_V
        iterations += 1
        if delta < theta:
            converged = True
            break

    policy: dict[str, str] = {}
    for s in states:
        policy[s] = max(
            actions,
            key=lambda a: R[s][a] + gamma * sum(T[s][a].get(sp, 0.0) * V[sp] for sp in states),
        )
    return policy, V, iterations, converged


def run(payload: Any) -> dict[str, Any]:
    """Point d'entree du service : valide le corps, iterer, repond au contrat.

    Les erreurs de validation traitees deviennent
    ``{"status": "invalid", "error": ...}``.
    """
    if not isinstance(payload, dict):
        return {"status": "invalid", "error": "corps JSON objet attendu"}

    try:
        states = payload.get("states")
        actions = payload.get("actions")
        T = payload.get("T")
        R = payload.get("R")
        gamma = payload.get("gamma", 0.9)
        theta = payload.get("theta", 1e-6)
        max_iterations = payload.get("max_iterations", 1000)

        if not _is_number(theta) or theta <= 0:
            return {"status": "invalid", "error": "theta: seuil strictement positif attendu"}
        if not _is_number(max_iterations) or max_iterations < 1:
            return {"status": "invalid", "error": "max_iterations: entier >= 1 attendu"}

        _check_mdp(states, actions, T, R, gamma)
        policy, value, iterations, converged = value_iteration(
            states, actions, T, R, gamma, theta, int(max_iterations)
        )
    except MdpInputError as exc:
        return {"status": "invalid", "error": str(exc)}
    except (TypeError, ValueError, KeyError, IndexError) as exc:
        return {"status": "invalid", "error": f"MDP incoherent: {exc}"}

    return {
        "status": "ok",
        "policy": policy,
        "value": value,
        "iterations": iterations,
        "converged": converged,
        "n_states": len(states),
    }
