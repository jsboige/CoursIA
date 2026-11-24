"""Coeur du service MDP — iteration de la politique (Epic AIMA-Gateway #19571).

Reprise auto-contenue de l'iteration de la politique du carnet phare
``RL/RL-05-MDP-Programmation-Dynamique-Q-Learning-Python.ipynb`` (AIMA ch. 14,
programmation dynamique sur MDP : evaluation de politique + amelioration
gloutonne, en alternance jusqu'a stabilisation). Le service est testable hors
kernel et hors notebook : aucun import du carnet.

Contrat  ``POST /rl/mdp-policy-iteration``
------------------------------
Meme corps que l'iteration de la valeur (``states``, ``actions``, ``T``, ``R``,
``gamma``, ``theta``, ``max_iterations``) ::

    {
      "states":  ["s0", "s1"],
      "actions": ["a0", "a1"],
      "T":  {"s0": {"a0": {"s0": 0.5, "s1": 0.5}, ...}, "s1": {...}},
      "R":  {"s0": {"a0": 1.0, "a1": -1.0}, "s1": {...}},
      "gamma": 0.9,
      "theta": 1e-6,
      "max_iterations": 100
    }

- ``states`` / ``actions`` / ``T`` / ``R`` / ``gamma`` : meme contrat que
  ``/rl/mdp-value-iteration`` (MDP complet, ``T[s][a]`` normalise,
  ``0 <= gamma < 1``).
- ``theta`` : seuil de convergence de l'evaluation de politique interne.
- ``max_iterations`` : plafond de **cycles d'amelioration** (chacun = une
  evaluation de politique complete + une amelioration gloutonne).

Reponse (JSON, HTTP 200) ::

    {
      "status": "ok",
      "policy":  {"s0": "a0", "s1": "a1"},
      "value":   {"s0": 8.3, "s1": -5.1},
      "improvement_steps": 4,
      "converged": true,
      "n_states": 2
    }

- ``policy`` : politique optimale (stabilisee par amelioration gloutonne).
- ``value`` : fonction de valeur de cette politique (``V*`` a convergence).
- ``improvement_steps`` : nombre de cycles d'amelioration effectues.
- ``converged`` : ``true`` si la politique est stable avant ``max_iterations``.

Sur un meme MDP, l'iteration de la politique et de la valeur convergent vers la
**meme** politique optimale et la **meme** valeur : l'iteration de la politique
l'atteint typiquement en **moins** de cycles (chacun resout une evaluation
complete), d'ou le discriminant mesurable entre les deux services.

Entree hors contrat : ``{"status": "invalid", "error": ...}`` — **le service ne
leve jamais d'exception**.
"""

from __future__ import annotations

from typing import Any

# Seuil d'egalite flottante pour la normalisation des distributions de T.
TOL = 1e-6


class MdpInputError(ValueError):
    """Entree hors contrat : le service repond ``status: invalid``."""


def _is_number(x: Any) -> bool:
    """Vrai si ``x`` est un reel (int/float) et non un bool."""
    return isinstance(x, (int, float)) and not isinstance(x, bool)


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


def _evaluate_policy(
    states: list[str],
    actions: list[str],
    T: dict[str, dict[str, dict[str, float]]],
    R: dict[str, dict[str, float]],
    gamma: float,
    pi: dict[str, str],
    theta: float,
    max_iterations: int,
    V0: dict[str, float] | None = None,
) -> dict[str, float]:
    """Evaluation de politique : ``V[s] = R[s][pi[s]] + gamma * E[V[s']]`` (iteratif).

    ``V0`` (optionnel) : valeur de depart — rechauffage a la valeur du cycle
    precedent, comme dans l'iteration de la politique canonique ; par defaut
    0 partout. Sans rechauffage, une evaluation a froid depuis 0 ne converge
    pas a la valeur exacte avant d'atteindre le plafond d'iterations.
    """
    V = {s: (V0[s] if V0 is not None else 0.0) for s in states}
    for _ in range(max_iterations):
        new_V: dict[str, float] = {}
        for s in states:
            a = pi[s]
            new_V[s] = R[s][a] + gamma * sum(T[s][a].get(sp, 0.0) * V[sp] for sp in states)
        delta = max(abs(new_V[s] - V[s]) for s in states)
        V = new_V
        if delta < theta:
            break
    return V


def policy_iteration(
    states: list[str],
    actions: list[str],
    T: dict[str, dict[str, dict[str, float]]],
    R: dict[str, dict[str, float]],
    gamma: float,
    theta: float,
    max_iterations: int,
) -> tuple[dict[str, str], dict[str, float], int, bool]:
    """Iteration de la politique : evaluation + amelioration gloutonne en alternance.

    Retourne ``(politique, valeur, improvement_steps, converge)``. La politique
    est initialisee a la premiere action dans chaque etat, puis alterne evaluation
    de politique (complete) et amelioration gloutonne jusqu'a stabilisation.
    """
    pi = {s: actions[0] for s in states}
    V = {s: 0.0 for s in states}
    improvement_steps = 0
    converged = False
    for _ in range(max_iterations):
        V = _evaluate_policy(states, actions, T, R, gamma, pi, theta, max_iterations, V0=V)
        new_pi: dict[str, str] = {}
        changed = False
        for s in states:
            new_pi[s] = max(
                actions,
                key=lambda a: R[s][a] + gamma * sum(T[s][a].get(sp, 0.0) * V[sp] for sp in states),
            )
            if new_pi[s] != pi[s]:
                changed = True
        pi = new_pi
        improvement_steps += 1
        if not changed:
            converged = True
            break
    return pi, V, improvement_steps, converged


def run(payload: Any) -> dict[str, Any]:
    """Point d'entree du service : valide le corps, iterer, repond au contrat.

    Ne leve jamais d'exception : tout echec de validation devient
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
        max_iterations = payload.get("max_iterations", 100)

        if not _is_number(theta) or theta <= 0:
            return {"status": "invalid", "error": "theta: seuil strictement positif attendu"}
        if not _is_number(max_iterations) or max_iterations < 1:
            return {"status": "invalid", "error": "max_iterations: entier >= 1 attendu"}

        _check_mdp(states, actions, T, R, gamma)
        policy, value, steps, converged = policy_iteration(
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
        "improvement_steps": steps,
        "converged": converged,
        "n_states": len(states),
    }
