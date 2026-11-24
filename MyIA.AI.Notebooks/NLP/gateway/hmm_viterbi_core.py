"""Coeur du service HMM / Viterbi (pli 1 de l'Epic AIMA-Gateway #19571).

Reprise auto-contenue du decodage de Viterbi du carnet phare
``NLP/05-HMM-Viterbi.ipynb`` (AIMA ch. 14, raisonnement probabiliste sur la
duree), en **espace des logarithmes** pour la stabilite numerique. Le service
est testable hors kernel et hors notebook : aucun import du carnet.

Contrat  ``POST /nlp/viterbi``
------------------------------
Corps (JSON) ::

    {
      "states":       ["EnSoleil", "Pluie"],
      "observations": ["promenade", "magasin", "nettoyage"],
      "pi":           [0.6, 0.4],
      "A":            [[0.7, 0.3], [0.4, 0.6]],
      "B":            {"EnSoleil": {"promenade": 0.7, "magasin": 0.4,
                                    "nettoyage": 0.1},
                       "Pluie":    {"promenade": 0.1, "magasin": 0.4,
                                    "nettoyage": 0.6}}
    }

- ``states`` : liste de noms d'etats (non vide).
- ``observations`` : liste de symboles observes (non vide).
- ``pi`` : distribution initiale sur les etats (longueur = n_etats, somme ~ 1).
- ``A`` : matrice de transition n_etats x n_etats (entrees >= 0).
- ``B`` : emissions par etat, ``B[etat][symbole] = probabilite`` (>= 0).

Reponse (JSON, HTTP 200) ::

    {
      "status": "ok",
      "best_path":        ["EnSoleil", "EnSoleil", "Pluie"],
      "best_path_log_prob": -3.21,
      "observation_log_prob": -2.87,
      "n_states": 2,
      "n_observations": 3
    }

Un symbole absent de ``B[etat]`` vaut une emission de probabilite ``EPS``
(floor), pas une erreur : le decodage reste defini pour toute suite
d'observations. Entree hors contrat (cles manquantes, longueurs incoherentes,
probabilites negatives) : ``{"status": "invalid", "error": ...}`` -- le service
ne leve jamais d'exception.
"""

from __future__ import annotations

import math
from typing import Any

# Floor d'emission : un symbole inconnu dans B[etat] ne fait pas diverger le
# log (log(0) = -inf), il plafonne simplement l'apport de l'observation.
EPS = 1e-9


class HmmInputError(ValueError):
    """Entrree hors contrat : le service repond ``status: invalid``."""


def _log(p: float) -> float:
    """log() avec floor : log(max(p, EPS))."""
    return math.log(max(p, EPS))


def _logsumexp(values: list[float]) -> float:
    """somme en espace des log : log(sum(exp(v))) stable (max + somme)."""
    m = max(values)
    return m + math.log(sum(math.exp(v - m) for v in values))


def _check_model(
    states: list[str],
    pi: list[float],
    A: list[list[float]],
    B: dict[str, dict[str, float]],
) -> None:
    """Valide la forme du modele ; leve ``HmmInputError`` sinon."""
    if not isinstance(states, list) or not states:
        raise HmmInputError("states: liste de noms d'etats non vide requise")
    if len(set(states)) != len(states):
        raise HmmInputError("states: noms en double")
    n = len(states)

    if not isinstance(pi, list) or len(pi) != n:
        raise HmmInputError(f"pi: liste de {n} probabilites attendue")
    if any(not isinstance(p, (int, float)) or isinstance(p, bool) or p < 0 for p in pi):
        raise HmmInputError("pi: probabilites reelles >= 0 attendues")
    if abs(sum(pi) - 1.0) > 1e-6:
        raise HmmInputError(f"pi: somme = {sum(pi):.6f} attend ~ 1")

    if not isinstance(A, list) or len(A) != n:
        raise HmmInputError(f"A: matrice {n} x {n} attendue")
    for i, row in enumerate(A):
        if not isinstance(row, list) or len(row) != n:
            raise HmmInputError(f"A[{i}]: {n} colonnes attendues")
        if any(not isinstance(p, (int, float)) or isinstance(p, bool) or p < 0 for p in row):
            raise HmmInputError(f"A[{i}]: probabilites reelles >= 0 attendues")

    if not isinstance(B, dict):
        raise HmmInputError("B: dictionnaire etat -> {symbole: probabilite} attendu")
    for s in states:
        if s not in B:
            raise HmmInputError(f"B: etat '{s}' manquant")
        if not isinstance(B[s], dict):
            raise HmmInputError(f"B['{s}']: dictionnaire symbole -> probabilite attendu")
        for sym, p in B[s].items():
            if not isinstance(p, (int, float)) or isinstance(p, bool) or p < 0:
                raise HmmInputError(f"B['{s}']['{sym}']: probabilite reelle >= 0 attendue")


def viterbi(
    states: list[str],
    pi: list[float],
    A: list[list[float]],
    B: dict[str, dict[str, float]],
    observations: list[str],
) -> tuple[list[str], float]:
    """Decodage de Viterbi en log. Retourne ``(chemin_optimal, log_prob)``.

    ``chemin_optimal`` est la suite d'etats maximisant la probabilite jointe
    (etats + observations) ; ``log_prob`` est le log de cette probabilite.
    """
    n = len(states)
    T = len(observations)
    delta: list[list[float]] = [ [] for _ in range(T) ]
    psi: list[list[int]] = [ [] for _ in range(T) ]

    delta[0] = [_log(pi[i]) + _log(B[states[i]].get(observations[0], 0.0)) for i in range(n)]
    psi[0] = [0] * n

    for t in range(1, T):
        delta[t] = [0.0] * n
        psi[t] = [0] * n
        for j in range(n):
            emit = _log(B[states[j]].get(observations[t], 0.0))
            best_val = -math.inf
            best_i = 0
            for i in range(n):
                val = delta[t - 1][i] + _log(A[i][j])
                if val > best_val:
                    best_val = val
                    best_i = i
            delta[t][j] = best_val + emit
            psi[t][j] = best_i

    best_last = max(range(n), key=lambda i: delta[-1][i])
    best_log_prob = delta[-1][best_last]

    path_idx = [0] * T
    path_idx[-1] = best_last
    for t in range(T - 1, 0, -1):
        path_idx[t - 1] = psi[t][path_idx[t]]
    return [states[i] for i in path_idx], best_log_prob


def forward_log(
    states: list[str],
    pi: list[float],
    A: list[list[float]],
    B: dict[str, dict[str, float]],
    observations: list[str],
) -> float:
    """Algorithme de l'avant : ``log P(observations | modele)`` (somme, pas max)."""
    n = len(states)
    T = len(observations)
    alpha = [_log(pi[i]) + _log(B[states[i]].get(observations[0], 0.0)) for i in range(n)]
    for t in range(1, T):
        new_alpha = [0.0] * n
        for j in range(n):
            acc = _logsumexp([alpha[i] + _log(A[i][j]) for i in range(n)])
            new_alpha[j] = acc + _log(B[states[j]].get(observations[t], 0.0))
        alpha = new_alpha
    return _logsumexp(alpha)


def run(payload: Any) -> dict[str, Any]:
    """Point d'entree du service : valide le corps, decode, repond au contrat.

    Ne leve jamais d'exception : tout echec de validation devient
    ``{"status": "invalid", "error": ...}``.
    """
    if not isinstance(payload, dict):
        return {"status": "invalid", "error": "corps JSON objet attendu"}

    try:
        states = payload.get("states")
        observations = payload.get("observations")
        pi = payload.get("pi")
        A = payload.get("A")
        B = payload.get("B")

        if not isinstance(observations, list) or not observations:
            return {"status": "invalid", "error": "observations: liste non vide requise"}

        _check_model(states, pi, A, B)
        best_path, best_log_prob = viterbi(states, pi, A, B, observations)
        obs_log_prob = forward_log(states, pi, A, B, observations)
    except HmmInputError as exc:
        return {"status": "invalid", "error": str(exc)}
    except (TypeError, ValueError, KeyError, IndexError) as exc:
        return {"status": "invalid", "error": f"modele incohherent: {exc}"}

    return {
        "status": "ok",
        "best_path": best_path,
        "best_path_log_prob": best_log_prob,
        "observation_log_prob": obs_log_prob,
        "n_states": len(states),
        "n_observations": len(observations),
    }
