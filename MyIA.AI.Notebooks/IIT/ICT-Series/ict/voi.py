"""Valeur de l'information pour l'animat ICT — interface canonique EVPI/EVSI.

Outille le notebook **ICT-12e** (Epic #4588, Jambe C2 — parente d'ICT-12c/12d
sur la cognition incarnee). La *valeur de l'information* est une mesure
howardienne classique (Howard, 1966) : combien l'agent est pret a payer pour
observer avant d'agir.

**Trois exemplaires natifs dans le depot** (acceptance #13569) :

| Notebook                                       | Moteur    | Calcul                |
|------------------------------------------------|-----------|-----------------------|
| ``DecInfer/DecInfer-6-Value-Information.ipynb``| Infer.NET | bayesien deterministe |
| ``PyMC/DecPyMC-5-Value-Information.ipynb``     | PyMC      | bayesien + MCMC       |
| ``PyMC/DecPyMC-11-Valeur-Info-Souscription.ipynb`` | PyMC   | bayesien applique     |

Ce module degage **l'interface canonique** que ICT appelle pour les deux
moteurs : ``prior + utility_matrix`` en entree, ``EVPI`` / ``EVSI`` / ``EV_net``
en sortie. Les implementations natives (DecInfer-6, DecPyMC-5) restent
*appelees*, pas recopiees — la greffe #13569.

Principe directeur : **la valeur n'est pas declaree, elle est mesuree**.
Chaque fonction renvoie un flottant ; aucun raccourci bayesien n'est pris
en charge. Les tolerances sont explicites dans la docstring de chaque test.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional, Sequence, Tuple

import numpy as np

ArrayLike = Sequence[float]


@dataclass(frozen=True)
class DecisionProblem:
    """Probleme de decision statique : etats x actions, avec utilite et prior.

    Attributes
    ----------
    states : tuple of str
        Noms des etats possibles du monde (longueur n_states).
    prior : np.ndarray
        Distribution a priori sur les etats, shape ``(n_states,)``.
    actions : tuple of str
        Noms des actions disponibles (longueur n_actions).
    utility : np.ndarray
        Matrice d'utilite ``U[etat, action]``, shape ``(n_states, n_actions)``.
    """

    states: Tuple[str, ...]
    prior: np.ndarray
    actions: Tuple[str, ...]
    utility: np.ndarray

    def __post_init__(self) -> None:
        prior = np.asarray(self.prior, dtype=float)
        utility = np.asarray(self.utility, dtype=float)
        if prior.ndim != 1:
            raise ValueError(f"prior doit etre 1D, recu shape {prior.shape}")
        if utility.ndim != 2:
            raise ValueError(f"utility doit etre 2D, recu shape {utility.shape}")
        if prior.shape[0] != len(self.states):
            raise ValueError(
                f"prior.shape[0]={prior.shape[0]} != len(states)={len(self.states)}"
            )
        if utility.shape != (len(self.states), len(self.actions)):
            raise ValueError(
                f"utility.shape={utility.shape} incompatible avec "
                f"(n_states={len(self.states)}, n_actions={len(self.actions)})"
            )
        if np.any(prior < 0):
            raise ValueError("prior doit etre >= 0 partout")
        s = float(prior.sum())
        if not np.isclose(s, 1.0, atol=1e-9):
            raise ValueError(f"prior doit sommer a 1, recu {s}")
        object.__setattr__(self, "prior", prior)
        object.__setattr__(self, "utility", utility)
        object.__setattr__(self, "states", tuple(self.states))
        object.__setattr__(self, "actions", tuple(self.actions))


def expected_utility_per_action(problem: DecisionProblem) -> np.ndarray:
    """EU de chaque action sous le prior : ``EU[a] = sum_e prior[e] * U[e, a]``.

    Parameters
    ----------
    problem : DecisionProblem
        Le probleme de decision.

    Returns
    -------
    np.ndarray
        Vecteur ``(n_actions,)`` des espérances d'utilite par action.
    """
    return problem.prior @ problem.utility


def optimal_action_without_info(problem: DecisionProblem) -> Tuple[float, str]:
    """Meilleure action sans observation supplementaire.

    Parameters
    ----------
    problem : DecisionProblem
        Le probleme de decision.

    Returns
    -------
    tuple of (float, str)
        ``(EU_max, nom_action)`` de la politique constante optimale.
    """
    eu_per_action = expected_utility_per_action(problem)
    best_idx = int(np.argmax(eu_per_action))
    return float(eu_per_action[best_idx]), problem.actions[best_idx]


def evpi(problem: DecisionProblem) -> float:
    """EVPI : *expected value of perfect information*.

    C'est le **plafond** theorique de la valeur d'une observation : ce qu'un
    oracle parfait rapporterait. Calculable en closed-form par Bayes.

    .. math::

        \\mathrm{EVPI} = \\sum_e p(e) \\max_a U(e, a) - \\max_a \\sum_e p(e) U(e, a)

    Parameters
    ----------
    problem : DecisionProblem
        Le probleme de decision.

    Returns
    -------
    float
        EVPI >= 0 par construction. EVPI = 0 ssi la politique constante est
        deja optimale sur tous les etats (l'info ne peut rien changer).
    """
    eu_per_action = expected_utility_per_action(problem)
    eu_const = float(np.max(eu_per_action))
    eu_perfect = float(
        sum(
            problem.prior[i] * float(np.max(problem.utility[i, :]))
            for i in range(len(problem.states))
        )
    )
    return eu_perfect - eu_const


def evsi(
    problem: DecisionProblem,
    likelihood: np.ndarray,
    test_outcomes: Optional[Tuple[str, ...]] = None,
) -> float:
    """EVSI : valeur d'un test imparfait decrit par sa matrice de vraisemblance.

    Parameters
    ----------
    problem : DecisionProblem
        Le probleme de decision.
    likelihood : np.ndarray
        Matrice ``L[etat, outcome] = P(outcome | etat)``,
        shape ``(n_states, n_outcomes)``.
    test_outcomes : tuple of str, optional
        Noms des resultats possibles du test ; metadata informative uniquement.

    Returns
    -------
    float
        EVSI >= 0 par construction. EVSI <= EVPI toujours (l'imparfait ne
        peut pas exceder le parfait).

    Notes
    -----
    Convention numerique : si un outcome est de vraisemblance marginale
    ``P(outcome) < 1e-12``, on le neglige (evite division par zero sur le
    posterior de Bayes).
    """
    L = np.asarray(likelihood, dtype=float)
    if L.shape != (len(problem.states), L.shape[1]):
        raise ValueError(
            f"likelihood.shape[0]={L.shape[0]} doit valoir "
            f"len(states)={len(problem.states)}"
        )
    if np.any(L < 0):
        raise ValueError("likelihood doit etre >= 0 partout")
    if L.shape[1] < 1:
        raise ValueError("likelihood doit avoir au moins 1 colonne (outcome)")
    eu_sans, _ = optimal_action_without_info(problem)
    n_outcomes = L.shape[1]
    eu_avec = 0.0
    for j in range(n_outcomes):
        # P(outcome=j) par loi des probabilites totales
        p_outcome_j = float(
            sum(problem.prior[i] * L[i, j] for i in range(len(problem.states)))
        )
        if p_outcome_j < 1e-12:
            continue
        # Posterior de Bayes : P(etat=i | outcome=j) ∝ prior[i] * L[i, j]
        posterior = np.array(
            [problem.prior[i] * L[i, j] / p_outcome_j for i in range(len(problem.states))]
        )
        eu_per_action_posterior = posterior @ problem.utility
        eu_avec += p_outcome_j * float(np.max(eu_per_action_posterior))
    return eu_avec - eu_sans


def evsi_net(problem: DecisionProblem, likelihood: np.ndarray, cost: float) -> float:
    """EVSI net : EVSI moins le cout d'observation.

    L'animat observe ssi ``evsi_net > 0``.

    Parameters
    ----------
    problem : DecisionProblem
        Le probleme de decision.
    likelihood : np.ndarray
        Matrice de vraisemblance ``(n_states, n_outcomes)``.
    cost : float
        Cout fixe de l'observation (>= 0).

    Returns
    -------
    float
        EVSI_net. Positif = observation rentable.
    """
    if cost < 0:
        raise ValueError(f"cout doit etre >= 0, recu {cost}")
    return evsi(problem, likelihood) - cost


def observation_is_worthwhile(
    problem: DecisionProblem,
    likelihood: np.ndarray,
    cost: float,
) -> bool:
    """Politique d'observation de l'animat : observe-t-il ?

    .. math::

        \\mathrm{observe} \\Leftrightarrow \\mathrm{EVSI}(L) > \\mathrm{cout}

    Parameters
    ----------
    problem : DecisionProblem
        Le probleme de decision.
    likelihood : np.ndarray
        Matrice de vraisemblance ``(n_states, n_outcomes)``.
    cost : float
        Cout fixe de l'observation.

    Returns
    -------
    bool
        ``True`` si l'observation est rentable.
    """
    return evsi_net(problem, likelihood, cost) > 0


def animat_decision_summary(
    problem: DecisionProblem,
    likelihood: np.ndarray,
    cost: float,
) -> dict:
    """Résumé de la decision de l'animat — interface d'appel principale.

    C'est l'entrée canonique que le notebook ICT-12e consomme : un seul
    appel, toutes les grandeurs howardiennes + la politique recommandee.

    Parameters
    ----------
    problem : DecisionProblem
        Le probleme de decision.
    likelihood : np.ndarray
        Matrice de vraisemblance ``(n_states, n_outcomes)``.
    cost : float
        Cout fixe de l'observation.

    Returns
    -------
    dict
        Dictionnaire avec les cles ``eu_no_info``, ``best_no_info``,
        ``evpi``, ``evsi``, ``evsi_net``, ``observe``.
    """
    eu_no, best_no = optimal_action_without_info(problem)
    e = evpi(problem)
    s = evsi(problem, likelihood)
    sn = s - cost
    return {
        "eu_no_info": eu_no,
        "best_no_info": best_no,
        "evpi": e,
        "evsi": s,
        "evsi_net": sn,
        "observe": sn > 0,
    }
