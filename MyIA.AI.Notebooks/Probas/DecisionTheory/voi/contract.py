"""Contrat JSON commun EVPI/EVSI — tranche 3/3 (issue #13569).

Le contrat ``VoiContract`` est la representation portable d'un probleme de
decision howardien : etats, prior, actions, utilite, vraisemblance du test,
cout de l'observation. La sortie ``VoiResult`` aligne sur la signature
``ict.voi.animat_decision_summary`` de la tranche 1/3 (PR #13652).
"""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any, Dict, List, Tuple

import numpy as np


@dataclass(frozen=True)
class VoiContract:
    """Probleme de decision howardien + test imparfait + cout d'observation.

    Attributes
    ----------
    states : tuple of str
        Noms des etats du monde.
    prior : list of float
        Distribution a priori ``(n_states,)``.
    actions : tuple of str
        Noms des actions disponibles.
    utility : list of list of float
        Matrice d'utilite ``U[etat, action]``, ``(n_states, n_actions)``.
    likelihood : list of list of float
        ``L[etat, outcome] = P(outcome | etat)``, ``(n_states, n_outcomes)``.
    test_outcomes : tuple of str
        Noms des resultats possibles du test.
    cost : float
        Cout fixe d'observation, strictement >= 0.

    Examples
    --------
    Parapluie/soleil (DecPyMC-5)::

        VoiContract(
            states=("pluie", "soleil"),
            prior=(0.3, 0.7),
            actions=("parapluie", "pas_parapluie"),
            utility=[[0.0, -50.0], [-5.0, 0.0]],
            likelihood=[[0.8, 0.2], [0.1, 0.9]],
            test_outcomes=("annonce_pluie", "annonce_soleil"),
            cost=1.0,
        )
    """

    states: Tuple[str, ...]
    prior: Tuple[float, ...]
    actions: Tuple[str, ...]
    utility: Tuple[Tuple[float, ...], ...]
    likelihood: Tuple[Tuple[float, ...], ...]
    test_outcomes: Tuple[str, ...] = field(default_factory=tuple)
    cost: float = 0.0

    def __post_init__(self) -> None:
        if len(self.states) < 2:
            raise ValueError(f"states doit avoir >= 2 elements, recu {self.states}")
        if len(self.actions) < 1:
            raise ValueError(f"actions doit avoir >= 1 element, recu {self.actions}")
        if len(self.prior) != len(self.states):
            raise ValueError(
                f"len(prior)={len(self.prior)} != len(states)={len(self.states)}"
            )
        if self.cost < 0:
            raise ValueError(f"cost doit etre >= 0, recu {self.cost}")
        prior_arr = np.asarray(self.prior, dtype=float)
        if np.any(prior_arr < 0):
            raise ValueError("prior doit etre >= 0 partout")
        if not np.isclose(prior_arr.sum(), 1.0, atol=1e-9):
            raise ValueError(f"prior doit sommer a 1, recu {prior_arr.sum()}")
        utility_arr = np.asarray(self.utility, dtype=float)
        if utility_arr.shape != (len(self.states), len(self.actions)):
            raise ValueError(
                f"utility.shape={utility_arr.shape} incompatible avec "
                f"(n_states={len(self.states)}, n_actions={len(self.actions)})"
            )
        likelihood_arr = np.asarray(self.likelihood, dtype=float)
        if likelihood_arr.ndim != 2:
            raise ValueError(
                f"likelihood doit etre 2D, recu ndim={likelihood_arr.ndim}"
            )
        if likelihood_arr.shape[0] != len(self.states):
            raise ValueError(
                f"likelihood.shape[0]={likelihood_arr.shape[0]} != "
                f"len(states)={len(self.states)}"
            )
        if likelihood_arr.shape[1] < 1:
            raise ValueError(
                f"likelihood doit avoir au moins 1 outcome, recu "
                f"shape={likelihood_arr.shape}"
            )
        # Vraisemblance : chaque ligne doit sommer a 1.
        row_sums = likelihood_arr.sum(axis=1)
        if not np.allclose(row_sums, 1.0, atol=1e-9):
            raise ValueError(
                f"chaque ligne de likelihood doit sommer a 1, "
                f"recu row_sums={row_sums.tolist()}"
            )
        if np.any(likelihood_arr < 0):
            raise ValueError("likelihood doit etre >= 0 partout")

    def to_dict(self) -> Dict[str, Any]:
        """Serialisation JSON-compatible (list, pas ndarray)."""
        return {
            "states": list(self.states),
            "prior": list(self.prior),
            "actions": list(self.actions),
            "utility": [list(row) for row in self.utility],
            "likelihood": [list(row) for row in self.likelihood],
            "test_outcomes": list(self.test_outcomes),
            "cost": self.cost,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> "VoiContract":
        """Construction depuis un dict JSON-deserialise."""
        return cls(
            states=tuple(d["states"]),
            prior=tuple(float(x) for x in d["prior"]),
            actions=tuple(d["actions"]),
            utility=tuple(tuple(float(x) for x in row) for row in d["utility"]),
            likelihood=tuple(
                tuple(float(x) for x in row) for row in d["likelihood"]
            ),
            test_outcomes=tuple(d.get("test_outcomes", ())),
            cost=float(d.get("cost", 0.0)),
        )


@dataclass(frozen=True)
class VoiResult:
    """Sortie howardienne alignee sur ``ict.voi.animat_decision_summary``.

    Attributes
    ----------
    engine : str
        Nom du moteur (``"pymc"`` ou ``"infernet"``).
    eu_no_info : float
        Utilite esperee de la meilleure action constante (sans observation).
    best_no_info : str
        Nom de cette action.
    evpi : float
        Valeur de l'information parfaite.
    evsi : float
        Valeur de l'observation (avant cout).
    evsi_net : float
        Valeur nette de l'observation (``evsi - cost``).
    observe : bool
        ``True`` si l'observation est recommandee (``evsi_net > 0``).
    raw : dict
        Metadonnees moteur-specifiques (samples, walltime, etc.).
    """

    engine: str
    eu_no_info: float
    best_no_info: str
    evpi: float
    evsi: float
    evsi_net: float
    observe: bool
    raw: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


def animat_decision_summary_contract(
    contract: VoiContract,
) -> VoiResult:
    """Spec executable du contrat : evaluation analytique NumPy.

    Sert de **reference analytique close-form** : la sortie de tout adaptateur
    cross-engine doit s'en approcher a tolerance pres. Cette routine ne
    touche ni a PyMC ni a Infer.NET ; c'est l'implementation de reference
    qui definit le contrat.

    Parameters
    ----------
    contract : VoiContract
        Probleme de decision a evaluer.

    Returns
    -------
    VoiResult
        Sortie howardienne. ``engine="analytical"``.
    """
    prior = np.asarray(contract.prior, dtype=float)
    utility = np.asarray(contract.utility, dtype=float)
    likelihood = np.asarray(contract.likelihood, dtype=float)

    # EU par action sous le prior.
    eu_per_action = prior @ utility
    best_idx = int(np.argmax(eu_per_action))
    eu_no_info = float(eu_per_action[best_idx])
    best_no_info = contract.actions[best_idx]

    # EVPI : oracle parfait.
    eu_perfect = float(
        sum(prior[i] * float(np.max(utility[i, :])) for i in range(len(contract.states)))
    )
    evpi = eu_perfect - eu_no_info

    # EVSI : test imparfait. Bayes sur les posterior(outcome | etat).
    # P(outcome) = sum_etat prior[etat] * L[etat, outcome]
    p_outcome = prior @ likelihood  # shape (n_outcomes,)
    evsi = 0.0
    for j in range(likelihood.shape[1]):
        if p_outcome[j] < 1e-12:
            continue
        # posterior[etat | outcome] = L[etat, outcome] * prior[etat] / P(outcome)
        posterior = (likelihood[:, j] * prior) / p_outcome[j]
        eu_with_outcome = float(
            sum(posterior[i] * float(np.max(utility[i, :])) for i in range(len(contract.states)))
        )
        evsi += p_outcome[j] * eu_with_outcome
    evsi -= eu_no_info

    evsi_net = evsi - contract.cost
    return VoiResult(
        engine="analytical",
        eu_no_info=eu_no_info,
        best_no_info=best_no_info,
        evpi=evpi,
        evsi=evsi,
        evsi_net=evsi_net,
        observe=evsi_net > 0,
        raw={"method": "closed-form-bayes", "p_outcome": p_outcome.tolist()},
    )
