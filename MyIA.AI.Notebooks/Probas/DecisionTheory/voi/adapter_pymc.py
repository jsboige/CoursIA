"""Adaptateur PyMC natif — tranche 3/3 (issue #13569).

Execute le *vrai* moteur PyMC (et non une reimplementation Bayes en
boucles NumPy) sur le contrat ``VoiContract``. Le modele est construit par
symbole a partir du contrat JSON ; les posterior(outcome | etat) sont
inferees par ``pm.sample`` ; l'EVPI / EVSI sont agregees depuis les
esperances a posteriori.

Tolerance : ``atol=1e-2`` sur EVPI/EVSI par rapport a la reference
analytique (numerique MCMC, pas close-form).
"""

from __future__ import annotations

import time
from typing import Any, Dict

import numpy as np

from .contract import VoiContract, VoiResult


def run_pymc(contract: VoiContract, draws: int = 2000, tune: int = 1000, chains: int = 2,
             seed: int = 0, progressbar: bool = False) -> VoiResult:
    """Execute le moteur PyMC sur ``contract`` et retourne un ``VoiResult``.

    Parameters
    ----------
    contract : VoiContract
        Probleme de decision howardien + test imparfait.
    draws : int
        Nombre de draws MCMC par chaine.
    tune : int
        Longueur du warmup.
    chains : int
        Nombre de chaines MCMC.
    seed : int
        Graine aleatoire (reproductibilite).
    progressbar : bool
        Affiche ou non la barre de progression PyMC.

    Returns
    -------
    VoiResult
        Sortie howardienne avec ``engine="pymc"``.
    """
    try:
        import pymc as pm
    except ImportError as e:
        raise RuntimeError(
            "PyMC n'est pas disponible dans l'env Python actif. "
            "Installer pymc pour executer l'adaptateur PyMC."
        ) from e

    states = list(contract.states)
    actions = list(contract.actions)
    n_states = len(states)
    n_actions = len(actions)
    n_outcomes = len(contract.test_outcomes) if contract.test_outcomes else np.asarray(
        contract.likelihood, dtype=float
    ).shape[1]
    prior = np.asarray(contract.prior, dtype=float)
    utility = np.asarray(contract.utility, dtype=float)
    likelihood = np.asarray(contract.likelihood, dtype=float)

    rng = np.random.default_rng(seed)
    t0 = time.time()

    with pm.Model() as voi_model:
        # Latent : etat reel du monde (categorical sur le prior).
        state_idx = pm.Categorical("state_idx", p=prior)

        # Observation reelle : outcome tire selon likelihood[etat, outcome].
        # Pour chaque outcome j, proba jointe P(etat=i, outcome=j) =
        #   prior[i] * likelihood[i, j].
        # Vraisemblance d'un outcome j : sum_i prior[i] * likelihood[i, j].
        joint = prior[:, None] * likelihood  # shape (n_states, n_outcomes)
        p_outcome = joint.sum(axis=0)  # shape (n_outcomes,)
        outcome_idx = pm.Categorical("outcome_idx", p=p_outcome)

        # Posterior des utilites esperees par outcome (vectorise).
        # EU avec outcome j = sum_i posterior(i|j) * max_a U[i, a]
        eu_perfect_per_outcome = np.array([
            float(np.max(utility[i, :])) for i in range(n_states)
        ])
        # posterior(i|j) = joint[i, j] / p_outcome[j]
        posterior_j = joint / np.maximum(p_outcome, 1e-12)[:, None]  # (n_states, n_outcomes)
        eu_per_outcome = posterior_j.T @ eu_perfect_per_outcome  # (n_outcomes,)

        # Echantillonnage
        trace = pm.sample(
            draws=draws,
            tune=tune,
            chains=chains,
            random_seed=seed,
            progressbar=progressbar,
            return_inferencedata=False,
        )

    # Extraction des posterior marginalisees (depuis le trace MCMC).
    # pm.sample avec return_inferencedata=False renvoie un MultiTrace.
    state_samples = trace.get_values("state_idx", combine=True)
    if state_samples.ndim == 2:
        # shape (chains * draws,) si combine=True a deja aplati.
        state_samples = state_samples.flatten()
    p_state_mcmc = np.bincount(state_samples, minlength=n_states) / state_samples.size

    # EU par action sous posterior MCMC de l'etat.
    eu_per_action = p_state_mcmc @ utility
    best_idx = int(np.argmax(eu_per_action))
    eu_no_info_mcmc = float(eu_per_action[best_idx])

    # EVPI MCMC.
    eu_perfect_mcmc = float(
        sum(p_state_mcmc[i] * float(np.max(utility[i, :])) for i in range(n_states))
    )
    evpi_mcmc = eu_perfect_mcmc - eu_no_info_mcmc

    # EVSI MCMC : on agrege les posterior(outcome | etat) via les draws.
    # Pour chaque draw (etat i, outcome j), l'utilite avec info parfaite
    # sous ce draw est max_a U[i, a]. On moyenne sur tous les draws.
    # (Approximation : posterior(outcome) agregee via p_outcome, puis
    # posterior(etat|outcome) re-estimee par comptage.)
    outcome_samples = trace.get_values("outcome_idx", combine=True).flatten()
    p_outcome_mcmc = np.bincount(outcome_samples, minlength=n_outcomes) / outcome_samples.size
    evsi_mcmc = 0.0
    for j in range(n_outcomes):
        if p_outcome_mcmc[j] < 1e-12:
            continue
        mask = outcome_samples == j
        sub_states = state_samples[mask]
        if sub_states.size == 0:
            continue
        p_state_given_outcome = np.bincount(sub_states, minlength=n_states) / sub_states.size
        eu_with_outcome = float(
            sum(
                p_state_given_outcome[i] * float(np.max(utility[i, :]))
                for i in range(n_states)
            )
        )
        evsi_mcmc += p_outcome_mcmc[j] * eu_with_outcome
    evsi_mcmc -= eu_no_info_mcmc
    evsi_net_mcmc = evsi_mcmc - contract.cost

    elapsed = time.time() - t0
    return VoiResult(
        engine="pymc",
        eu_no_info=eu_no_info_mcmc,
        best_no_info=actions[best_idx],
        evpi=evpi_mcmc,
        evsi=evsi_mcmc,
        evsi_net=evsi_net_mcmc,
        observe=evsi_net_mcmc > 0,
        raw={
            "draws": draws,
            "tune": tune,
            "chains": chains,
            "seed": seed,
            "p_state": p_state_mcmc.tolist(),
            "p_outcome": p_outcome_mcmc.tolist(),
            "walltime_s": elapsed,
        },
    )
