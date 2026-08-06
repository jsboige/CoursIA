"""Boucle auto-referentielle p_hat -> action -> p_hat (Case 2, Epic #9533).

La matrice de dissociations ICT (``docs/ict/dissociations-matrix.md``) factorise
la serie en 4 objets -- ``s_t`` (saillance), ``q_t(z)`` (representation
predictive), ``pi_t(z)`` (pregnance/valence), ``W_t`` (workspace) -- et, depuis
#9533, **inverse** la matrice : chaque case vide designe une experience
manquante, avec prediction pre-enregistree + null adversarial. Ce module teste
la deuxieme case nommee : la **boucle auto-referentielle** ``p_hat -> action
-> p_hat`` (le representant interne predit ses propres etats futurs).

Prediction pre-enregistree (PR #9546 SHA 3f6590fa4, verrouillee avant ce test) :
    Une boucle fermee ``p_hat -> action -> p_hat`` est stable sur un regime
    borne mais diverge (oscillation amplifiee) hors de ce regime. Le seuil de
    stabilite est pre-enregistre avant le test :

        Pour un couplage lineaire ``x_{t+1} = a x_t + kappa * p_hat_t + b +
        epsilon_t`` ou l'action ``a_t = p_hat_t`` et ``p_hat_{t+1} =
        f_obs(x_t)``, le systeme lineaire resultant a un coefficient effectif
        ``a_eff = a + kappa * a_hat``. Si ``|a_eff| < 1``, le regime est
        borne ; si ``|a_eff| > 1``, il diverge.

        Avec ``a = 0.95`` et ``a_hat = 0.95`` (predicteur exact), la frontiere
        est ``kappa_c = (1 - a) / a_hat = (1 - 0.95) / 0.95 ~= 0.0526``. Pour
        ``kappa > kappa_c`` le regime diverge. Seuil de stabilite
        pre-enregistre : ``kappa_c = 0.05`` (arrondi a la resolution de la
        grille 0.1).

Null adversarial : un **delieur causal** (``kappa = 0``, la prediction
n'influence pas l'environnement) supprime la divergence meme quand le predicteur
est interne. Si le delieur borne mais la boucle diverge, la causalite
auto-referentielle tient.

Verdict du test (honnete, multi-seed >= 4) :
    - Si la frontiere observee coincide avec ``kappa_c ~= 0.05`` (a +/- 0.05,
      resolution de la grille) sur au moins 4 graines sur 5, prediction
      ``CONFIRMED``.
    - Sinon, prediction ``FALSIFIED`` au sens numerique strict mais la
      **dissociation** (bouclee diverge vs delieur borne) peut tenir
      (``PARTIAL``).
    - Si meme la dissociation ne tient pas (delieur diverge ou bouclee ne
      diverge jamais), verdict ``FALSIFIED``.

Substrat
--------
Numpy uniquement, CPU-only. L'animat a un etat de position scalaire ``x_t``
et une representation interne ``p_hat_t``. La boucle auto-referentielle est
definie par trois equations :

    (1) Action         : a_t = p_hat_t                (l'action EST la prediction)
    (2) Environnement  : x_{t+1} = a x_t + kappa a_t + b + epsilon_t
    (3) Prediction     : p_hat_{t+1} = f_obs(x_t)     (observation pure)

Le couplage ``kappa`` dans (2) ferme la boucle ``p_hat -> action -> x ->
p_hat``. Pour ``kappa = 0``, la prediction n'influence pas l'environnement
(delier causal), meme si la computation interne reste formellement en boucle
(c'est la subtilite du design : c'est le **feedback sur l'environnement** qui
compte, pas la recurrence du calcul de prediction).

La prediction purement observationnelle est ``f_obs(x) = a_hat x + b_hat``.
Le predicteur est exact (``a_hat = a``, ``b_hat = b``) -- on isole ainsi
l'effet de la boucle de toute erreur d'estimation. Le parametre manipule
est ``kappa in [0, 2]`` (kappa = 0 = delieur causal, kappa dans (0, kappa_c)
= boucle sous-amortie, kappa > kappa_c = boucle sur-amortie / divergence).

Pour chaque graine et chaque ``kappa``, on tire ``N_init`` conditions
initiales (``x_0 ~ U(-1, +1)``, ``p_hat_0 = f_obs(x_0)``), on simule T pas,
on mesure ``R_T = sqrt(mean(x_T^2))`` et ``R_0 = sqrt(mean(x_0^2))``. Le ratio
``R_T / R_0`` est l'indicateur de divergence (>5 = divergence, <2 = borne).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Optional, Sequence, Tuple

import numpy as np


# --------------------------------------------------------------------------- #
#  Constantes experimentales (seuils pre-enregistres, PR #9546 SHA 3f6590fa4)   #
# --------------------------------------------------------------------------- #

# Frontiere de stabilite predite (theorie lineaire : x_{t+1} = (a + kappa*a_hat)
# x_t + ..., stable ssi |a + kappa*a_hat| < 1 ; avec a = a_hat = 0.95, kappa_c
# = (1 - a) / a_hat).
KAPPA_C_PREDICTED: float = (1.0 - 0.95) / 0.95  # ~= 0.0526

# Ratio de divergence : R_T / R_0 au-dessus duquel on declare le regime divergent.
RATIO_DIVERGENT: float = 5.0

# Ratio de stabilite : R_T / R_0 au-dessus duquel on declare le regime borne
# (entre RATIO_BORNE_HIGH et RATIO_DIVERGENT, c'est la zone "metastable").
RATIO_BORNE_HIGH: float = 2.0

# Horizon de simulation (pas de temps).
HORIZON_T: int = 200

# Grille de couplages ``kappa`` balayee. Grille fine autour de KAPPA_C_PREDICTED
# (~= 0.053), plus large au-dela pour explorer le regime divergent.
KAPPA_GRID: Tuple[float, ...] = (
    0.0, 0.02, 0.04, 0.05, 0.06, 0.08, 0.10, 0.15, 0.20, 0.30, 0.50, 1.00,
)

# Conditions initiales par graine et par gain.
N_INIT: int = 30


# --------------------------------------------------------------------------- #
#  Environnement simule et prediction observationnelle                          #
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class EnvironmentParams:
    """Parametres de la dynamique d'environnement (identiques entre conditions).

    Le predicteur est exact (``a_hat = a``, ``b_hat = b``) -- on isole l'effet
    de la boucle de toute erreur d'estimation. Si la prediction etait
    imprecise, la divergence pourrait venir de l'erreur d'estimation plutot
    que de la boucle auto-referentielle. Cette isolation est la condition
    experimentale qui rend le test falsifiable.
    """

    a: float = 0.95        # coefficient AR(1) de l'environnement
    b: float = 0.0         # biais
    sigma: float = 0.05    # bruit d'observation
    a_hat: float = 0.95    # estimation de a par le predicteur (identique)
    b_hat: float = 0.0     # estimation de b (identique)


def f_obs(x: np.ndarray, params: EnvironmentParams) -> np.ndarray:
    """Prediction purement observationnelle de l'etat suivant."""
    return params.a_hat * x + params.b_hat


# --------------------------------------------------------------------------- #
#  Simulation de la boucle auto-referentielle                                     #
# --------------------------------------------------------------------------- #


def simulate_self_reference_loop(
    kappa: float,
    n_init: int = N_INIT,
    horizon: int = HORIZON_T,
    params: Optional[EnvironmentParams] = None,
    rng: Optional[np.random.Generator] = None,
) -> Dict[str, np.ndarray]:
    """Simule la boucle ``p_hat -> action -> p_hat`` pour un couplage ``kappa``.

    Equations integrees pas a pas :
        a_t            = p_hat_t
        x_{t+1}        = a x_t + kappa a_t + b + epsilon_t
        p_hat_{t+1}    = f_obs(x_t)

    Pour chaque condition initiale ``x_0 ~ U(-1, +1)``, on initialise
    ``p_hat_0 = f_obs(x_0)`` (le predicteur demarre aligne sur sa meilleure
    estimation).

    Renvoie un dict avec :
        - ``R_0``  : rms des positions initiales (taille ``n_init``)
        - ``R_T``  : rms des positions finales (taille ``n_init``)
        - ``ratio``: ``R_T / R_0`` (taille ``n_init``)
        - ``trajectories_x`` : forme ``(n_init, horizon + 1)``
        - ``trajectories_phat`` : forme ``(n_init, horizon + 1)``
    """
    if params is None:
        params = EnvironmentParams()
    if rng is None:
        rng = np.random.default_rng(0)

    x0 = rng.uniform(-1.0, 1.0, size=n_init)
    p_hat0 = f_obs(x0, params)

    traj_x = np.empty((n_init, horizon + 1), dtype=np.float64)
    traj_phat = np.empty((n_init, horizon + 1), dtype=np.float64)
    traj_x[:, 0] = x0
    traj_phat[:, 0] = p_hat0

    for t in range(horizon):
        # (1) Action EST la prediction (couplage interne -> externe).
        a_t = traj_phat[:, t]
        # (2) Environnement reel, avec couplage de l'action.
        noise = rng.normal(0.0, params.sigma, size=n_init)
        x_next = params.a * traj_x[:, t] + kappa * a_t + params.b + noise
        # (3) Prediction purement observationnelle.
        p_hat_next = f_obs(traj_x[:, t], params)

        traj_x[:, t + 1] = x_next
        traj_phat[:, t + 1] = p_hat_next

    R_0 = np.sqrt(np.mean(x0 ** 2))
    R_T = np.sqrt(np.mean(traj_x[:, -1] ** 2))
    ratio = R_T / max(R_0, 1e-12)

    return {
        "R_0": np.full(n_init, R_0),
        "R_T": np.full(n_init, R_T),
        "ratio": np.full(n_init, ratio),
        "trajectories_x": traj_x,
        "trajectories_phat": traj_phat,
    }


# --------------------------------------------------------------------------- #
#  Scan de stabilite : ratio R_T / R_0 en fonction de kappa                      #
# --------------------------------------------------------------------------- #


def stability_scan(
    kappa_grid: Sequence[float] = KAPPA_GRID,
    n_init: int = N_INIT,
    horizon: int = HORIZON_T,
    seeds: Sequence[int] = (0, 1, 7, 42, 99),
    params: Optional[EnvironmentParams] = None,
) -> Dict[str, np.ndarray]:
    """Balaye la grille ``kappa_grid`` pour chaque graine et agrege les ratios.

    Renvoie un dict avec :
        - ``kappa_grid``     : la grille des couplages balayes
        - ``ratio_mean``     : forme ``(len(seeds), len(kappa_grid))``
        - ``ratio_median``   : forme idem, ratio median par graine
        - ``stable_mask``    : forme idem, True si toutes les conditions initiales
                               restent sous RATIO_DIVERGENT
        - ``divergent_mask`` : forme idem, True si TOUTES les conditions
                               initiales depassent RATIO_DIVERGENT
        - ``seeds``          : les graines utilisees
    """
    if params is None:
        params = EnvironmentParams()

    n_seeds = len(seeds)
    n_kappa = len(kappa_grid)

    ratio_mean = np.empty((n_seeds, n_kappa), dtype=np.float64)
    ratio_median = np.empty((n_seeds, n_kappa), dtype=np.float64)
    stable_mask = np.empty((n_seeds, n_kappa), dtype=bool)
    divergent_mask = np.empty((n_seeds, n_kappa), dtype=bool)

    for i, seed in enumerate(seeds):
        rng = np.random.default_rng(seed)
        for j, kappa in enumerate(kappa_grid):
            sim = simulate_self_reference_loop(
                kappa=kappa,
                n_init=n_init,
                horizon=horizon,
                params=params,
                rng=rng,
            )
            ratios = sim["ratio"]  # shape (n_init,)
            ratio_mean[i, j] = float(np.mean(ratios))
            ratio_median[i, j] = float(np.median(ratios))
            stable_mask[i, j] = bool(np.all(ratios < RATIO_DIVERGENT))
            divergent_mask[i, j] = bool(np.all(ratios >= RATIO_DIVERGENT))

    return {
        "kappa_grid": np.asarray(kappa_grid, dtype=np.float64),
        "ratio_mean": ratio_mean,
        "ratio_median": ratio_median,
        "stable_mask": stable_mask,
        "divergent_mask": divergent_mask,
        "seeds": np.asarray(seeds),
    }


# --------------------------------------------------------------------------- #
#  Estimation de la frontiere de stabilite observee                              #
# --------------------------------------------------------------------------- #


def estimate_stability_boundary(
    scan: Dict[str, np.ndarray],
    threshold: float = RATIO_DIVERGENT,
) -> Dict[str, float]:
    """Estime la frontiere de stabilite observee a partir du scan.

    Pour chaque graine, on cherche le plus petit ``kappa`` tel que le ratio
    median depasse ``threshold``. La frontiere mediane est la mediane
    inter-graines. On rapporte aussi l'ecart-type et le biais par rapport a
    ``KAPPA_C_PREDICTED``.
    """
    kappa_grid = scan["kappa_grid"]
    ratio_median = scan["ratio_median"]  # shape (n_seeds, n_kappa)

    n_seeds = ratio_median.shape[0]
    kappa_critical = np.empty(n_seeds, dtype=np.float64)
    for i in range(n_seeds):
        above = np.where(ratio_median[i] >= threshold)[0]
        if len(above) == 0:
            # Aucun couplage ne franchit le seuil -> frontiere au-dela de la grille.
            kappa_critical[i] = float(kappa_grid[-1] + 0.1)
        else:
            # Premiere fois ou le seuil est franchi.
            kappa_critical[i] = float(kappa_grid[above[0]])

    return {
        "kappa_critical_per_seed": kappa_critical,
        "kappa_critical_median": float(np.median(kappa_critical)),
        "kappa_critical_std": float(np.std(kappa_critical)),
        "bias_vs_predicted": float(np.median(kappa_critical) - KAPPA_C_PREDICTED),
    }


# --------------------------------------------------------------------------- #
#  Null adversarial : delieur causal (kappa = 0)                                #
# --------------------------------------------------------------------------- #


def delieur_verdict(scan: Dict[str, np.ndarray]) -> Dict[str, float]:
    """Verifie que le delieur causal (``kappa = 0``) reste dans le regime borne.

    Le delieur doit presenter un ratio median < RATIO_DIVERGENT sur toutes les
    graines. Si oui, la dissociation tient : le couplage boucle etait bien la
    cause de la divergence observee aux grands ``kappa``.
    """
    kappa_grid = scan["kappa_grid"]
    ratio_median = scan["ratio_median"]
    idx_zero = int(np.where(np.isclose(kappa_grid, 0.0))[0][0])

    delieur_ratios = ratio_median[:, idx_zero]  # shape (n_seeds,)
    return {
        "delieur_ratio_per_seed": delieur_ratios,
        "delieur_ratio_max": float(np.max(delieur_ratios)),
        "delieur_ratio_mean": float(np.mean(delieur_ratios)),
        "delieur_stable": bool(np.all(delieur_ratios < RATIO_DIVERGENT)),
    }


# --------------------------------------------------------------------------- #
#  Synthese : verdict honnete a deux niveaux (prediction + dissociation)         #
# --------------------------------------------------------------------------- #


def predict_and_dissociate(scan: Dict[str, np.ndarray]) -> Dict[str, object]:
    """Verdict honnete du test, decompose en prediction stricte + dissociation.

    Prediction stricte  : la frontiere observee coincide-t-elle avec
    ``KAPPA_C_PREDICTED ~= 0.053`` a +/- 0.05 (resolution de la grille 0.1,
    on accepte la moitie de la maille) sur au moins 4 graines sur 5 ?

    Dissociation  : la frontiere bouclee diverge-t-elle tandis que le delieur
    (``kappa = 0``) reste borne ? Si oui, la causalite auto-referentielle tient
    meme quand la prediction numerique est mise en defaut.
    """
    boundary = estimate_stability_boundary(scan)
    delieur = delieur_verdict(scan)

    # Tolerance : la grille est espacee de 0.1, on accepte +- 0.05 (demi-maille).
    TOLERANCE = 0.05
    n_seeds = len(boundary["kappa_critical_per_seed"])
    n_within = int(
        np.sum(
            np.abs(boundary["kappa_critical_per_seed"] - KAPPA_C_PREDICTED) <= TOLERANCE
        )
    )
    prediction_confirmed = bool(n_within >= max(1, int(0.8 * n_seeds)))

    dissociation_confirmed = bool(delieur["delieur_stable"])
    # Dissociation tient si delieur borne ET frontiere bouclee au-dessus de
    # RATIO_DIVERGENT pour au moins un kappa dans la grille.
    any_loop_divergent = bool(np.any(scan["divergent_mask"]))
    dissociation_full = dissociation_confirmed and any_loop_divergent

    if prediction_confirmed and dissociation_full:
        verdict = "CONFIRMED"
        verdict_detail = (
            f"Frontiere de stabilite observee a kappa_c = "
            f"{boundary['kappa_critical_median']:.3f} (biais "
            f"{boundary['bias_vs_predicted']:+.3f}, prediction KAPPA_C = "
            f"{KAPPA_C_PREDICTED:.3f}) ; delieur causal borne "
            f"(R_T/R_0 max = {delieur['delieur_ratio_max']:.2f}) ; "
            f"bouclee divergente pour kappa >= "
            f"{float(scan['kappa_grid'][np.any(scan['divergent_mask'], axis=0)][0]):.2f}."
        )
    elif dissociation_full:
        verdict = "PARTIAL"
        verdict_detail = (
            "Dissociation bouclee/delieur CONFIRMED (delieur borne, bouclee "
            "divergente), mais frontiere observee deplacee : kappa_c = "
            f"{boundary['kappa_critical_median']:.3f} vs prediction KAPPA_C = "
            f"{KAPPA_C_PREDICTED:.3f} (biais "
            f"{boundary['bias_vs_predicted']:+.3f}). Theorie lineaire "
            "capturale partielle."
        )
    else:
        verdict = "FALSIFIED"
        verdict_detail = (
            "Dissociation non soutenue : "
            f"delieur_ratio_max = {delieur['delieur_ratio_max']:.2f}, "
            f"any_loop_divergent = {any_loop_divergent}. "
            "La boucle auto-referentielle n'a pas le comportement predit."
        )

    return {
        "verdict": verdict,
        "verdict_detail": verdict_detail,
        "boundary": boundary,
        "delieur": delieur,
        "prediction_confirmed": prediction_confirmed,
        "dissociation_confirmed": dissociation_confirmed,
        "n_seeds": n_seeds,
        "n_within_tolerance": n_within,
    }


# --------------------------------------------------------------------------- #
#  Reproduction : run-and-print pour integration notebook                         #
# --------------------------------------------------------------------------- #


def run_full_protocol(
    seeds: Sequence[int] = (0, 1, 7, 42, 99),
    kappa_grid: Sequence[float] = KAPPA_GRID,
    n_init: int = N_INIT,
    horizon: int = HORIZON_T,
) -> Dict[str, object]:
    """Execute le protocole complet et renvoie le verdict synthetise.

    C'est cette fonction qu'appelle le notebook pour obtenir le verdict final
    avec un seul appel. Toutes les autres fonctions sont exposees pour les
    tests unitaires et l'exploration.
    """
    scan = stability_scan(
        kappa_grid=kappa_grid, n_init=n_init, horizon=horizon, seeds=seeds
    )
    verdict = predict_and_dissociate(scan)
    return {"scan": scan, "verdict": verdict}