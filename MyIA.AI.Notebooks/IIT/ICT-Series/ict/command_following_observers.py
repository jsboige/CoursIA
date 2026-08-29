"""Observateurs bayésiens du suivi de commande covert (#8182, Owen/Cruse).

Ce module formalise une portée diagnostique, pas un détecteur de conscience.
L'état latent ``C`` signifie seulement « capable de suivre volontairement la
commande dans le paradigme ». Les données de contrôle de Cruse et al. (2011)
calibrent la sensibilité EEG (9/12 contrôles positifs) et sa spécificité sous
null « écouter sans suivre » (0/12 positifs).

Le protocole et les seuils ont été scellés AVANT implémentation dans
``docs/ict/command-following-observers-pre-enregistrement.md`` au commit
``103fdb23c``. La lecture Schurger (2012) a été séparée : son biais
d'alignement sur franchissement de seuil n'est pas une erreur d'observation
d'un état latent.

Références
----------
Adrian M. Owen et al., Science 313 (2006), 1402,
DOI 10.1126/science.1130197. Lecture firsthand 2026-08-29.
Damian Cruse et al., The Lancet 378 (2011), 2088-2094,
DOI 10.1016/S0140-6736(11)61224-5. Lecture firsthand 2026-08-29.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

import numpy as np

__all__ = [
    "Calibration",
    "predictive_values",
    "sample_observer",
    "evaluate_seed",
    "run_preregistered_study",
]

DEFAULT_SEEDS = (0, 1, 7, 42, 99)
DEFAULT_PREVALENCES = (0.05, 0.10, 0.20, 0.40)


@dataclass(frozen=True)
class Calibration:
    """Paramètres Beta des sensibilité et spécificité d'un observateur."""

    sensitivity_alpha: float
    sensitivity_beta: float
    specificity_alpha: float
    specificity_beta: float

    def __post_init__(self) -> None:
        values = (
            self.sensitivity_alpha,
            self.sensitivity_beta,
            self.specificity_alpha,
            self.specificity_beta,
        )
        if any(value <= 0 for value in values):
            raise ValueError("Les paramètres Beta doivent être strictement positifs")


CRUSE_CALIBRATION = Calibration(10.0, 4.0, 13.0, 1.0)
AUTOMATIC_RESPONSE_STRESS = Calibration(10.0, 4.0, 9.0, 5.0)


def _probability_array(value: float | np.ndarray, name: str) -> np.ndarray:
    array = np.asarray(value, dtype=float)
    if np.any(~np.isfinite(array)) or np.any((array < 0.0) | (array > 1.0)):
        raise ValueError(f"{name} doit être une probabilité finie dans [0, 1]")
    return array


def predictive_values(
    prevalence: float | np.ndarray,
    sensitivity: float | np.ndarray,
    specificity: float | np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    """Retourne ``(PPV, P(C | résultat négatif))``.

    Les trois arguments suivent les règles de diffusion NumPy. Un dénominateur
    nul indique un résultat impossible sous le modèle et produit ``nan`` plutôt
    qu'une certitude fabriquée.
    """

    p = _probability_array(prevalence, "prevalence")
    se = _probability_array(sensitivity, "sensitivity")
    sp = _probability_array(specificity, "specificity")

    positive = p * se + (1.0 - p) * (1.0 - sp)
    negative = p * (1.0 - se) + (1.0 - p) * sp
    ppv = np.divide(
        p * se,
        positive,
        out=np.full(np.broadcast(p, se, sp).shape, np.nan),
        where=positive > 0.0,
    )
    p_capable_given_negative = np.divide(
        p * (1.0 - se),
        negative,
        out=np.full(np.broadcast(p, se, sp).shape, np.nan),
        where=negative > 0.0,
    )
    return ppv, p_capable_given_negative


def sample_observer(
    calibration: Calibration,
    *,
    seed: int,
    n_draws: int = 50_000,
) -> tuple[np.ndarray, np.ndarray]:
    """Tire les postérieurs indépendants de sensibilité et spécificité."""

    if n_draws <= 0:
        raise ValueError("n_draws doit être strictement positif")
    rng = np.random.default_rng(seed)
    sensitivity = rng.beta(
        calibration.sensitivity_alpha,
        calibration.sensitivity_beta,
        size=n_draws,
    )
    specificity = rng.beta(
        calibration.specificity_alpha,
        calibration.specificity_beta,
        size=n_draws,
    )
    return sensitivity, specificity


def _quantiles(values: np.ndarray) -> dict[str, float]:
    q05, q50, q95 = np.quantile(values, (0.05, 0.50, 0.95))
    return {"q05": float(q05), "median": float(q50), "q95": float(q95)}


def evaluate_seed(
    seed: int,
    *,
    n_draws: int = 50_000,
    prevalences: Iterable[float] = DEFAULT_PREVALENCES,
) -> dict:
    """Évalue une graine du protocole pré-enregistré.

    Le bras comportemental est constant négatif dans la sous-population
    étudiée. La fusion OR se réduit donc algébriquement à l'EEG ; ``P3`` pince
    cette identité au lieu de lui attribuer un gain fictif.
    """

    p_values = tuple(float(value) for value in prevalences)
    if not p_values:
        raise ValueError("prevalences ne peut pas être vide")
    _probability_array(np.asarray(p_values), "prevalences")

    se, sp = sample_observer(CRUSE_CALIBRATION, seed=seed, n_draws=n_draws)
    se_auto, sp_auto = sample_observer(
        AUTOMATIC_RESPONSE_STRESS,
        seed=seed + 10_000,
        n_draws=n_draws,
    )

    calibrated: dict[str, dict[str, dict[str, float]]] = {}
    auto: dict[str, dict[str, dict[str, float]]] = {}
    medians: list[float] = []
    max_fusion_delta = 0.0

    for prevalence in p_values:
        ppv, p_negative = predictive_values(prevalence, se, sp)
        ppv_auto, p_negative_auto = predictive_values(
            prevalence, se_auto, sp_auto
        )
        key = f"{prevalence:.2f}"
        calibrated[key] = {
            "ppv": _quantiles(ppv),
            "p_capable_given_negative": _quantiles(p_negative),
        }
        auto[key] = {
            "ppv": _quantiles(ppv_auto),
            "p_capable_given_negative": _quantiles(p_negative_auto),
        }
        medians.append(calibrated[key]["ppv"]["median"])

        # Fusion OR avec un canal toujours négatif : Se et Sp inchangées.
        fusion_ppv, fusion_negative = predictive_values(prevalence, se, sp)
        max_fusion_delta = max(
            max_fusion_delta,
            float(np.max(np.abs(fusion_ppv - ppv))),
            float(np.max(np.abs(fusion_negative - p_negative))),
        )

    target = "0.20"
    if target not in calibrated:
        raise ValueError("Le protocole exige la prévalence cible 0.20")
    target_ppv = calibrated[target]["ppv"]
    target_negative = calibrated[target]["p_capable_given_negative"]
    auto_ratio = auto[target]["ppv"]["median"] / target_ppv["median"]

    gates = {
        "P1_positive_informative": (
            target_ppv["median"] >= 0.55 and target_ppv["q05"] >= 0.25
        ),
        "P2_negative_non_conclusive": target_negative["median"] >= 0.04,
        "P3_constant_channel_no_gain": max_fusion_delta < 1e-12,
        "P4_automatic_null_reduces_ppv": auto_ratio <= 0.60,
        "P5_ppv_increases_with_prevalence": all(
            left < right for left, right in zip(medians, medians[1:])
        ),
    }
    return {
        "seed": seed,
        "n_draws": n_draws,
        "calibrated": calibrated,
        "automatic_stress": auto,
        "automatic_ppv_ratio_at_0.20": float(auto_ratio),
        "max_fusion_delta": max_fusion_delta,
        "gates": gates,
    }


def run_preregistered_study(
    *,
    seeds: Iterable[int] = DEFAULT_SEEDS,
    n_draws: int = 50_000,
) -> dict:
    """Exécute les cinq graines et applique le verdict pré-enregistré."""

    seed_values = tuple(int(seed) for seed in seeds)
    if len(seed_values) < 5:
        raise ValueError("Le protocole pré-enregistré exige au moins 5 graines")
    rows = [evaluate_seed(seed, n_draws=n_draws) for seed in seed_values]
    pass_counts = {
        gate: sum(bool(row["gates"][gate]) for row in rows)
        for gate in rows[0]["gates"]
    }
    p1 = pass_counts["P1_positive_informative"] >= len(rows) - 1
    p2 = pass_counts["P2_negative_non_conclusive"] == len(rows)
    p3 = pass_counts["P3_constant_channel_no_gain"] == len(rows)
    p4 = pass_counts["P4_automatic_null_reduces_ppv"] >= len(rows) - 1
    p5 = pass_counts["P5_ppv_increases_with_prevalence"] == len(rows)
    if p1 and p2 and p3 and p4 and p5:
        verdict = "SUPPORTED"
    elif p2 and p3 and p5:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "FALSIFIED_MODEL"
    return {
        "source_counts": {
            "conscious_controls_positive": 9,
            "conscious_controls_total": 12,
            "null_controls_positive": 0,
            "null_controls_total": 12,
        },
        "seeds": list(seed_values),
        "pass_counts": pass_counts,
        "verdict": verdict,
        "rows": rows,
    }


if __name__ == "__main__":
    import json

    print(json.dumps(run_preregistered_study(), indent=1, ensure_ascii=False))
