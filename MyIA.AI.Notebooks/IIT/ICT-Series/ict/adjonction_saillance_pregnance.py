"""Test borné du canal saillance-prégnance proposé par #13580.

Le prototype ``docs/ict/strates-as-adjunctions-prototype.md`` proposait une
fonction ``f_aj(s, pi)`` comme témoin d'une adjonction. Une fonction scalaire
n'est toutefois pas une adjonction catégorielle : ce module ne définit ni
catégories, ni foncteurs, ni bijection naturelle de hom-sets. Il teste seulement
une signature empirique plus faible : un canal de décision bilinéaire répond-il
aux deux entrées indépendantes, contrairement à deux nulls mono-canal ?

La dette d'inhibition d'ICT-30 appartient par ailleurs à un autre substrat. Elle
est donc déclarée ``NOT_TESTABLE_ON_THIS_SUBSTRATE`` plutôt que remplacée par
une métrique commode. L'entropie de décision est rapportée à titre diagnostique,
sans être appelée dette d'inhibition.

Le protocole et ses seuils ont été amendés dans le document prototype avant la
première exécution de cette tranche. Les graines d'étude sont fixées à
``(0, 1, 7, 42, 99)``.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Iterable

import numpy as np

from ict.salience_valence_dissociation import (
    learn_valences,
    measure_decision_given_detected,
    partial_spearman,
    stimulus_battery,
)

__all__ = [
    "CouplingConfig",
    "couple_engagement",
    "evaluate_seed",
    "derive_operational_verdict",
    "run_preregistered_study",
]

DEFAULT_SEEDS = (0, 1, 7, 42, 99)
P1_GATE_NAMES = (
    "P1_coupled_responds_to_both_channels",
    "P1_null_s_excludes_pi",
    "P1_null_pi_excludes_s",
)
GATE_NAMES = P1_GATE_NAMES + ("P3_scalar_operation_ratio_at_most_two",)


@dataclass(frozen=True)
class CouplingConfig:
    """Paramètres scellés du banc NumPy CPU-only."""

    n_stimuli: int = 160
    n_epochs: int = 200
    alpha: float = 0.15
    n_trials: int = 500
    kappa: float = 2.0
    mu: float = 2.0
    nu: float = 2.0
    joint_partial_floor: float = 0.40
    absent_partial_ceiling: float = 0.20

    def __post_init__(self) -> None:
        if self.n_stimuli < 20:
            raise ValueError("n_stimuli doit être >= 20")
        if self.n_epochs <= 0 or self.n_trials <= 0:
            raise ValueError("n_epochs et n_trials doivent être > 0")
        if not 0.0 < self.alpha <= 1.0:
            raise ValueError("alpha doit être dans ]0, 1]")
        if min(self.kappa, self.mu, self.nu) < 0.0:
            raise ValueError("les coefficients du canal doivent être >= 0")
        if not 0.0 < self.joint_partial_floor < 1.0:
            raise ValueError("joint_partial_floor doit être dans ]0, 1[")
        if not 0.0 < self.absent_partial_ceiling < 1.0:
            raise ValueError("absent_partial_ceiling doit être dans ]0, 1[")


def _sigmoid(values: np.ndarray) -> np.ndarray:
    values = np.asarray(values, dtype=float)
    return np.where(
        values >= 0.0,
        1.0 / (1.0 + np.exp(-values)),
        np.exp(values) / (1.0 + np.exp(values)),
    )


def couple_engagement(
    salience: np.ndarray,
    pregnance: np.ndarray,
    *,
    mode: str = "coupled",
    config: CouplingConfig = CouplingConfig(),
) -> np.ndarray:
    """Retourne ``P(approche | détecté)`` pour le traitement ou un null.

    ``coupled`` ajoute l'interaction bilinéaire ``s*pi`` à un modèle additif
    deux-canaux. ``null_s`` et ``null_pi`` suppriment respectivement la
    prégnance et la saillance ; varier le canal absent ne peut donc rien changer.
    """

    s = np.asarray(salience, dtype=float)
    pi = np.asarray(pregnance, dtype=float)
    if s.shape != pi.shape:
        raise ValueError("salience et pregnance doivent avoir la même forme")
    if mode == "coupled":
        logits = config.kappa * s + config.mu * pi + config.nu * s * pi
    elif mode == "null_s":
        logits = config.kappa * s
    elif mode == "null_pi":
        logits = config.mu * pi
    else:
        raise ValueError(f"mode inconnu : {mode}")
    return _sigmoid(logits)


def _binary_entropy(probabilities: np.ndarray) -> float:
    p = np.clip(np.asarray(probabilities, dtype=float), 1e-12, 1.0 - 1e-12)
    return float(np.mean(-(p * np.log2(p) + (1.0 - p) * np.log2(1.0 - p))))


def _partials(
    salience: np.ndarray,
    pregnance: np.ndarray,
    decisions: np.ndarray,
) -> dict[str, float]:
    return {
        "pi_given_s": float(partial_spearman(pregnance, decisions, [salience])),
        "s_given_pi": float(partial_spearman(salience, decisions, [pregnance])),
    }


def evaluate_seed(
    seed: int,
    *,
    config: CouplingConfig = CouplingConfig(),
) -> dict:
    """Évalue une graine held-out avec des flux aléatoires séparés par bras."""

    rng = np.random.default_rng(int(seed))
    salience, rewards = stimulus_battery(config.n_stimuli, rng=rng)
    pregnance = learn_valences(
        rewards,
        n_epochs=config.n_epochs,
        alpha=config.alpha,
        rng=rng,
    )

    probabilities = {
        mode: couple_engagement(salience, pregnance, mode=mode, config=config)
        for mode in ("coupled", "null_s", "null_pi")
    }
    seed_offsets = {"coupled": 10_000, "null_s": 20_000, "null_pi": 30_000}
    decisions = {
        mode: measure_decision_given_detected(
            salience,
            probability,
            n_trials=config.n_trials,
            rng=np.random.default_rng(int(seed) + seed_offsets[mode]),
        )
        for mode, probability in probabilities.items()
    }
    partials = {
        mode: _partials(salience, pregnance, decision)
        for mode, decision in decisions.items()
    }

    # Modèle additif deux-canaux : 2 multiplications + 1 addition = 3 ops.
    # Canal couplé : + produit s*pi, multiplication par nu et addition = 6 ops.
    additive_ops = 3
    coupled_ops = 6
    operation_ratio = coupled_ops / additive_ops

    gates = {
        "P1_coupled_responds_to_both_channels": (
            abs(partials["coupled"]["pi_given_s"]) >= config.joint_partial_floor
            and abs(partials["coupled"]["s_given_pi"])
            >= config.joint_partial_floor
        ),
        "P1_null_s_excludes_pi": (
            abs(partials["null_s"]["pi_given_s"])
            <= config.absent_partial_ceiling
            and abs(partials["null_s"]["s_given_pi"])
            >= config.joint_partial_floor
        ),
        "P1_null_pi_excludes_s": (
            abs(partials["null_pi"]["s_given_pi"])
            <= config.absent_partial_ceiling
            and abs(partials["null_pi"]["pi_given_s"])
            >= config.joint_partial_floor
        ),
        "P3_scalar_operation_ratio_at_most_two": operation_ratio <= 2.0,
    }
    if operation_ratio <= 2.0:
        complexity_verdict = "SUPPORTED"
    elif operation_ratio > 5.0:
        complexity_verdict = "FALSIFIED"
    else:
        complexity_verdict = "INCONCLUSIVE"

    return {
        "seed": int(seed),
        "rho_s_pi": float(np.corrcoef(salience, pregnance)[0, 1]),
        "partials": partials,
        "decision_entropy_bits": {
            mode: _binary_entropy(probability)
            for mode, probability in probabilities.items()
        },
        "complexity": {
            "additive_two_channel_scalar_ops": additive_ops,
            "coupled_scalar_ops": coupled_ops,
            "ratio": float(operation_ratio),
            "asymptotic_order": "O(n_stimuli)",
            "verdict": complexity_verdict,
        },
        "P2_original_inhibition_debt": "NOT_TESTABLE_ON_THIS_SUBSTRATE",
        "gates": gates,
    }


def derive_operational_verdict(gates_per_seed: Iterable[dict]) -> str:
    """Dérive le verdict du canal, sans requalifier la spécification originale."""

    rows = [dict(gates) for gates in gates_per_seed]
    if len(rows) < 5:
        raise ValueError("le protocole exige au moins cinq graines")
    counts = {gate: sum(bool(row[gate]) for row in rows) for gate in GATE_NAMES}
    if all(counts[gate] >= len(rows) - 1 for gate in P1_GATE_NAMES):
        return "SUPPORTED_OPERATIONAL_CHANNEL"
    return "FALSIFIED_OPERATIONAL_CHANNEL"


def run_preregistered_study(
    *,
    seeds: Iterable[int] = DEFAULT_SEEDS,
    config: CouplingConfig = CouplingConfig(),
) -> dict:
    """Exécute les cinq graines et conserve deux niveaux de verdict."""

    seed_values = tuple(int(seed) for seed in seeds)
    if len(seed_values) < 5:
        raise ValueError("le protocole exige au moins cinq graines")
    rows = [evaluate_seed(seed, config=config) for seed in seed_values]
    pass_counts = {
        gate: sum(bool(row["gates"][gate]) for row in rows)
        for gate in GATE_NAMES
    }
    return {
        "reference": {
            "prototype": "docs/ict/strates-as-adjunctions-prototype.md#41-amendement-pre-execution--observables-et-frontieres",
            "substrate": "ict.salience_valence_dissociation",
            "source_issue": 8182,
            "source_pr": 13580,
        },
        "config": asdict(config),
        "seeds": list(seed_values),
        "pass_counts": pass_counts,
        "verdicts": {
            "original_specification": "FALSIFIED_SPECIFICATION",
            "operational_channel": derive_operational_verdict(
                row["gates"] for row in rows
            ),
            "P2_inhibition_debt": "NOT_TESTABLE_ON_THIS_SUBSTRATE",
            "categorical_adjunction": "NOT_ESTABLISHED",
        },
        "aggregate": {
            "coupled_abs_partial_pi_median": float(
                np.median([abs(row["partials"]["coupled"]["pi_given_s"]) for row in rows])
            ),
            "coupled_abs_partial_s_median": float(
                np.median([abs(row["partials"]["coupled"]["s_given_pi"]) for row in rows])
            ),
            "operation_ratio": float(rows[0]["complexity"]["ratio"]),
        },
        "rows": rows,
    }
