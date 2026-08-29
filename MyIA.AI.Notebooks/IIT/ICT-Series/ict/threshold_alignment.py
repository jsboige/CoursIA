"""Dissociation biais d'alignement / derive precoce (Schurger 2012, #8182).

Ce module formalise une question instrumentale, pas un modele de conscience
ni une preuve sur le libre arbitre. Un accumulateur stochastique borne evolue
sans derive deterministe ; le « mouvement » est le premier franchissement
d'un seuil absorbant. Le banc mesure alors :

- que la moyenne des trajectoires **alignees sur le franchissement** montre
  une rampe pre-evenement alors qu'aucun essai ne porte de derive
  (biais de selection, lecture Schurger) ;
- que la meme moyenne, alignee sur un instant **non informatif** (sham),
  reste plate (controle null) ;
- qu'une derive precoce authentique, injectee essai par essai, se separe
  de l'artefact par le niveau **non aligne** — la vue alignee seule restant
  ambigue entre les deux hypotheses.

Le protocole a ete scelle AVANT implementation dans
``docs/ict/threshold-alignment-pre-enregistrement.md`` au commit
``fb4d92715``, puis re-verrouille en v2 au commit ``9391a21df`` : les
parametres v1 rendaient le seuil inatteignable (0 franchissement sur
2 000 essais x 5 000 pas), fait constate avant toute evaluation de gate.
Les bandes v2 sont calibrees sur la graine 1000, disjointe des graines
d'etude. Aucune donnee EEG n'est analysee ; aucune claim n'est faite sur
l'origine des intentions.

References
----------
Aaron Schurger, Jacobo D. Sitt et Stanislas Dehaene, « An accumulator model
for spontaneous neural activity prior to self-initiated movement », PNAS 109
(2012), E2904-E2913, DOI 10.1073/pnas.1210467109. Lecture firsthand
2026-08-29. Contexte historique non relu : Kornhuber & Deecke 1965 ;
Libet et al., Brain 106 (1983), 623-642.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Iterable

import numpy as np

__all__ = [
    "AccumulatorConfig",
    "simulate_accumulator",
    "evaluate_seed",
    "derive_verdict",
    "run_preregistered_study",
]

# --- Parametres scelles par le pre-enregistrement ---------------------------

DEFAULT_SEEDS = (0, 1, 7, 42, 99)

WINDOW = 60           # fenetre pre-evenement, lags -59..0 (evenement inclus)
EARLY_SPAN = 15       # 15 premiers points de la fenetre
LATE_SPAN = 15        # 15 derniers points de la fenetre
MIN_CROSSING_INDEX = 61  # il faut c >= 61 pour une fenetre sham non vide
T_MAX = 5_000
N_TRIALS = 2_000

SEED_OFFSETS = {
    "trials_null": 0,
    "trials_drift": 10_000,
    "sham_null": 20_000,
    "sham_drift": 30_000,
}

GATE_NAMES = (
    "P1_alignment_ramp_without_drift",
    "P2_sham_null_flat",
    "P3_aligned_view_not_discriminant",
    "P4_sham_elevation_separates",
    "P5_artifact_localized",
)

# Bandes numeriques v2, scellees avant evaluation de gate (unites : seuil b
# par pas). Derivees de la calibration de faisabilite (graine 1000) avec des
# marges >= 2x, cf. docs/ict/threshold-alignment-pre-enregistrement.md.
SLOPE_RAMP_FLOOR = 0.0030
SHAM_SLOPE_BAND = 0.0010
SHAM_ELEVATION_FLOOR = 0.060
AMPLITUDE_FLOOR = 0.14
EARLY_VS_SHAM_BAND = 0.10


@dataclass(frozen=True)
class AccumulatorConfig:
    """Parametres d'un bras de l'accumulateur stochastique borne.

    Dynamique : ``x <- max(0, x - leak*x + drift + sigma*eps)`` avec
    ``eps ~ N(0, 1)`` iid ; le seuil ``threshold`` est absorbant.
    """

    leak: float
    sigma: float
    threshold: float
    drift: float = 0.0
    n_trials: int = N_TRIALS
    t_max: int = T_MAX

    def __post_init__(self) -> None:
        if not 0.0 <= self.leak < 1.0:
            raise ValueError(f"leak doit etre dans [0, 1) (recu {self.leak})")
        if self.sigma < 0.0:
            raise ValueError(f"sigma doit etre >= 0 (recu {self.sigma})")
        if self.threshold <= 0.0:
            raise ValueError(
                f"threshold doit etre > 0 (recu {self.threshold})"
            )
        if self.drift < 0.0:
            raise ValueError(f"drift doit etre >= 0 (recu {self.drift})")
        if self.n_trials <= 0:
            raise ValueError(f"n_trials doit etre > 0 (recu {self.n_trials})")
        if self.t_max <= 0:
            raise ValueError(f"t_max doit etre > 0 (recu {self.t_max})")


NULL_CONFIG = AccumulatorConfig(leak=0.10, sigma=0.15, threshold=1.0, drift=0.0)
DRIFT_CONFIG = replace(NULL_CONFIG, drift=0.035)

_LAGS = np.arange(-(WINDOW - 1), 1, dtype=float)


# --- Simulation --------------------------------------------------------------


def simulate_accumulator(
    config: AccumulatorConfig,
    *,
    seed: int,
) -> dict:
    """Simule ``n_trials`` essais et retourne trajectoires et franchissements.

    A chaque pas, le bruit est tire pour l'integralite des essais : le flux
    pseudo-aleatoire ne depend donc pas du sous-ensemble d'essais encore
    actifs, ce qui rend la simulation deterministe par construction pour une
    graine donnee. Les essais franchis restent figes a leur valeur de
    franchissement ; les essais jamais franchis a ``t_max`` sont comptes dans
    ``n_uncrossed`` avec un indice de franchissement egal a ``-1``.
    """

    rng = np.random.default_rng(seed)
    n = config.n_trials
    x = np.zeros(n, dtype=float)
    crossing = np.full(n, -1, dtype=np.int64)
    active = np.arange(n)
    columns: list[np.ndarray] = [x.copy()]
    t = 0
    while active.size > 0 and t < config.t_max:
        t += 1
        eps = rng.standard_normal(n)
        nxt = (
            x[active]
            - config.leak * x[active]
            + config.drift
            + config.sigma * eps[active]
        )
        np.maximum(nxt, 0.0, out=nxt)  # reflexion en 0
        x[active] = nxt
        columns.append(x.copy())
        crossed = nxt >= config.threshold
        newly = active[crossed]
        crossing[newly] = t
        active = active[~crossed]
    return {
        "config": config,
        "history": np.column_stack(columns),  # (n_trials, t + 1)
        "crossing": crossing,
        "n_uncrossed": int(active.size),
    }


# --- Analyse -----------------------------------------------------------------


def _ols_slope(values: np.ndarray) -> float:
    """Pente OLS de la moyenne de fenetre sur les lags -59..0."""

    if values.shape[-1] != WINDOW:
        raise ValueError(f"la fenetre doit avoir {WINDOW} points")
    return float(np.polyfit(_LAGS, values, 1)[0])


def _window_summary(average: np.ndarray) -> dict:
    early = float(np.mean(average[:EARLY_SPAN]))
    late = float(np.mean(average[-LATE_SPAN:]))
    return {
        "slope": _ols_slope(average),
        "early_mean": early,
        "late_mean": late,
        "amplitude": late - early,
    }


def _arm_metrics(
    config: AccumulatorConfig,
    *,
    trial_seed: int,
    sham_seed: int,
) -> dict:
    """Mesure un bras : moyenne alignee sur le franchissement + moyenne sham."""

    sim = simulate_accumulator(config, seed=trial_seed)
    crossing = sim["crossing"]
    history = sim["history"]
    analyzable = crossing >= MIN_CROSSING_INDEX
    n_analyzed = int(np.count_nonzero(analyzable))
    row: dict = {
        "n_trials": config.n_trials,
        "n_crossed": int(np.count_nonzero(crossing >= 1)),
        "n_analyzed": n_analyzed,
        "n_short_excluded": int(
            np.count_nonzero((crossing >= 1) & ~analyzable)
        ),
        "n_uncrossed": sim["n_uncrossed"],
        "mean_crossing_index": (
            float(np.mean(crossing[crossing >= 1]))
            if np.any(crossing >= 1)
            else float("nan")
        ),
    }
    if n_analyzed == 0:
        raise ValueError(
            "aucun essai analysable : le bras ne permet pas une mesure "
            "honnete (fenetre vide) et refuse de fabriquer une metrique"
        )

    indices = np.flatnonzero(analyzable)
    c = crossing[indices]
    aligned = history[indices[:, None], c[:, None] - WINDOW + 1 + np.arange(WINDOW)[None, :]]
    average_aligned = aligned.mean(axis=0)

    sham_rng = np.random.default_rng(sham_seed)
    a = sham_rng.integers(MIN_CROSSING_INDEX - 1, c)  # a uniforme dans {60..c-1}
    sham = history[indices[:, None], a[:, None] - WINDOW + 1 + np.arange(WINDOW)[None, :]]
    average_sham = sham.mean(axis=0)

    row["aligned"] = _window_summary(average_aligned)
    row["sham"] = {
        "slope": _ols_slope(average_sham),
        "mean": float(np.mean(average_sham)),
    }
    return row


def _gates(null_row: dict, drift_row: dict) -> dict:
    aligned_slope_null = null_row["aligned"]["slope"]
    sham_slope_null = null_row["sham"]["slope"]
    return {
        "P1_alignment_ramp_without_drift": (
            aligned_slope_null >= SLOPE_RAMP_FLOOR
            and aligned_slope_null >= 5.0 * abs(sham_slope_null)
        ),
        "P2_sham_null_flat": abs(sham_slope_null) <= SHAM_SLOPE_BAND,
        "P3_aligned_view_not_discriminant": (
            aligned_slope_null >= SLOPE_RAMP_FLOOR
            and drift_row["aligned"]["slope"] >= SLOPE_RAMP_FLOOR
        ),
        "P4_sham_elevation_separates": (
            drift_row["sham"]["mean"] - null_row["sham"]["mean"]
            >= SHAM_ELEVATION_FLOOR
        ),
        "P5_artifact_localized": (
            null_row["aligned"]["amplitude"] >= AMPLITUDE_FLOOR
            and abs(
                null_row["aligned"]["early_mean"] - null_row["sham"]["mean"]
            )
            <= EARLY_VS_SHAM_BAND
        ),
    }


def evaluate_seed(
    seed: int,
    *,
    null_config: AccumulatorConfig = NULL_CONFIG,
    drift_config: AccumulatorConfig = DRIFT_CONFIG,
) -> dict:
    """Evalue une graine du protocole pre-enregistre."""

    null_row = _arm_metrics(
        null_config,
        trial_seed=seed + SEED_OFFSETS["trials_null"],
        sham_seed=seed + SEED_OFFSETS["sham_null"],
    )
    drift_row = _arm_metrics(
        drift_config,
        trial_seed=seed + SEED_OFFSETS["trials_drift"],
        sham_seed=seed + SEED_OFFSETS["sham_drift"],
    )
    gates = _gates(null_row, drift_row)
    return {
        "seed": seed,
        "null_arm": null_row,
        "drift_arm": drift_row,
        "sham_elevation_discriminant": (
            drift_row["sham"]["mean"] - null_row["sham"]["mean"]
        ),
        "gates": gates,
    }


def derive_verdict(gates_per_seed: Iterable[dict]) -> str:
    """Applique le verdict tri-etat scelle par le pre-enregistrement.

    ``SUPPORTED`` si P1-P5 passent dans >= 4/5 graines ;
    ``FALSIFIED_MODEL`` si P1 ou P2 echoue (artefact non reproduit ou
    controle null faux-positif) ; ``INCONCLUSIVE`` sinon.
    """

    rows = [dict(gates) for gates in gates_per_seed]
    if len(rows) < 2:
        raise ValueError("le verdict exige au moins deux graines")
    counts = {
        gate: sum(bool(row[gate]) for row in rows) for gate in GATE_NAMES
    }
    if counts["P1_alignment_ramp_without_drift"] >= len(rows) - 1 and counts[
        "P2_sham_null_flat"
    ] >= len(rows) - 1:
        if all(count >= len(rows) - 1 for count in counts.values()):
            return "SUPPORTED"
        return "INCONCLUSIVE"
    return "FALSIFIED_MODEL"


def run_preregistered_study(
    *,
    seeds: Iterable[int] = DEFAULT_SEEDS,
) -> dict:
    """Execute les cinq graines et applique le verdict pre-enregistre."""

    seed_values = tuple(int(seed) for seed in seeds)
    if len(seed_values) < 5:
        raise ValueError("le protocole pre-enregistre exige au moins 5 graines")
    rows = [evaluate_seed(seed) for seed in seed_values]
    pass_counts = {
        gate: sum(bool(row["gates"][gate]) for row in rows)
        for gate in GATE_NAMES
    }
    return {
        "reference": {
            "primary": "Schurger, Sitt & Dehaene, PNAS 109 (2012), E2904-E2913",
            "doi": "10.1073/pnas.1210467109",
            "preregistration": "docs/ict/threshold-alignment-pre-enregistrement.md",
        },
        "config": {
            "leak": NULL_CONFIG.leak,
            "sigma": NULL_CONFIG.sigma,
            "threshold": NULL_CONFIG.threshold,
            "drift_null": NULL_CONFIG.drift,
            "drift_comparator": DRIFT_CONFIG.drift,
            "n_trials": NULL_CONFIG.n_trials,
            "t_max": NULL_CONFIG.t_max,
            "window": WINDOW,
            "early_span": EARLY_SPAN,
            "late_span": LATE_SPAN,
            "min_crossing_index": MIN_CROSSING_INDEX,
            "seed_offsets": SEED_OFFSETS,
        },
        "seeds": list(seed_values),
        "pass_counts": pass_counts,
        "verdict": derive_verdict(row["gates"] for row in rows),
        "aggregate": {
            "aligned_slope_null_mean": float(
                np.mean([row["null_arm"]["aligned"]["slope"] for row in rows])
            ),
            "sham_slope_null_abs_mean": float(
                np.mean(
                    [abs(row["null_arm"]["sham"]["slope"]) for row in rows]
                )
            ),
            "aligned_slope_drift_mean": float(
                np.mean([row["drift_arm"]["aligned"]["slope"] for row in rows])
            ),
            "aligned_amplitude_null_mean": float(
                np.mean(
                    [
                        row["null_arm"]["aligned"]["amplitude"]
                        for row in rows
                    ]
                )
            ),
            "sham_elevation_discriminant_mean": float(
                np.mean(
                    [row["sham_elevation_discriminant"] for row in rows]
                )
            ),
        },
        "rows": rows,
    }


if __name__ == "__main__":
    import json

    print(json.dumps(run_preregistered_study(), indent=1, ensure_ascii=False))
