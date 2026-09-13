"""Harnais de benchmark Optuna/Rustuna, agnostique du moteur.

Serie Search/Applications/Hybrid — consomme par App-18c (Regime D).
Absorbe les divergences d'API mesurees dans App-18c (rustuna 0.1.0) :

- ``rustuna`` n'a pas de ``study.best_value`` ;
- ``rustuna.study.best_trial`` ne rend PAS l'argmax (bug de reporting mesure
  dans la cellule de sonde d'App-18c) — seul ``study.trials`` est fiable ;
- les deux moteurs exposent ``create_study(direction=..., sampler=...)`` et
  ``study.optimize(objective, n_trials=...)`` a l'identique.

Le harnais n'importe donc AUCUN moteur : l'appelant fournit une fabrique
d'etude par moteur (``make_study(seed) -> study``), ce qui le rend testable
hors ligne avec des etudes factices (la CI n'a pas rustuna).

Convention de direction : ``best_value_of`` rend l'argmax — les objectifs de
la serie (TSP et derives) sont tous en ``direction="maximize"`` (longueur
neguee). Un objectif minimize doit etre reformule en maximise par l'appelant.
"""

from __future__ import annotations

import time
from dataclasses import dataclass
from typing import Callable, Mapping, Sequence

__all__ = ["BenchResult", "best_value_of", "bench", "compare", "render_table"]


@dataclass(frozen=True)
class BenchResult:
    """Une mesure : un moteur, une graine, n_trials evaluations."""

    engine: str
    seed: int
    n_trials: int
    elapsed_s: float
    best_value: float | None

    @property
    def trials_per_s(self) -> float | None:
        if self.elapsed_s <= 0:
            return None
        return self.n_trials / self.elapsed_s


def best_value_of(study) -> float | None:
    """Argmax sur TOUS les trials — jamais via ``best_trial``/``best_value``.

    ``rustuna 0.1.0`` : ``best_value`` n'existe pas et ``best_trial`` ne rend
    pas l'argmax (bug de reporting mesure dans App-18c). ``optuna`` rend les
    deux correctement, mais reprendre ``study.trials`` pour les deux moteurs
    est le seul chemin commun — et il est exact pour les deux.

    Tolere les representations de valeur des deux moteurs (scalaire ou liste),
    et saute les trials sans valeur (echecs) plutot que de crasher.
    """
    values = []
    for trial in study.trials:
        v = trial.values
        if v is None:
            continue
        values.append(v[0] if isinstance(v, (list, tuple)) else float(v))
    return max(values) if values else None


def bench(
    engine: str,
    make_study: Callable[[int], object],
    objective: Callable[[object], float],
    n_trials: int,
    seed: int,
) -> BenchResult:
    """Chronometre creation d'etude + boucle optimize, rend le meilleur score.

    Le chronometre couvre volontairement la creation de l'etude (sampler
    compris) : c'est le cout reel d'une session de tuning, pas seulement la
    boucle d'evaluation.
    """
    t0 = time.perf_counter()
    study = make_study(seed)
    study.optimize(objective, n_trials=n_trials)
    elapsed_s = time.perf_counter() - t0
    return BenchResult(
        engine=engine,
        seed=seed,
        n_trials=n_trials,
        elapsed_s=elapsed_s,
        best_value=best_value_of(study),
    )


def compare(
    make_study_by_engine: Mapping[str, Callable[[int], object]],
    objective: Callable[[object], float],
    n_trials: int,
    seeds: Sequence[int],
) -> list[BenchResult]:
    """Matrice complete : chaque moteur x chaque graine, ordre stable.

    Ordre moteur-major, graine-minor (celui des boucles des Regimes C/D
    d'App-18c) — ``render_table`` groupe visuellement par moteur sur cette
    base.
    """
    return [
        bench(engine, make_study, objective, n_trials, seed)
        for engine, make_study in make_study_by_engine.items()
        for seed in seeds
    ]


def render_table(results: Sequence[BenchResult]) -> str:
    """Table ASCII monospace : moteur, seed, trials, meilleur, s, trials/s."""
    header = f"{'moteur':<10} {'seed':>4} {'trials':>7} {'meilleur':>11} {'s':>8} {'trials/s':>9}"
    lines = [header, "-" * len(header)]
    for r in results:
        best = "-" if r.best_value is None else f"{r.best_value:.4f}"
        rate = "-" if r.trials_per_s is None else f"{r.trials_per_s:,.0f}"
        lines.append(
            f"{r.engine:<10} {r.seed:>4} {r.n_trials:>7} {best:>11} "
            f"{r.elapsed_s:>8.2f} {rate:>9}"
        )
    return "\n".join(lines)
