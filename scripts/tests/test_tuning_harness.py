"""Tests hors ligne du harnais de benchmark Optuna/Rustuna (App-18c, #15659).

Aucun moteur requis : le harnais est agnostique et se teste sur des etudes
factices. C'est la garantie CI — la CI n'a pas rustuna, les tests ne doivent
pas en dependre.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "MyIA.AI.Notebooks" / "Search" / "Applications" / "Hybrid"))

from tuning_harness import (  # noqa: E402
    BenchResult,
    bench,
    best_value_of,
    compare,
    render_table,
)


@dataclass
class FakeTrial:
    """Trial factice : `values` liste (optuna), scalaire (rustuna) ou None (echec)."""

    values: object


class FakeStudy:
    """Etude factice minimale : le seul contrat du harnais est `trials` + `optimize`."""

    def __init__(self, trials):
        self.trials = list(trials)
        self.optimize_calls = []

    def optimize(self, objective, n_trials=None):
        self.optimize_calls.append((objective, n_trials))


class WrongBestTrialStudy(FakeStudy):
    """Reproduit le bug mesure de rustuna 0.1.0 : `best_trial` rend un trial
    qui n'est PAS l'argmax, et `best_value` n'existe pas du tout."""

    def __init__(self, trials):
        super().__init__(trials)
        self.best_trial = trials[0]

    # pas de best_value : deliberement absent


def _study_list_values():
    return FakeStudy([FakeTrial([-700.0]), FakeTrial([-655.5]), FakeTrial([-680.2])])


def _study_scalar_values():
    return FakeStudy([FakeTrial(-700.0), FakeTrial(-655.5), FakeTrial(-680.2)])


class TestBestValueOf:
    def test_list_valued_trials_optuna_shape(self):
        assert best_value_of(_study_list_values()) == -655.5

    def test_scalar_valued_trials_rustuna_shape(self):
        assert best_value_of(_study_scalar_values()) == -655.5

    def test_mixed_shapes(self):
        study = FakeStudy([FakeTrial([-700.0]), FakeTrial(-655.5)])
        assert best_value_of(study) == -655.5

    def test_empty_study_rend_none(self):
        assert best_value_of(FakeStudy([])) is None

    def test_failed_trials_skipped_not_crash(self):
        study = FakeStudy([FakeTrial(None), FakeTrial([-655.5]), FakeTrial(None)])
        assert best_value_of(study) == -655.5

    def test_all_failed_rend_none(self):
        assert best_value_of(FakeStudy([FakeTrial(None)])) is None

    def test_never_relies_on_best_trial_or_best_value(self):
        """Le pin du bug rustuna : best_trial renvoie -700.0 (pas l'argmax) et
        best_value n'existe pas — le harnais doit rendre l'argmax quand meme.
        Toute consultation de l'un de ces attributs fait echouer ce test
        (AttributeError ou valeur -700.0)."""
        study = WrongBestTrialStudy([FakeTrial(-700.0), FakeTrial(-655.5)])
        assert best_value_of(study) == -655.5
        assert not hasattr(study, "best_value")

    def test_negative_max_is_not_absorbed(self):
        """Tous les objectifs de la serie sont negatifs (longueur TSP niee) :
        l'argmax de valeurs toutes negatives reste le plus proche de zero."""
        study = FakeStudy([FakeTrial([-600.1]), FakeTrial([-900.9])])
        assert best_value_of(study) == -600.1


class TestBench:
    def test_fields_and_calls(self):
        seen = {}

        def make_study(seed):
            seen["seed"] = seed
            return _study_list_values()

        def objective(trial):
            return 0.0

        result = bench("Optuna", make_study, objective, n_trials=2000, seed=7)

        assert seen["seed"] == 7
        assert isinstance(result, BenchResult)
        assert result.engine == "Optuna"
        assert result.seed == 7
        assert result.n_trials == 2000
        assert result.best_value == -655.5

    def test_optimize_receives_objective_and_n_trials(self):
        study = _study_scalar_values()
        objective = lambda t: 0.0  # noqa: E731
        bench("Rustuna", lambda seed: study, objective, n_trials=500, seed=0)
        assert study.optimize_calls == [(objective, 500)]

    def test_elapsed_is_measured_positive(self):
        result = bench("Optuna", lambda seed: _study_list_values(), lambda t: 0.0, 10, 0)
        assert result.elapsed_s > 0

    def test_trials_per_s(self):
        r = BenchResult(engine="x", seed=0, n_trials=100, elapsed_s=0.25, best_value=1.0)
        assert r.trials_per_s == 400.0

    def test_trials_per_s_zero_elapsed_is_none(self):
        r = BenchResult(engine="x", seed=0, n_trials=100, elapsed_s=0.0, best_value=1.0)
        assert r.trials_per_s is None


class TestCompare:
    def test_order_engine_major_seed_minor(self):
        studies = {
            "Optuna": lambda seed: _study_list_values(),
            "Rustuna": lambda seed: _study_scalar_values(),
        }
        results = compare(studies, lambda t: 0.0, n_trials=50, seeds=(0, 1, 7))
        assert [(r.engine, r.seed) for r in results] == [
            ("Optuna", 0), ("Optuna", 1), ("Optuna", 7),
            ("Rustuna", 0), ("Rustuna", 1), ("Rustuna", 7),
        ]

    def test_count_is_engines_times_seeds(self):
        results = compare({"a": lambda s: _study_list_values(),
                           "b": lambda s: _study_list_values(),
                           "c": lambda s: _study_list_values()},
                          lambda t: 0.0, 10, seeds=(0, 1))
        assert len(results) == 6

    def test_seed_reaches_each_factory(self):
        seeds_seen = []

        def make(seed):
            seeds_seen.append(seed)
            return _study_list_values()

        compare({"only": make}, lambda t: 0.0, 5, seeds=(3, 4))
        assert seeds_seen == [3, 4]


class TestRenderTable:
    def test_header_and_one_line_per_result(self):
        results = [
            BenchResult("Optuna", 0, 2000, 28.6, -655.5),
            BenchResult("Rustuna", 0, 2000, 4.9, -700.1),
        ]
        table = render_table(results)
        lines = table.splitlines()
        assert len(lines) == 4  # entete + separateur + 2 resultats
        assert lines[0].split()[:2] == ["moteur", "seed"]
        assert "Optuna" in lines[2] and "Rustuna" in lines[3]

    def test_none_best_value_renders_dash(self):
        r = BenchResult("x", 0, 10, 1.0, None)
        assert "-" in render_table([r]).splitlines()[2]

    def test_negative_best_value_rendered(self):
        r = BenchResult("x", 0, 10, 1.0, -655.5)
        assert "-655.5" in render_table([r])
