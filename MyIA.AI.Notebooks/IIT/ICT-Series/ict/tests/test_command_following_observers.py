"""Tests du banc Owen/Cruse de suivi de commande covert (#8182).

Les gates P1-P5 viennent du pré-enregistrement scellé au commit ``103fdb23c``.
Les tests ne mesurent pas la conscience : ils pincent la calibration et la
portée diagnostique d'un observateur de capacité opérationnelle.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.command_following_observers import (
    Calibration,
    evaluate_seed,
    predictive_values,
    run_preregistered_study,
    sample_observer,
)


class TestClosedFormControls:
    def test_perfect_specificity_makes_positive_decisive(self):
        ppv, _ = predictive_values(0.20, 0.75, 1.0)
        assert float(ppv) == pytest.approx(1.0)

    def test_uninformative_observer_returns_prevalence(self):
        ppv, p_negative = predictive_values(0.20, 0.70, 0.30)
        assert float(ppv) == pytest.approx(0.20)
        assert float(p_negative) == pytest.approx(0.20)

    def test_ppv_increases_with_specificity(self):
        low, _ = predictive_values(0.20, 0.75, 0.60)
        high, _ = predictive_values(0.20, 0.75, 0.95)
        assert float(low) < float(high)

    def test_invalid_probability_rejected(self):
        with pytest.raises(ValueError):
            predictive_values(1.2, 0.75, 0.95)

    def test_invalid_beta_parameter_rejected(self):
        with pytest.raises(ValueError):
            Calibration(0.0, 1.0, 1.0, 1.0)


class TestSampling:
    def test_seed_is_deterministic(self):
        calibration = Calibration(10.0, 4.0, 13.0, 1.0)
        first = sample_observer(calibration, seed=7, n_draws=100)
        second = sample_observer(calibration, seed=7, n_draws=100)
        assert np.array_equal(first[0], second[0])
        assert np.array_equal(first[1], second[1])

    def test_non_positive_sample_size_rejected(self):
        with pytest.raises(ValueError):
            sample_observer(Calibration(1.0, 1.0, 1.0, 1.0), seed=0, n_draws=0)


@pytest.fixture(scope="module")
def standard_study() -> dict:
    return run_preregistered_study()


class TestPreregisteredPredictions:
    def test_p1_positive_is_informative(self, standard_study):
        assert standard_study["pass_counts"]["P1_positive_informative"] >= 4

    def test_p2_negative_remains_non_conclusive(self, standard_study):
        assert standard_study["pass_counts"]["P2_negative_non_conclusive"] == 5

    def test_p3_constant_behavior_channel_adds_no_information(self, standard_study):
        assert standard_study["pass_counts"]["P3_constant_channel_no_gain"] == 5
        assert all(row["max_fusion_delta"] == 0.0 for row in standard_study["rows"])

    def test_p4_automatic_response_stress_reduces_ppv(self, standard_study):
        assert standard_study["pass_counts"]["P4_automatic_null_reduces_ppv"] >= 4

    def test_p5_ppv_depends_on_prevalence(self, standard_study):
        assert standard_study["pass_counts"]["P5_ppv_increases_with_prevalence"] == 5

    def test_verdict_is_explicit(self, standard_study):
        assert standard_study["verdict"] in {
            "SUPPORTED",
            "INCONCLUSIVE",
            "FALSIFIED_MODEL",
        }

    def test_cruse_source_counts_are_preserved(self, standard_study):
        assert standard_study["source_counts"] == {
            "conscious_controls_positive": 9,
            "conscious_controls_total": 12,
            "null_controls_positive": 0,
            "null_controls_total": 12,
        }

    def test_fewer_than_five_seeds_rejected(self):
        with pytest.raises(ValueError):
            run_preregistered_study(seeds=(0, 1, 7, 42))


class TestSingleSeedShape:
    def test_expected_prevalence_grid_is_present(self):
        row = evaluate_seed(0, n_draws=1_000)
        assert list(row["calibrated"]) == ["0.05", "0.10", "0.20", "0.40"]

    def test_target_prevalence_is_required(self):
        with pytest.raises(ValueError):
            evaluate_seed(0, n_draws=100, prevalences=(0.05, 0.10))
