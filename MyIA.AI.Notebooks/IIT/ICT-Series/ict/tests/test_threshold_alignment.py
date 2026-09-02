"""Tests du banc Schurger de dissociation alignement/derive precoce (#8182).

Les gates P1-P5 et le verdict tri-etat viennent du pre-enregistrement scelle
au commit ``fb4d92715`` puis re-verrouille en v2 au commit ``9391a21df``
(docs/ict/threshold-alignment-pre-enregistrement.md). Les tests ne mesurent
ni la conscience ni le libre arbitre : ils pincent la semantique de
franchissement de seuil, le controle null sham, la separation du
comparateur a derive et la derivation du verdict.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import pytest

from ict.threshold_alignment import (
    AccumulatorConfig,
    derive_verdict,
    evaluate_seed,
    run_preregistered_study,
    simulate_accumulator,
    GATE_NAMES,
)

RESULTS_PATH = Path(__file__).resolve().parent.parent / (
    "results/threshold_alignment_results.json"
)


class TestSimulationSemantics:
    def test_pure_deterministic_drift_crosses_at_ceiling_ratio(self):
        config = AccumulatorConfig(
            leak=0.0, sigma=0.0, threshold=1.0, drift=0.2, n_trials=8
        )
        sim = simulate_accumulator(config, seed=0)
        assert sim["n_uncrossed"] == 0
        assert np.all(sim["crossing"] == 5)  # premier t avec 0.2*t >= 1
        assert sim["history"][0, 5] == pytest.approx(1.0)

    def test_previous_step_stays_below_threshold(self):
        sim = simulate_accumulator(
            AccumulatorConfig(leak=0.08, sigma=0.06, threshold=1.0),
            seed=7,
        )
        crossed = sim["crossing"] >= 1
        assert np.all(
            sim["history"][crossed, sim["crossing"][crossed] - 1] < 1.0
        )
        assert np.all(
            sim["history"][crossed, sim["crossing"][crossed]] >= 1.0
        )

    def test_reflection_keeps_accumulator_non_negative(self):
        sim = simulate_accumulator(
            AccumulatorConfig(leak=0.5, sigma=0.5, threshold=50.0, n_trials=64),
            seed=42,
        )
        assert sim["history"].min() >= 0.0

    def test_noiseless_zero_drift_never_crosses(self):
        config = AccumulatorConfig(
            leak=0.08, sigma=0.0, threshold=1.0, drift=0.0, n_trials=8
        )
        sim = simulate_accumulator(config, seed=0)
        assert sim["n_uncrossed"] == config.n_trials
        assert np.all(sim["crossing"] == -1)

    def test_same_seed_reproduces_bit_identical_run(self):
        config = AccumulatorConfig(
            leak=0.08, sigma=0.06, threshold=1.0, n_trials=128
        )
        first = simulate_accumulator(config, seed=99)
        second = simulate_accumulator(config, seed=99)
        assert np.array_equal(first["history"], second["history"])
        assert np.array_equal(first["crossing"], second["crossing"])

    @pytest.mark.parametrize(
        "kwargs",
        [
            {"leak": -0.1, "sigma": 0.1, "threshold": 1.0},
            {"leak": 1.0, "sigma": 0.1, "threshold": 1.0},
            {"leak": 0.08, "sigma": -0.1, "threshold": 1.0},
            {"leak": 0.08, "sigma": 0.1, "threshold": 0.0},
            {"leak": 0.08, "sigma": 0.1, "threshold": 1.0, "drift": -0.01},
            {"leak": 0.08, "sigma": 0.1, "threshold": 1.0, "n_trials": 0},
            {"leak": 0.08, "sigma": 0.1, "threshold": 1.0, "t_max": 0},
        ],
    )
    def test_invalid_config_rejected(self, kwargs):
        with pytest.raises(ValueError):
            AccumulatorConfig(**kwargs)


class TestEvaluation:
    def test_row_shape_and_window_semantics(self):
        row = evaluate_seed(0)
        assert row["seed"] == 0
        for arm in ("null_arm", "drift_arm"):
            summary = row[arm]["aligned"]
            assert set(summary) == {
                "slope",
                "early_mean",
                "late_mean",
                "amplitude",
            }
            assert set(row[arm]["sham"]) == {"slope", "mean"}
            # La moyenne alignee converge vers le seuil a l'evenement (lag 0)
            # tandis que la moyenne sham reflete le regime stationnaire.
            assert row[arm]["aligned"]["late_mean"] > row[arm]["sham"]["mean"]
        assert set(row["gates"]) == set(GATE_NAMES)
        assert row["null_arm"]["n_analyzed"] + row["null_arm"][
            "n_short_excluded"
        ] + row["null_arm"]["n_uncrossed"] == row["null_arm"]["n_trials"]

    def test_arm_without_analyzable_trial_refuses_to_measure(self):
        # derive pure deterministe : franchissement a ceil(1/0.03) = 34 < 61
        with pytest.raises(ValueError):
            evaluate_seed(
                0,
                null_config=AccumulatorConfig(
                    leak=0.0, sigma=0.0, threshold=1.0, drift=0.03, n_trials=4
                ),
                drift_config=AccumulatorConfig(
                    leak=0.0, sigma=0.0, threshold=1.0, drift=0.03, n_trials=4
                ),
            )

    def test_evaluate_seed_is_deterministic(self):
        first = evaluate_seed(1)
        second = evaluate_seed(1)
        assert first == second


@pytest.fixture(scope="module")
def standard_study() -> dict:
    return run_preregistered_study()


class TestPreregisteredPredictions:
    def test_p1_selection_alone_produces_ramp(self, standard_study):
        assert (
            standard_study["pass_counts"]["P1_alignment_ramp_without_drift"]
            >= 4
        )

    def test_p2_sham_control_stays_flat(self, standard_study):
        assert standard_study["pass_counts"]["P2_sham_null_flat"] >= 4
        for row in standard_study["rows"]:
            assert abs(row["null_arm"]["sham"]["slope"]) <= 0.0010

    def test_p3_aligned_ramp_presence_remains_nondiscriminant(self, standard_study):
        assert (
            standard_study["pass_counts"]["P3_aligned_view_not_discriminant"]
            >= 4
        )
        for row in standard_study["rows"]:
            assert row["null_arm"]["aligned"]["slope"] >= 0.0030
            assert row["drift_arm"]["aligned"]["slope"] >= 0.0030

    def test_p4_sham_elevation_separates_drift(self, standard_study):
        assert (
            standard_study["pass_counts"]["P4_sham_elevation_separates"] >= 4
        )
        for row in standard_study["rows"]:
            assert row["sham_elevation_discriminant"] >= 0.060

    def test_p5_artifact_is_localized(self, standard_study):
        assert standard_study["pass_counts"]["P5_artifact_localized"] >= 4
        for row in standard_study["rows"]:
            null = row["null_arm"]
            assert null["aligned"]["amplitude"] >= 0.14
            assert (
                abs(null["aligned"]["early_mean"] - null["sham"]["mean"])
                <= 0.10
            )

    def test_seeds_are_the_preregistered_five(self, standard_study):
        assert standard_study["seeds"] == [0, 1, 7, 42, 99]

    def test_verdict_is_explicit(self, standard_study):
        assert standard_study["verdict"] in {
            "SUPPORTED",
            "INCONCLUSIVE",
            "FALSIFIED_MODEL",
        }

    def test_fewer_than_five_seeds_rejected(self):
        with pytest.raises(ValueError):
            run_preregistered_study(seeds=(0, 1, 7))


class TestVerdictDerivation:
    @staticmethod
    def _rows(**overrides: bool) -> list[dict]:
        base = {gate: True for gate in GATE_NAMES}
        base.update(overrides)
        return [dict(base) for _ in range(5)]

    def test_all_gates_supported(self):
        assert derive_verdict(self._rows()) == "SUPPORTED"

    def test_one_seed_out_of_five_still_supported(self):
        rows = self._rows()
        rows[0]["P4_sham_elevation_separates"] = False
        assert derive_verdict(rows) == "SUPPORTED"

    def test_two_seeds_failing_one_gate_is_not_supported(self):
        rows = self._rows()
        rows[0]["P4_sham_elevation_separates"] = False
        rows[1]["P4_sham_elevation_separates"] = False
        assert derive_verdict(rows) == "INCONCLUSIVE"

    def test_p1_failure_falsifies_model(self):
        assert (
            derive_verdict(
                self._rows(**{"P1_alignment_ramp_without_drift": False})
            )
            == "FALSIFIED_MODEL"
        )

    def test_p2_failure_falsifies_model(self):
        assert (
            derive_verdict(self._rows(**{"P2_sham_null_flat": False}))
            == "FALSIFIED_MODEL"
        )

    def test_p1_or_p2_failure_dominates_other_passes(self):
        rows = self._rows(**{"P2_sham_null_flat": False})
        # Meme si les autres gates passent, le controle null faux-positif
        # condamne le banc.
        assert derive_verdict(rows) == "FALSIFIED_MODEL"

    def test_too_few_rows_rejected(self):
        with pytest.raises(ValueError):
            derive_verdict([dict.fromkeys(GATE_NAMES, True)])


class TestCommittedResults:
    """Le JSON commit doit etre un artefact derive du meme protocole.

    Politique de comparaison : la structure discrete (cles de dict,
    longueurs et ordre des listes, chaines, booleens, entiers, gates,
    verdict) doit etre EXACTEMENT identique entre le JSON commit et une
    execution fraiche ; les flottants sont compares en tolerance croisee
    plateforme (pytest.approx rel=1e-12, abs=1e-15) car la generation
    (normal_draws) et les sommations NumPy peuvent differe de quelques
    ULP entre plateformes/builds. L'identite bit a bit n'est exigee que
    dans un meme environnement (cf. test_evaluate_seed_is_deterministic).
    """

    def test_results_file_exists_and_parses(self):
        assert RESULTS_PATH.exists()
        payload = json.loads(RESULTS_PATH.read_text(encoding="utf-8"))
        assert payload["seeds"] == [0, 1, 7, 42, 99]
        assert payload["reference"]["doi"] == "10.1073/pnas.1210467109"
        assert set(payload["pass_counts"]) == set(GATE_NAMES)
        assert payload["verdict"] in {
            "SUPPORTED",
            "INCONCLUSIVE",
            "FALSIFIED_MODEL",
        }
        assert len(payload["rows"]) == 5

    def test_committed_verdict_matches_derivation_from_its_rows(self):
        payload = json.loads(RESULTS_PATH.read_text(encoding="utf-8"))
        recomputed = derive_verdict(row["gates"] for row in payload["rows"])
        assert recomputed == payload["verdict"]

    @staticmethod
    def _assert_payload_matches(expected, actual, path: str = "$") -> None:
        """Comparaison recursive : discret exact, flottants en tolerance.

        ``bool`` est teste avant ``int``/``float`` car c'est une sous-classe
        d'``int`` en Python ; un flottant integral du JSON reste ``float``
        et un compteur reste ``int`` — un echange int<->float est un drift
        de schema, pas une difference d'ULP, et doit echouer.
        """

        if isinstance(expected, bool) or isinstance(actual, bool):
            assert isinstance(expected, bool) and isinstance(actual, bool), path
            assert expected == actual, path
        elif isinstance(expected, int) and isinstance(actual, int):
            assert expected == actual, path
        elif isinstance(expected, float) and isinstance(actual, float):
            assert actual == pytest.approx(
                expected, rel=1e-12, abs=1e-15
            ), path
        elif isinstance(expected, str) and isinstance(actual, str):
            assert expected == actual, path
        elif isinstance(expected, list) and isinstance(actual, list):
            assert len(expected) == len(actual), path
            for index, (item_expected, item_actual) in enumerate(
                zip(expected, actual)
            ):
                TestCommittedResults._assert_payload_matches(
                    item_expected, item_actual, f"{path}[{index}]"
                )
        elif isinstance(expected, dict) and isinstance(actual, dict):
            assert set(expected) == set(actual), path
            for key in expected:
                TestCommittedResults._assert_payload_matches(
                    expected[key], actual[key], f"{path}.{key}"
                )
        else:
            raise AssertionError(
                f"type mismatch at {path}: {type(expected)} vs {type(actual)}"
            )

    def test_committed_results_structure_exact_floats_within_tolerance(
        self, standard_study
    ):
        payload = json.loads(RESULTS_PATH.read_text(encoding="utf-8"))
        self._assert_payload_matches(payload, standard_study)
