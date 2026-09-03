"""Tests du protocole saillance-prégnance borné et pré-enregistré."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import numpy as np
import pytest

from ict.adjonction_saillance_pregnance import (
    CouplingConfig,
    couple_engagement,
    derive_operational_verdict,
    evaluate_seed,
    run_preregistered_study,
)

RESULTS_PATH = (
    Path(__file__).parents[1] / "results"
    / "adjonction_saillance_pregnance_results.json"
)


@pytest.fixture(scope="module")
def standard_study() -> dict:
    return run_preregistered_study()


def test_coupled_channel_uses_both_inputs() -> None:
    config = CouplingConfig()
    salience = np.array([-0.5, -0.5, 0.5, 0.5])
    pregnance = np.array([-0.5, 0.5, -0.5, 0.5])

    probabilities = couple_engagement(salience, pregnance, config=config)

    assert probabilities[0] != pytest.approx(probabilities[1])
    assert probabilities[0] != pytest.approx(probabilities[2])
    assert probabilities[3] > probabilities[1]
    assert probabilities[3] > probabilities[2]


def test_null_channels_ignore_the_absent_input() -> None:
    salience = np.array([-0.8, -0.1, 0.3, 0.9])
    pregnance_a = np.array([-0.9, 0.7, 0.2, -0.4])
    pregnance_b = pregnance_a[::-1]

    np.testing.assert_allclose(
        couple_engagement(salience, pregnance_a, mode="null_s"),
        couple_engagement(salience, pregnance_b, mode="null_s"),
    )
    np.testing.assert_allclose(
        couple_engagement(pregnance_a, salience, mode="null_pi"),
        couple_engagement(pregnance_b, salience, mode="null_pi"),
    )


def test_invalid_inputs_are_rejected() -> None:
    with pytest.raises(ValueError, match="n_stimuli"):
        CouplingConfig(n_stimuli=10)
    with pytest.raises(ValueError, match="alpha"):
        CouplingConfig(alpha=0.0)
    with pytest.raises(ValueError, match="même forme"):
        couple_engagement(np.ones(2), np.ones(3))
    with pytest.raises(ValueError, match="mode inconnu"):
        couple_engagement(np.ones(2), np.ones(2), mode="adjunction")


def test_seed_evaluation_is_deterministic() -> None:
    assert evaluate_seed(42) == evaluate_seed(42)


def test_seed_row_separates_testable_and_untestable_claims() -> None:
    row = evaluate_seed(0)

    assert set(row["partials"]) == {"coupled", "null_s", "null_pi"}
    assert row["P2_original_inhibition_debt"] == (
        "NOT_TESTABLE_ON_THIS_SUBSTRATE"
    )
    assert row["complexity"]["ratio"] == pytest.approx(2.0)
    assert row["complexity"]["asymptotic_order"] == "O(n_stimuli)"
    assert row["complexity"]["verdict"] == "SUPPORTED"
    assert set(row["gates"]) == {
        "P1_coupled_responds_to_both_channels",
        "P1_null_s_excludes_pi",
        "P1_null_pi_excludes_s",
        "P3_scalar_operation_ratio_at_most_two",
    }


def test_operational_verdict_branches() -> None:
    passing = {
        "P1_coupled_responds_to_both_channels": True,
        "P1_null_s_excludes_pi": True,
        "P1_null_pi_excludes_s": True,
        "P3_scalar_operation_ratio_at_most_two": True,
    }
    rows = [passing.copy() for _ in range(5)]
    assert derive_operational_verdict(rows) == "SUPPORTED_OPERATIONAL_CHANNEL"

    rows[0]["P3_scalar_operation_ratio_at_most_two"] = False
    rows[1]["P3_scalar_operation_ratio_at_most_two"] = False
    assert derive_operational_verdict(rows) == "SUPPORTED_OPERATIONAL_CHANNEL"

    rows[0]["P1_coupled_responds_to_both_channels"] = False
    rows[1]["P1_coupled_responds_to_both_channels"] = False
    assert derive_operational_verdict(rows) == "FALSIFIED_OPERATIONAL_CHANNEL"


def test_study_uses_fixed_seeds_and_honest_verdict_levels(
    standard_study: dict,
) -> None:
    assert standard_study["seeds"] == [0, 1, 7, 42, 99]
    assert standard_study["verdicts"]["original_specification"] == (
        "FALSIFIED_SPECIFICATION"
    )
    assert standard_study["verdicts"]["categorical_adjunction"] == (
        "NOT_ESTABLISHED"
    )
    assert standard_study["verdicts"]["P2_inhibition_debt"] == (
        "NOT_TESTABLE_ON_THIS_SUBSTRATE"
    )
    assert len(standard_study["rows"]) == 5
    assert all(0 <= count <= 5 for count in standard_study["pass_counts"].values())


def _assert_result_equal(actual: Any, expected: Any, path: str = "root") -> None:
    if isinstance(expected, dict):
        assert isinstance(actual, dict), path
        assert set(actual) == set(expected), path
        for key, value in expected.items():
            _assert_result_equal(actual[key], value, f"{path}.{key}")
    elif isinstance(expected, list):
        assert isinstance(actual, list), path
        assert len(actual) == len(expected), path
        for index, value in enumerate(expected):
            _assert_result_equal(actual[index], value, f"{path}[{index}]")
    elif isinstance(expected, bool):
        assert actual is expected, path
    elif isinstance(expected, int):
        assert actual == expected and isinstance(actual, int), path
    elif isinstance(expected, float):
        assert actual == pytest.approx(expected, rel=1e-12, abs=1e-15), path
    else:
        assert actual == expected, path


def test_committed_results_match_fresh_execution(standard_study: dict) -> None:
    expected = json.loads(RESULTS_PATH.read_text(encoding="utf-8"))
    _assert_result_equal(standard_study, expected)
