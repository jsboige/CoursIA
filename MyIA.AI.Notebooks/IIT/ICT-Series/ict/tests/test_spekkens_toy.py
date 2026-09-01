"""Tests case 10 (#8182) — toy bit Spekkens : restriction ⟂ contextualité.

Pré-enregistrement scellé au commit ``82e187e5f``. Les tests pincent les
quantités exactes du pré-enregistrement : 6 états purs, perturbation 1/2,
borne CHSH atteinte (et non dépassée), contraste QM 2√2, clonage 1/3.
"""

from __future__ import annotations

import math

from ict.spekkens_toy import (
    MEASUREMENTS,
    PURE_STATES,
    chsh_exhaustive,
    clairvoyant_control,
    measure,
    no_cloning_fixed_basis,
    qm_reference,
    sequence_mc,
    sequence_prob_exact,
)


def test_six_pure_states():
    assert len(PURE_STATES) == 6
    assert all(len(s) == 2 for s in PURE_STATES)


def test_compatible_measurement_no_disturbance():
    outcome, posterior = measure(frozenset({1, 2}), "X")
    assert outcome == "+"
    assert posterior == frozenset({1, 2})


def test_p1a_no_disturbance():
    assert sequence_prob_exact(None) == 1.0


def test_p1b_disturbance_exact_half():
    assert sequence_prob_exact("Y") == 0.5
    assert sequence_prob_exact("Z") == 0.5


def test_p1b_monte_carlo_within_band():
    for m in ("Y", "Z"):
        for seed in (0, 1, 7, 42, 99):
            assert 0.48 <= sequence_mc(m, seed) <= 0.52


def test_p1c_clairvoyant():
    assert clairvoyant_control() == 1.0


def test_p2_chsh_bound_reached_not_exceeded():
    res = chsh_exhaustive()
    assert res["n_states"] == 1820
    assert res["n_combos"] == 9
    assert 1.99 <= res["max_S"] <= 2.01


def test_p2_qm_tsirelson():
    res = qm_reference()
    assert abs(res["S_qm"] - math.sqrt(8.0)) < 1e-9


def test_s1_no_cloning_third():
    res = no_cloning_fixed_basis()
    assert abs(res["best_fidelity"] - 1 / 3) < 1e-12
    assert res["clairvoyant_fidelity"] == 1.0


def test_measurements_are_pair_partitions():
    for plus, minus in MEASUREMENTS.values():
        assert len(plus) == len(minus) == 2
        assert not (plus & minus)
