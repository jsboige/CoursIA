"""Tests du jouet « conscience relativiste » (case 23, #8182 — Lahav).

Contrôles mécaniques (disjointness des codebooks appris séparément, fidélité
du dispatch complet à la table de l'éq 46, déterminisme par graine),
contrôles d'estimation (reconnaissance propre vs étrangère, canal physique
au-dessus du hasard), et lecture du verdict sur mesures synthétiques — y
compris les sorties NON_CONCLUSIF (instrument, null b) et REFUTED.
"""

import json
from pathlib import Path

import numpy as np
import pytest

from ict import lahav_relativistic as lr


@pytest.fixture(scope="module")
def world():
    return lr.build_world(0)


def test_bands_match_sealed_doc():
    # Scellé §4 — garde contre la dérive des bandes entre doc et module.
    assert lr.BANDS["p1_own_min"] == 0.95
    assert lr.BANDS["p2_foreign_max"] == 0.05
    assert lr.BANDS["p3_channel_min"] == 0.75
    assert lr.BANDS["p3_three_x_chance"] == pytest.approx(0.375)
    assert lr.BANDS["null_a_lo"] == 0.70 and lr.BANDS["null_a_hi"] == 0.98
    assert lr.BANDS["door_margin_min"] == 0.80


def test_separate_learning_makes_disjoint_states(world):
    # « Alice and Bob have no states in common » : codebooks croisés sous tau.
    _, alice, bob, _ = world
    cross_pc = max(
        float(np.abs(alice.percepts @ bob.percepts.T).max()),
        float(np.abs(alice.judgments @ bob.judgments.T).max()),
        float(np.abs(alice.percepts @ bob.judgments.T).max()),
    )
    assert cross_pc < lr.TAU
    # Le monde, lui, est partagé : mêmes propriétés physiques pour les deux systèmes.
    # (alice et bob voient les mêmes entrées mais les encodent différemment)


def test_replica_shares_states_but_not_position(world):
    # Symétrie brisée (éqs 49-50) : ALICE a les MÊMES états qu'Alice, autre position.
    _, alice, _, replica = world
    np.testing.assert_allclose(replica.judgments, alice.judgments)
    assert replica.position != alice.position


def test_own_recognition_high_and_foreign_empty(world):
    _, alice, bob, _ = world
    rng = np.random.default_rng(1)
    own, own_cos = lr.measure_own(alice, rng)
    fp, cross = lr.measure_foreign(alice, bob, rng)
    assert own >= lr.BANDS["p1_own_min"]
    assert own_cos >= lr.TAU
    assert fp <= lr.BANDS["p2_foreign_max"]
    assert cross < lr.TAU


def test_channel_above_chance_and_noise_monotone(world):
    _, alice, _, _ = world
    acc_low = lr.channel_accuracy(alice.judgments, 0.05, np.random.default_rng(2))
    acc_high = lr.channel_accuracy(alice.judgments, 0.30, np.random.default_rng(2))
    assert acc_low > 1.0 / lr.K_INPUTS
    assert acc_high <= acc_low  # plus de bruit, pas plus de précision


def test_dispatch_full_matches_expected_table(world):
    props, alice, bob, replica = world
    rows = lr.dispatch_table(alice, replica, bob, props, np.random.default_rng(3))
    assert set(rows) == {"/".join(k) for k in lr.EXPECTED_DISPATCH}
    for key, row in rows.items():
        expected = lr.EXPECTED_DISPATCH[tuple(key.split("/"))]
        assert row["full"] == expected, key


def test_membership_only_misroutes_own_broken_symmetry(world):
    # Null (b) : sans delta_r, le propre quale en symétrie brisée passe pour direct.
    props, alice, bob, replica = world
    rows = lr.dispatch_table(alice, replica, bob, props, np.random.default_rng(4))
    assert rows["own_quale/diff_pos"]["full"] == "S"
    assert rows["own_quale/diff_pos"]["membership_only"] == "DIRECT"
    assert rows["own_quale/diff_pos"]["eq51"] == "S"  # eq51 voit la position, pas l'appartenance


def test_eq51_misroutes_cocolocated_third_and_other(world):
    # Approximation éq 51 : comportementalement correct, aveugle à l'identité de cadre.
    props, alice, bob, replica = world
    rows = lr.dispatch_table(alice, replica, bob, props, np.random.default_rng(5))
    for key in ("third_input/same_pos", "other_quale/same_pos"):
        assert rows[key]["full"] == "S"
        assert rows[key]["eq51"] == "DIRECT"


def test_run_seed_deterministic():
    a = lr.run_seed(7, sigma_t=0.30)
    b = lr.run_seed(7, sigma_t=0.30)
    assert a["r_direct_own"] == b["r_direct_own"]
    assert a["acc_indirect"] == b["acc_indirect"]


def _synth_calib(ok=True, selected=0.30):
    return {
        "grid_scan": {"0.3": {"accs": [0.9, 0.9, 0.9], "mean": 0.9}},
        "sigma_t_selected": selected,
        "own_rates": [1.0] * 6,
        "foreign_rates": [0.0] * 3,
        "margin_direct_tiers": 1.0,
        "null_a_ok": ok,
        "door_ok": True,
    }


def test_verdict_supported():
    calib = _synth_calib()
    runs = [
        {"r_direct_own": 1.0, "r_direct_foreign": 0.0, "acc_indirect": 0.9,
         "membership_misroutes_own_broken": True}
    ] * 5
    v = lr.verdict(calib, runs)
    assert v["verdict"] == "SUPPORTED"
    assert all(v["checks"].values())


def test_verdict_instrument_when_calibration_fails():
    calib = _synth_calib(selected=None)
    v = lr.verdict(calib, [])
    assert "NON_CONCLUSIF_INSTRUMENT" in v["verdict"]
    assert "calibration" in v["verdict"]


def test_verdict_null_b_when_delta_r_does_no_work():
    calib = _synth_calib()
    runs = [
        {"r_direct_own": 1.0, "r_direct_foreign": 0.0, "acc_indirect": 0.9,
         "membership_misroutes_own_broken": False}
    ] * 5
    v = lr.verdict(calib, runs)
    assert v["verdict"].startswith("NON_CONCLUSIF (null b")


def test_verdict_refuted_when_channel_below_chance():
    calib = _synth_calib()
    runs = [
        {"r_direct_own": 1.0, "r_direct_foreign": 0.0, "acc_indirect": 0.15,
         "membership_misroutes_own_broken": True}
    ] * 5
    v = lr.verdict(calib, runs)
    assert v["verdict"].startswith("REFUTED (P3")


def test_verdict_refuted_when_foreign_channel_open():
    calib = _synth_calib()
    runs = [
        {"r_direct_own": 1.0, "r_direct_foreign": 0.8, "acc_indirect": 0.9,
         "membership_misroutes_own_broken": True}
    ] * 5
    v = lr.verdict(calib, runs)
    assert v["verdict"].startswith("REFUTED (P2")


def test_results_file_matches_sealed_verdict():
    # Le JSON livré existe et porte le verdict SUPPORTED mesuré au run principal.
    path = Path(__file__).resolve().parents[1] / "results" / "lahav_relativistic_results.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    assert data["frozen"]["seeds"] == list(lr.TEST_SEEDS)
    assert data["frozen"]["sigma_t"] in lr.SIGMA_T_GRID
    assert data["verdict"]["verdict"] == "SUPPORTED"
    for run in data["runs"]:
        assert run["full_dispatch_fidelity"] is True
        assert run["membership_misroutes"] == ["own_quale/diff_pos"]
