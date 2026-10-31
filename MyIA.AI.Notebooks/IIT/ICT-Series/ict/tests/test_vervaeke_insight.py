"""Tests de vervaeke_insight -- pre-enregistrement docs/ict/vervaeke-insight-pre-enregistrement.md."""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from ict import vervaeke_insight as v  # noqa: E402


# -- terrain ----------------------------------------------------------------
def test_terrain_deterministe():
    assert np.array_equal(v.terrain(7), v.terrain(7))


def test_terrain_exactement_k_pertinents():
    g = v.terrain(3)
    assert g.sum(axis=1).min() == v.K_COMMIT and g.sum(axis=1).max() == v.K_COMMIT


def test_terrain_bascule_change_l_ensemble():
    g = v.terrain(11)
    overlap = int((g[v.SHIFTS[0] - 1] & g[v.SHIFTS[0]]).sum())
    assert overlap == v.K_COMMIT - v.REPLACED_AT_SHIFT


def test_terrain_stationaire_constant():
    g = v.terrain(11, stationary=True)
    assert all(np.array_equal(g[0], g[t]) for t in range(v.N_STEPS))


def test_terrain_forme():
    g = v.terrain(0)
    assert g.shape == (v.N_STEPS, v.N_CUES) and g.dtype == bool


# -- execution --------------------------------------------------------------
def test_run_deterministe_par_bras():
    a, b = v.run(42, "opponent"), v.run(42, "opponent")
    assert a["grip"] == b["grip"] and a["switches"] == b["switches"]
    assert a["grip_series"] == b["grip_series"]


def test_grip_est_la_moyenne_des_derniers_pas():
    r = v.run(1, "opponent")
    assert r["grip"] == pytest.approx(float(np.mean(r["grip_series"][-v.GRIP_WINDOW:])))


def test_grip_dans_unite():
    for arm in ("opponent", "static"):
        assert 0.0 <= v.run(5, arm)["grip"] <= 1.0


def test_switches_croissants_et_distingues_des_set_changes():
    r = v.run(9, "opponent")
    assert r["switches"] == sorted(r["switches"])
    # deux evenements distincts : aucun n'est un multiple trivial de l autre
    assert r["switch_count"] != r["set_changes"] * 240


def test_static_explore_environ_vingt_pourcent():
    shares = [v.run(s, "static")["explore_steps"] / v.N_STEPS for s in (0, 1, 7)]
    assert all(0.10 <= sh <= 0.30 for sh in shares)


def test_sham_apparie_en_budget():
    for s in (0, 1):
        opp, sham = v.run(s, "opponent"), v.run_matched_sham(s)
        assert abs(sham["explore_steps"] - opp["explore_steps"]) <= 6


def test_opponent_stationnaire_explore_moins_que_statique():
    so = v.run(2, "opponent", stationary=True)["explore_steps"]
    sb = v.run(2, "static", stationary=True)["explore_steps"]
    assert so < sb


# -- metriques --------------------------------------------------------------
def _fake_res(switches, stationary=False):
    series = np.linspace(0, 1, v.N_STEPS)
    return {"stationary": stationary, "switches": switches,
            "grip_series": series.tolist()}


def test_concentration_sans_bascule_nulle():
    assert v.concentration(_fake_res([], stationary=True)) == 0.0


def test_concentration_elevee_si_agrege():
    conc = v.concentration(_fake_res([s + 1 for s in v.SHIFTS]))
    assert conc >= 2.0


def test_concentration_faible_si_disperse():
    switches = [t for t in range(30, v.N_STEPS, 20)
                if not any(0 <= t - sh < v.SWITCH_FOCUS for sh in v.SHIFTS)]
    assert v.concentration(_fake_res(switches)) < 1.0


def test_switch_rate_apres_contre_hors():
    r = dict(_fake_res([]), switches=[s + 1 for s in v.SHIFTS])
    rates = v.switch_rate_after_shifts(r)
    assert rates["after"] > rates["outside"]


def test_impasse_profile_compte_le_plat():
    series = np.array([0.5] * 10 + [0.9] * (v.N_STEPS - 10))
    prof = v.impasse_profile(series, [12])
    assert prof[0]["t"] == 12 and prof[0]["flat"] >= 2 and prof[0]["gain"] > 0


def test_impasse_share_requiert_flat_three():
    res = {"impasse": [{"t": 1, "flat": 5, "gain": 0.1},
                       {"t": 2, "flat": 1, "gain": 0.1}]}
    assert v.impasse_share(res) == pytest.approx(0.5)


# -- verdict ----------------------------------------------------------------
def _seed_row(d1=0.2, d2=0.2, conc=3.0, ratio=4.0, imp=0.8, expl=0.05):
    return {"grip": {"opponent": 0.8, "static": 0.8 - d1, "sham_rate": 0.8 - d2},
            "grip_stationary": {"opponent": 0.9, "static": 0.9},
            "concentration": conc, "rate_ratio": ratio, "impasse_ok": imp,
            "explore_share_stationary": expl, "switch_count": 10}


def test_verdict_supported():
    per = {str(s): _seed_row() for s in v.STUDY_SEEDS}
    assert v.verdict(per)["verdict"] == "SUPPORTED"


def test_verdict_refute_si_p1_tombe_sur_une_graine():
    per = {str(s): _seed_row() for s in v.STUDY_SEEDS}
    per["42"] = _seed_row(d1=0.01)
    out = v.verdict(per)
    assert out["P1"] is False and out["verdict"] == "REFUTED"


def test_verdict_partial_deux_des_trois():
    per = {str(s): _seed_row() for s in v.STUDY_SEEDS}
    for s in per.values():
        s["concentration"] = 1.0  # P3 tombe ; P4 et P5 tiennent
    out = v.verdict(per)
    assert out["P3"] is False and out["verdict"] == "PARTIAL"


def test_verdict_refute_si_p2_tombe():
    per = {str(s): _seed_row() for s in v.STUDY_SEEDS}
    per["7"] = _seed_row(d2=0.0)
    assert v.verdict(per)["verdict"] == "REFUTED"


def test_verdict_p5_bande_moitie():
    per = {str(s): _seed_row() for s in v.STUDY_SEEDS}
    per["99"] = _seed_row(expl=0.15)
    assert v.verdict(per)["P5"] is False


# -- estimation -------------------------------------------------------------
def test_estimation_neutre_sans_observation():
    t = v.ValueTable()
    assert t.est(3) == pytest.approx(0.5)


def test_estimation_converge_vers_succes_constant():
    t = v.ValueTable()
    for _ in range(200):
        t.observe([3], [1.0])
    assert t.est(3) > 0.85


def test_marges_meilleur_non_choisi_moins_pire_choisi():
    t = v.ValueTable()
    for _ in range(60):
        t.observe([0], [1.0])
        t.observe([5], [0.0])
    margin, out_c, in_c = t.margins(np.array([0, 2, 3, 4, 5, 6]))
    assert out_c == 5 and in_c in (1, 2, 3, 4, 6)
    assert margin == pytest.approx(t.est(in_c) - t.est(5), abs=1e-9)


def test_explore_propose_k_indices_distincts():
    a = v.Agent(seed=1, arm="opponent")
    p = a._explore_step()
    assert len(p) == v.K_COMMIT and len(set(p.tolist())) == v.K_COMMIT


def test_exploit_change_au_plus_un_indice():
    a = v.Agent(seed=1, arm="opponent")
    before = a.chosen.copy()
    for _ in range(20):
        a.table.observe(a.chosen.tolist(), (a.rng.random(6) > 0.5).tolist())
    after = a._exploit_step()
    assert len(set(before.tolist()) - set(after.tolist())) <= 1


# -- evaluation end-to-end et sortie ----------------------------------------
def test_evaluate_structure():
    out = v.evaluate(seeds=(0,))
    assert set(out["per_seed"]["0"]["grip"]) == {"opponent", "static", "sham_rate"}
    assert set(out["predictions"]) >= {"P1", "P2", "P3", "P4", "P5", "verdict"}


def test_main_ecrit_le_json(tmp_path):
    out_file = tmp_path / "res.json"
    v.main(seeds=(0,), out=str(out_file))
    data = json.loads(out_file.read_text(encoding="utf-8"))
    assert data["predictions"]["verdict"] in ("SUPPORTED", "PARTIAL", "REFUTED")


def test_resultats_committees_reproductibles():
    ref = Path(__file__).parent.parent / "results" / "vervaeke_insight_results.json"
    if not ref.exists():
        pytest.skip("resultats non encore commits")
    data = json.loads(ref.read_text(encoding="utf-8"))
    fresh = v.evaluate()
    assert data["predictions"]["verdict"] == fresh["predictions"]["verdict"]
    for s, row in fresh["per_seed"].items():
        assert row["grip"]["opponent"] == pytest.approx(data["per_seed"][s]["grip"]["opponent"])
