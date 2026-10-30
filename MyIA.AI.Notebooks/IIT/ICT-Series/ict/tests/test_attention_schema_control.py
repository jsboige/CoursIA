"""Tests du module case 5ter (#8182) — executant du pre-enregistrement scelle.

Couvre : primitives circulaires, determinisme/gelement du terrain, regles des
bras (annonce initiale, quantification, permutation, distorsion), metriques
(correction connue, calmues, adaptation), predications/bandes P1a..P5 et la
regle de verdict sur fixtures manufacturees, determinisme run_seed.
"""
import json
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from ict import attention_schema_control as asc  # noqa: E402


# --- Primitives circulaires -------------------------------------------------

def test_circ_wrap_borne_0_1():
    assert asc.circ_wrap(-0.25) == pytest.approx(0.75)
    assert asc.circ_wrap(1.3) == pytest.approx(0.3)
    assert asc.circ_wrap(0.5) == pytest.approx(0.5)


def test_circ_delta_pliee():
    assert float(asc.circ_delta(0.9, 0.1)) == pytest.approx(-0.2)
    assert float(asc.circ_delta(0.1, 0.9)) == pytest.approx(0.2)
    assert float(asc.circ_delta(0.3, 0.3)) == pytest.approx(0.0)
    d = asc.circ_delta(np.array([0.0, 0.6]), np.array([0.9, 0.0]))
    assert np.all(np.abs(d) <= 0.5)


# --- Terrain : determinisme et gel -------------------------------------------

def test_terrain_deterministe():
    a = asc.build_terrain(7)
    b = asc.build_terrain(7)
    for f in ("positions", "velocities", "salience_true", "salience_obs"):
        assert np.array_equal(getattr(a, f), getattr(b, f))
    assert a.target_idx == b.target_idx


def test_terrain_formes_et_saillances():
    t = asc.build_terrain(0)
    assert t.positions.shape == (asc.STEPS, asc.N_ITEMS)
    assert t.salience_obs.shape == (asc.STEPS, asc.N_ITEMS)
    assert t.salience_true[t.target_idx] == asc.SALIENCE_TARGET
    autres = np.delete(t.salience_true, t.target_idx)
    assert np.all((autres >= asc.SALIENCE_DISTRACTORS[0] - 1e-9)
                  & (autres <= asc.SALIENCE_DISTRACTORS[1] + 1e-9))
    assert set(t.jumps) == set(asc.JUMP_TIMES)
    assert all(s in (-1, 1) for s in t.jumps.values())
    assert set(t.distractor_events) == set(asc.DISTRACTOR_TIMES)
    assert all(i != t.target_idx for i in t.distractor_events.values())


def test_terrain_positions_dans_0_1():
    t = asc.build_terrain(42)
    assert np.all(t.positions >= 0.0) and np.all(t.positions < 1.0)


# --- Bras --------------------------------------------------------------------

def test_reactive_annonce_initiale_vise_la_cible():
    t = asc.build_terrain(1)
    r = asc.run_reactive(t)
    # annonce (choix a2) : saillance vraie chargee, la cible (1.0) domine
    assert r.focus[0] == pytest.approx(t.positions[0, t.target_idx])
    assert r.error[0] == pytest.approx(0.0)


def test_schema_quantifie_et_initialise():
    t = asc.build_terrain(1)
    r = asc.run_schema(t, 1)
    assert r.arm == "schema"
    # grille 0.01 : le foyer stocke est multiple de GRID (a epsilon pres)
    assert np.allclose(r.focus / asc.GRID, np.round(r.focus / asc.GRID), atol=1e-9)
    assert r.error[0] < asc.GRID  # annonce initiale sur la cible
    for key in ("erreur_pred", "baseline_persistance", "baseline_ema_vitesse", "erreur_rapport"):
        assert key in r.metrics


def test_shuffled_nomme_et_distordu_rapport():
    t = asc.build_terrain(7)
    r = asc.run_schema(t, 7, shuffled=True)
    assert r.arm == "schema_shuffled"
    d = asc.FOCUS_WIDTH / 4.0
    rd = asc.run_schema(t, 7, distorted_d=d)
    assert rd.arm == "schema_distorted"
    # stockage = pos_s + d : l'ecart de rapport est de l'ordre de d (P3a mecanique)
    assert rd.metrics["erreur_rapport"] >= 0.8 * d


def test_schema_distortion_croissante():
    t = asc.build_terrain(7)
    r0 = asc.run_schema(t, 7, distorted_d=0.0)
    r1 = asc.run_schema(t, 7, distorted_d=asc.FOCUS_WIDTH / 4.0)
    r2 = asc.run_schema(t, 7, distorted_d=asc.FOCUS_WIDTH / 2.0)
    assert r0.metrics["erreur_rapport"] < r1.metrics["erreur_rapport"] < r2.metrics["erreur_rapport"]


def _terrain_lisse():
    """Terrain synthetique : cible a vitesse constante, saillance propre.

    Le filtre alpha-beta du schema doit y battre la persistance (garantie
    mecanique du modele 1-pas a vitesse convergee) ; sur le terrain scelle
    bruite, la question est pour le pilote, pas pour ce test.
    """
    n = asc.N_ITEMS
    pos = np.zeros((asc.STEPS, n))
    vel = np.zeros((asc.STEPS, n))
    vel[:, 0] = 0.01
    pos[0] = np.linspace(0.0, 1.0, n, endpoint=False)
    for t in range(1, asc.STEPS):
        pos[t] = asc.circ_wrap(pos[t - 1] + vel[t])
    sal = np.full(n, 0.5)
    sal[0] = asc.SALIENCE_TARGET
    return asc.Terrain(seed=0, positions=pos, velocities=vel, salience_true=sal,
                       salience_obs=np.repeat(sal[None, :], asc.STEPS, axis=0),
                       target_idx=0, jumps={}, distractor_events={})


def test_schema_prediction_bat_persistance_sur_flux_lisse():
    t = _terrain_lisse()
    r = asc.run_schema(t, 3)
    # la persistance (0,01 = le pas de vitesse) est battue ; sur flux sans
    # bruit la baseline EMA-vitesse est un oracle numeriquement parfait, la
    # comparer au schema regarde la bande P2 du terrain reel, pas ce test
    assert r.metrics["erreur_pred"] <= r.metrics["baseline_persistance"]


# --- Metriques ----------------------------------------------------------------

def test_correction_cas_connus():
    e_ok = np.full(asc.STEPS, 0.01)
    assert asc.correction_steps(e_ok, 150) == 0
    e_never = np.full(asc.STEPS, 0.5)
    assert asc.correction_steps(e_never, 150) == asc.CORRECTION_CENSOR
    e_late = np.full(asc.STEPS, 0.5)
    e_late[155:160] = 0.01                      # converve seulement a k=5
    assert asc.correction_steps(e_late, 150) == 5


def test_calm_mask_exclut_les_fenetres():
    m = asc.calm_mask()
    for t0 in (150, 390, 630, 210, 450, 690, 90, 330, 570):
        assert not m[t0] and not m[t0 - 5]
        if t0 + 70 < asc.STEPS:
            assert not m[t0 + 70]
    attendu = np.ones(asc.STEPS, dtype=bool)
    for t0 in (150, 390, 630, 210, 450, 690, 90, 330, 570):
        attendu[max(0, t0 - 10):t0 + 81] = False
    assert np.array_equal(m, attendu)
    assert m.sum() == attendu.sum()


def test_arm_metrics_cles_du_document():
    t = asc.build_terrain(0)
    mm = asc.arm_metrics(asc.run_reactive(t))
    for key in ("stabilite", "correction", "adaptation", "correction_par_perturbation"):
        assert key in mm
    assert len(mm["correction_par_perturbation"]) == 9


def test_run_seed_deterministe_et_json():
    a = asc.run_seed(0)
    b = asc.run_seed(0)
    assert json.dumps(a) == json.dumps(b)
    assert set(a["arms"]) == {"reactive", "schema", "schema_shuffled",
                              "schema_distorted_d0.025", "schema_distorted_d0.050"}


# --- Predictions et verdict (fixtures manufacturees) ---------------------------

def _seed_result(schema_stab=0.02, schema_corr=20.0, schema_adapt=0.8,
                 react_stab=0.05, react_corr=50.0, react_adapt=1.0,
                 shuf_stab=None, shuf_corr=None,
                 ep=0.001, base_p=0.01, base_v=0.01,
                 rap=lambda d: d):
    shuf_stab = react_stab * 1.2 if shuf_stab is None else shuf_stab
    shuf_corr = react_corr * 1.2 if shuf_corr is None else shuf_corr

    def arms():
        d025 = asc.FOCUS_WIDTH / 4.0
        d050 = asc.FOCUS_WIDTH / 2.0
        return {
            "reactive": {"stabilite": react_stab, "correction": react_corr, "adaptation": react_adapt},
            "schema": {"stabilite": schema_stab, "correction": schema_corr, "adaptation": schema_adapt,
                       "erreur_pred": ep, "baseline_persistance": base_p, "baseline_ema_vitesse": base_v},
            "schema_shuffled": {"stabilite": shuf_stab, "correction": shuf_corr},
            "schema_distorted_d0.025": {"stabilite": schema_stab + 0.001, "correction": schema_corr + 5,
                                        "erreur_rapport": rap(d025)},
            "schema_distorted_d0.050": {"stabilite": schema_stab + 0.004, "correction": schema_corr + 20,
                                        "erreur_rapport": rap(d050)},
        }

    return {"seed": 0, "arms": arms()}


def _pred(**kw):
    return asc.evaluate_predictions([_seed_result(**kw) for _ in range(5)])


def test_verdict_supported():
    p = _pred()
    assert all(p[k] for k in ("P1a", "P1b", "P1c", "P2", "P3a", "P3b", "P4"))
    assert not p["P5"]
    assert asc.verdict(p) == "SUPPORTED"


def test_verdict_partial_quand_p1c_tombe():
    p = _pred(schema_adapt=1.0)   # 1.0 <= 0.9*1.0 faux sur les 5 graines
    assert not p["P1c"]
    assert p["P1a"] and p["P1b"] and p["P4"] and p["P2"]
    assert asc.verdict(p) == "PARTIAL"


def test_verdict_partial_par_p3():
    # P2 tombe (erreur_pred == baseline), P3a/P3b passent
    p = _pred(ep=0.05)
    assert not p["P2"]
    assert p["P3a"] and p["P3b"]
    assert asc.verdict(p) == "PARTIAL"


def test_verdict_refute_quand_p1a_tombe():
    p = _pred(schema_stab=0.05)   # == reactive, jamais <= 0.8*reactive
    assert not p["P1a"]
    assert asc.verdict(p) == "REFUTED"


def test_porte_p5_terrain_trop_facile():
    p = _pred(react_stab=0.02, react_corr=8.0, schema_stab=0.01, schema_corr=5.0,
              shuf_stab=0.025, shuf_corr=9.0)
    assert p["P5"]
    assert asc.verdict(p) == "NON_CONCLUSIF_INSTRUMENT"


def test_p3b_tombe_quand_le_controle_derape():
    fixture = []
    for _ in range(5):
        r = _seed_result(schema_corr=10.0)
        r["arms"]["schema_distorted_d0.025"]["correction"] = 45.0   # +35 pas > +12
        r["arms"]["schema_distorted_d0.025"]["stabilite"] = 0.05    # +0.03 > 0.02
        fixture.append(r)
    p = asc.evaluate_predictions(fixture)
    assert not p["P3b"]


def test_p4_tombe_si_shuffled_ameliore():
    fixture = []
    for _ in range(5):
        r = _seed_result()
        r["arms"]["schema_shuffled"] = {"stabilite": 0.03, "correction": 30.0}
        fixture.append(r)
    p = asc.evaluate_predictions(fixture)
    assert not p["P4"]


def test_p3a_tombe_si_le_rapport_ne_suit_pas_d():
    fixture = []
    for _ in range(5):
        r = _seed_result(rap=lambda d: 0.0)
        fixture.append(r)
    p = asc.evaluate_predictions(fixture)
    assert not p["P3a"]


def test_bande_4_sur_5():
    # une graine hors bande sur cinq reste dans la bande
    fixture = [_seed_result() for _ in range(4)] + [_seed_result(schema_stab=0.05)]
    p = asc.evaluate_predictions(fixture)
    assert p["P1a"]
    # deux hors bande -> 3/5 < 4 -> tombee
    fixture2 = [_seed_result() for _ in range(3)] + [_seed_result(schema_stab=0.05) for _ in range(2)]
    p2 = asc.evaluate_predictions(fixture2)
    assert not p2["P1a"]
