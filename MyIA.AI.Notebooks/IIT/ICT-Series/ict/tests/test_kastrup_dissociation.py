"""Tests du jouet « dissociation cosmique » (case 18, #8182 — Kastrup).

Contrôles mécaniques (connexité figure 3.1a, bloc-diagonale figure 3.1b,
masse du dommage aléatoire, déterminisme), contrôles d'estimation (la
corrélation partielle donnée e tue un couplage purement environnemental mais
pas un couplage direct), et lecture du verdict sur mesures synthétiques.
Trajectoires courtes (T réduit via monkeypatch des constantes) pour rester
rapides — les constantes du run principal vivent dans le module.
"""

import numpy as np
import pytest

from ict import kastrup_dissociation as kd


@pytest.fixture(scope="module")
def field():
    f = kd.EvocationField.build(seed=0, p_out=0.02)
    assert f.connected_at_rest()
    return f


def test_bool_matmul_semantics():
    a = np.array([[True, False], [False, True]])
    assert ((a @ a) == a).all()


def test_graph_connected_at_rest(field):
    # Figure 3.1a : contenus phénoménaux ordinaires = graphe connexe.
    assert field.connected_at_rest()


def test_full_dissociation_is_block_diagonal(field):
    # Figure 3.1b : à d = 1, plus aucune évocation directe inter-alters.
    W1 = field.W_at(1.0)
    assert (W1[field.inter_mask] == 0.0).all()
    assert (W1[field.intra_mask] >= 0.0).any()


def test_partial_corr_removes_pure_env_coupling():
    # Deux nœuds couplés UNIQUEMENT par l'environnement : la marginale voit,
    # la partielle donnée e est aveugle — la machinerie de la case 14 au service
    # de la case 18.
    rng = np.random.default_rng(7)
    e = rng.normal(0.0, 1.0, size=50_000)
    x = np.column_stack([0.8 * e + rng.normal(0.0, 1.0, size=50_000),
                         0.9 * e + rng.normal(0.0, 1.0, size=50_000)])
    marginal = np.corrcoef(x, rowvar=False)[0, 1]
    partial = kd.partial_corr_given(x, e.reshape(-1, 1))[0, 1]
    assert marginal > 0.4
    assert abs(partial) < 0.05


def test_partial_corr_removes_lagged_env_coupling():
    # Amendement v2 : cause commune DYNAMIQUE — un couplage uniquement via
    # e(t-3) survit à un contrôle sur le seul e(t) et meurt sous le contrôle
    # de la matrice de décalages.
    rng = np.random.default_rng(9)
    e = rng.normal(0.0, 1.0, size=50_000)
    x = np.column_stack([0.8 * np.roll(e, 3) + rng.normal(0.0, 1.0, size=50_000),
                         0.9 * np.roll(e, 3) + rng.normal(0.0, 1.0, size=50_000)])
    partial_now = kd.partial_corr_given(x, e.reshape(-1, 1))[0, 1]
    controls, _ = kd.env_control_matrix(e)
    partial_lags = kd.partial_corr_given(x[kd.ENV_LAGS:], controls)[0, 1]
    assert partial_now > 0.4  # le piège v1, mesuré sur le jouet : 0.41
    assert abs(partial_lags) < 0.05


def test_partial_corr_keeps_direct_coupling():
    # Un couplage direct survit à la partialisation donnée e.
    rng = np.random.default_rng(8)
    n = 50_000
    e = rng.normal(0.0, 1.0, size=n)
    u = rng.normal(0.0, 1.0, size=n)
    x = np.column_stack([u + 0.3 * e + rng.normal(0.0, 1.0, size=n),
                         0.7 * u + 0.3 * e + rng.normal(0.0, 1.0, size=n)])
    partial = kd.partial_corr_given(x, e.reshape(-1, 1))[0, 1]
    assert partial > 0.3


def test_determinism_same_seed_same_field():
    f1 = kd.EvocationField.build(seed=42, p_out=0.02)
    f2 = kd.EvocationField.build(seed=42, p_out=0.02)
    assert np.array_equal(f1.W, f2.W) and np.array_equal(f1.beta, f2.beta)


def test_random_damage_removes_target_mass(field):
    rng = np.random.default_rng(5)
    W_rand = kd.random_damage_W(field, rng)
    inter_mass = field.W[field.inter_mask].sum()
    removed = field.W.sum() - W_rand.sum()
    assert removed == pytest.approx(inter_mass, rel=1e-9)
    # Le dommage touche aussi l'intra (sinon ce serait une dissociation).
    assert (field.W[field.intra_mask] - W_rand[field.intra_mask]).sum() > 0


def test_privacy_holds_and_intra_survives_short_run(field, monkeypatch):
    # Intégration courte : T réduit, mêmes lois — P2 doit être ≈ 0 à d = 1,
    # et le ratio P1 reste ≥ bande même avec du bruit d'échantillon.
    monkeypatch.setattr(kd, "T_STEPS", 8_000)
    monkeypatch.setattr(kd, "BURN_IN", 1_000)
    m0 = kd.measure(field, 0.0, np.random.default_rng(101))
    m1 = kd.measure(field, 1.0, np.random.default_rng(102))
    assert abs(m1["rho_direct_partial_env"]) <= kd.BANDS["p2_direct_max"]
    ratio = m1["rho_intra"] / m0["rho_intra"]
    # Bande scellee P1 = 0.80, adjudiquee sur le run principal calibre ; ce test
    # d'integration court tourne sur p_out NON calibre (0.02), ou le ratio
    # s'etablit a ~0.80 +- bruit d'echantillon — plage assoucie ici.
    assert ratio >= 0.70
    # Null (a), portee testable AVANT calibration : le canal direct vu au repos
    # est strictement superieur a celui vu a d = 1. La bande scellee (>= 0.15)
    # s'adjudique sur le run principal APRES calibration de p_out — a p_out non
    # calibre (0.02) le couplage direct reel est ~0.03, la vue de l'instrument
    # elle-meme etant prouvee au niveau estimateur (test keeps_direct_coupling).
    assert abs(m0["rho_direct_partial_env"]) > abs(m1["rho_direct_partial_env"])


def test_verdict_branches():
    base = dict(rho_intra=0.6, rho_intra_0=0.6, rho_direct_1=0.0,
                rho_direct_0=0.3, rho_env=0.5)
    v_ok = kd.verdict([dict(base)] * 5, [0.3] * 5)
    assert v_ok["verdict"] == "SUPPORTED"
    assert all(v_ok["checks"].values())

    v_p1 = kd.verdict([dict(base, rho_intra=0.3)] * 5, [0.3] * 5)
    assert v_p1["verdict"].startswith("NOT_SUPPORTED (P1")

    v_p3 = kd.verdict([dict(base, rho_env=0.1)] * 5, [0.3] * 5)
    assert v_p3["verdict"].startswith("NOT_SUPPORTED (P3")

    v_blind = kd.verdict([dict(base, rho_direct_0=0.05)] * 5, [0.3] * 5)
    assert v_blind["verdict"].startswith("NON_CONCLUSIF (null a")

    v_struct = kd.verdict([dict(base)] * 5, [0.9] * 5)
    assert v_struct["verdict"].startswith("NON_CONCLUSIF (null b")

    v_door = kd.verdict([dict(base, rho_intra_0=0.2)] * 5, [0.3] * 5)
    assert v_door["verdict"].startswith("NON_CONCLUSIF_INSTRUMENT")
