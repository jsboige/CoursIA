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
    f = kd.EvocationField.build(seed=0, p_out=kd.CALIBRATED_P_OUT,
                                beta_scale=kd.CALIBRATED_BETA_SCALE)
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


def test_row_mass_preserved_across_dissociation(field):
    # Amendement v4 : couper l'évocation inter-alters n'assombrit pas les
    # alters — chaque nœud garde sa masse d'évocation (renormalisation).
    # Exception déclarée : un nœud sans aucune arête intra restante à d = 1
    # (toute sa masse était inter) n'a rien vers quoi rediriger — il s'éteint.
    for d in (0.5, 0.8, 1.0):
        Wd = field.W_at(d)
        alive = Wd.sum(axis=1) > 0
        np.testing.assert_allclose(
            Wd.sum(axis=1)[alive], field.W.sum(axis=1)[alive], rtol=1e-9)


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


def test_random_damage_same_budget_hits_intra(field):
    rng = np.random.default_rng(5)
    W_rand = kd.random_damage_W(field, rng)
    # Amendement v4 : masse totale préservée (renorm, comme le bras dissociation).
    np.testing.assert_allclose(W_rand.sum(), field.W.sum(), rtol=1e-9)
    # Le dommage touche l'intra : des arêtes intra sont amoindries ou nulles,
    # et l'inter n'est pas entièrement coupée (sinon ce serait une dissociation).
    intra_damaged = (W_rand[field.intra_mask] < field.W[field.intra_mask] - 1e-12).sum()
    inter_surviving = (W_rand[field.inter_mask] > 1e-12).sum()
    assert intra_damaged > 0
    assert inter_surviving > 0


def test_privacy_holds_and_intra_survives_short_run(field):
    # Intégration courte : T réduit, mêmes lois — P2 doit être ≈ 0 à d = 1,
    # et le ratio P1 reste ≥ bande même avec du bruit d'échantillon.
    m0 = kd.measure(field, 0.0, np.random.default_rng(101), t_steps=8_000, burn_in=1_000)
    m1 = kd.measure(field, 1.0, np.random.default_rng(102), t_steps=8_000, burn_in=1_000)
    assert abs(m1["rho_direct_partial_env"]) <= kd.BANDS["p2_direct_max"]
    ratio = m1["rho_intra"] / m0["rho_intra"]
    # Bande scellee P1 = 0.80, adjudiquee sur le run principal (T = 20 000) ;
    # ce test d'integration court (T = 8 000) vise la meme loi a +/- bruit
    # d'echantillon — plage assoucie ici.
    assert ratio >= 0.70
    # Null (a) : l'instrument (amendement v3, niveau alter) voit le canal direct
    # au repos — la fixture tourne a p_out = 0.02, la valeur calibree gelee
    # (§6ter), ou la partielle agrégée à d = 0 s'établit à ~0.36.
    assert abs(m0["rho_direct_partial_env"]) >= kd.BANDS["null_a_direct0_min"]


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
