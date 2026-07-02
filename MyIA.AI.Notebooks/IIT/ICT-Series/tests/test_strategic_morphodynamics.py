"""Tests du module ICT-13 (morphodynamique strategique d'Axelrod).

Verifient les gains du PD, les strategies (TFT/grim/Pavlov), les matchs IPD avec
bruit, le tournoi round-robin, la dynamique de replicateur, le seuil analytique
de grim trigger (gate 2 : retrouve numeriquement), les bassins d'invasion
(gate 4) et l'effondrement sous bruit (gate 3 : TFT chute, GTFT/Pavlov resistent).

Coeur falsifiable mais reproductible : on ne predit JAMAIS l'ordre exact du
tournoi (sensible au tirage) ; on verifie les DIRECTIONS qualitatives qui rendent
le banc non trivial, et l'accord numerique du seuil grim (gate 2).

Numpy + pytest. CPU uniquement."""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import strategic_morphodynamics as M  # noqa: E402


# --------------------------------------------------------------------------- #
#  Gains du dilemme du prisonnier                                              #
# --------------------------------------------------------------------------- #
def test_payoff_pair_all_cases():
    assert M.payoff_pair(M.C, M.C) == (3.0, 3.0)
    assert M.payoff_pair(M.D, M.C) == (5.0, 0.0)
    assert M.payoff_pair(M.C, M.D) == (0.0, 5.0)
    assert M.payoff_pair(M.D, M.D) == (1.0, 1.0)


def test_payoff_pair_custom_gains():
    # jeu personalise : T=4,R=3,P=2,S=1
    assert M.payoff_pair(M.C, M.C, T=4, R=3, P=2, S=1) == (3.0, 3.0)
    assert M.payoff_pair(M.D, M.C, T=4, R=3, P=2, S=1) == (4.0, 1.0)


def test_pd_ordering_constraint():
    # T>R>P>S et 2R>T+S (contrainte du PD)
    T, R, P, S = M.CANON["T"], M.CANON["R"], M.CANON["P"], M.CANON["S"]
    assert T > R > P > S
    assert 2 * R > T + S


# --------------------------------------------------------------------------- #
#  Strategies                                                                   #
# --------------------------------------------------------------------------- #
def test_tft_mirrors_opponent():
    own = np.array([M.C, M.C, M.D])
    opp = np.array([M.C, M.D, M.C])
    assert M.tft(np.array([]), np.array([])) == M.C  # premier coup
    assert M.tft(own, opp) == M.C  # dernier coup adverse = C -> cooperer


def test_grim_never_forgives():
    own = np.array([M.C])
    opp_clean = np.array([M.C])
    opp_dirty = np.array([M.D])
    assert M.grim(own, opp_clean) == M.C
    assert M.grim(own, opp_dirty) == M.D  # defocte forever apres 1 defection


def test_pavlov_win_stay_lose_shift():
    # dernier coup own=C, adversaire=C : gain R (gagne) -> stay C
    own = np.array([M.C]); opp = np.array([M.C])
    assert M.pavlov(own, opp) == M.C
    # dernier coup own=C, adversaire=D : gain S (perd) -> shift D
    own = np.array([M.C]); opp = np.array([M.D])
    assert M.pavlov(own, opp) == M.D
    # dernier coup own=D, adversaire=C : gain T (gagne) -> stay D
    own = np.array([M.D]); opp = np.array([M.C])
    assert M.pavlov(own, opp) == M.D


def test_allc_and_alld():
    assert M.allc(np.array([M.C, M.D]), np.array([M.D])) == M.C
    assert M.alld(np.array([M.C]), np.array([M.C])) == M.D


# --------------------------------------------------------------------------- #
#  Match IPD avec bruit                                                        #
# --------------------------------------------------------------------------- #
def test_play_match_deterministic_no_noise():
    rng = np.random.default_rng(0)
    # AllD vs AllC : AllD devrait dominer nettement
    g_d, g_c = M.play_match(M.alld, M.allc, n_rounds=100, noise=0.0, rng=rng)
    assert g_d > g_c
    assert g_d == pytest.approx(5.0, abs=1e-9)  # T a chaque coup
    assert g_c == pytest.approx(0.0, abs=1e-9)  # S a chaque coup


def test_play_match_tft_vs_allc_ties():
    rng = np.random.default_rng(1)
    # TFT vs AllC : cooperation mutuelle, R chaque coup (apres le 1er aussi C)
    g_t, g_c = M.play_match(M.tft, M.allc, n_rounds=100, noise=0.0, rng=rng)
    assert g_t == pytest.approx(3.0, abs=1e-9)
    assert g_c == pytest.approx(3.0, abs=1e-9)


def test_play_match_scores_in_range():
    rng = np.random.default_rng(2)
    strat = M.make_strategies(rng)
    g1, g2 = M.play_match(strat["tft"], strat["grim"], n_rounds=50, noise=0.1, rng=rng)
    # gains moyens dans [S, T]
    assert 0.0 <= g1 <= 5.0 and 0.0 <= g2 <= 5.0


# --------------------------------------------------------------------------- #
#  Tournoi round-robin (gate 1)                                                #
# --------------------------------------------------------------------------- #
def test_round_robin_keys_and_ranges():
    rng = np.random.default_rng(3)
    strat = M.make_strategies(rng)
    scores = M.round_robin(strat, n_rounds=100, noise=0.0, n_reps=1, rng=rng)
    assert set(scores.keys()) == set(strat.keys())
    for v in scores.values():
        assert 0.0 <= v <= 5.0


def test_round_robin_alld_beats_allc_one_on_one_deterministic():
    rng = np.random.default_rng(4)
    strat = M.make_strategies(rng)
    # sans bruit, AllD exploite AllC ; sur le tournoi global l'ordre depend du
    # champ, mais AllD vs AllC donne toujours T a AllD
    g_d, _ = M.play_match(strat["alld"], strat["allc"], n_rounds=50, noise=0.0, rng=rng)
    assert g_d == pytest.approx(5.0, abs=1e-9)


def test_payoff_matrix_shape_and_symdiag():
    rng = np.random.default_rng(5)
    strat = M.make_strategies(rng)
    A = M.payoff_matrix(strat, n_rounds=50, noise=0.0, n_reps=2, rng=rng)
    assert A.shape == (len(strat), len(strat))
    # toutes les entrees dans [S, T]
    assert np.all(A >= 0.0) and np.all(A <= 5.0)


# --------------------------------------------------------------------------- #
#  Dynamique de replicateur                                                     #
# --------------------------------------------------------------------------- #
def test_replicator_pure_strategy_fixed():
    # une population pure (x0 = e_i) est un point fixe
    A = np.array([[3.0, 0.0], [5.0, 1.0]])
    x0 = np.array([0.0, 1.0])  # AllD pur
    traj = M.replicator_trajectory(A, x0, n_steps=50)
    assert traj[-1, 1] == pytest.approx(1.0, abs=1e-9)
    assert traj[-1, 0] == pytest.approx(0.0, abs=1e-9)


def test_replicator_alld_invades_allc():
    # matrice du PD 2-strategies (C, D) : D envahit (dominance stricte)
    A = np.array([[3.0, 0.0], [5.0, 1.0]])  # C vs {C,D} ; D vs {C,D}
    x0 = np.array([0.9, 0.1])  # majoritairement C
    traj = M.replicator_trajectory(A, x0, n_steps=500)
    assert traj[-1, 1] > 0.9  # D envahit


def test_replicator_trajectory_shape():
    A = np.array([[3.0, 1.0], [1.0, 3.0]])
    traj = M.replicator_trajectory(A, np.array([0.5, 0.5]), n_steps=100)
    assert traj.shape == (101, 2)
    # conservation de la somme des frequences
    assert np.allclose(traj.sum(axis=1), 1.0, atol=1e-6)


# --------------------------------------------------------------------------- #
#  Gate 2 : seuil grim trigger (analytique vs numerique)                       #
# --------------------------------------------------------------------------- #
def test_grim_threshold_canonical():
    # T=5, R=3, P=1 -> (T-R)/(T-P) = 2/4 = 0.5
    assert M.grim_threshold() == pytest.approx(0.5, abs=1e-9)


def test_grim_threshold_custom():
    # T=4, R=3, P=1 -> (4-3)/(4-1) = 1/3
    assert M.grim_threshold(T=4, R=3, P=1) == pytest.approx(1 / 3, abs=1e-9)


def test_grim_resists_above_threshold():
    """Gate 2 : pour delta > seuil, grim_vs_grim bat alld_vs_grim (resiste)."""
    rng = np.random.default_rng(10)
    thr = M.grim_threshold()
    delta_high = thr + 0.2  # bien au-dessus du seuil
    gg, ga = M.grim_continuation_payoff(delta_high, n_rounds=800, rng=rng)
    assert gg > ga


def test_grim_invaded_below_threshold():
    """Gate 2 : pour delta < seuil, AllD fait mieux que grim contre grim
    (grim ne resiste pas)."""
    rng = np.random.default_rng(11)
    thr = M.grim_threshold()
    delta_low = max(0.05, thr - 0.2)
    gg, ga = M.grim_continuation_payoff(delta_low, n_rounds=800, rng=rng)
    assert ga > gg


def test_grim_crossing_near_analytic():
    """Gate 2 : le croisement numerique doit etre proche du seuil analytique."""
    rng = np.random.default_rng(12)
    thr = M.grim_threshold()
    deltas = np.linspace(0.1, 0.9, 17)
    _, _, crossing = M.grim_resists_threshold(deltas, rng=rng)
    # accord a +/- 2 pas de grille (= 0.1)
    assert abs(crossing - thr) <= 0.15


# --------------------------------------------------------------------------- #
#  Gate 4 : bassins d'invasion                                                  #
# --------------------------------------------------------------------------- #
def test_invasion_basin_shapes():
    # matrice 2-strategies : invader AllD (idx 1) vs resident AllC (idx 0)
    A = np.array([[3.0, 0.0], [5.0, 1.0]])
    x0s, finals = M.invasion_basin(A, invader_idx=1, resident_idx=0, n_points=21, n_steps=300)
    assert x0s.shape == finals.shape == (21,)
    assert 0.0 <= finals.min() and finals.max() <= 1.0


def test_critical_fraction_allc_resident():
    # AllD envahit AllC des qu'il est present (dominance stricte) -> seuil ~ 0
    A = np.array([[3.0, 0.0], [5.0, 1.0]])
    x0s, finals = M.invasion_basin(A, invader_idx=1, resident_idx=0, n_points=26, n_steps=500)
    crit = M.critical_fraction(x0s, finals)
    assert crit is not None
    assert crit < 0.2  # AllD envahit meme a faible dose


def test_critical_fraction_returns_none_when_no_invasion():
    # un resident invincible (domine strictement l'envahisseur)
    A = np.array([[5.0, 5.0], [0.0, 0.0]])  # strategie 0 bat toujours 1
    x0s, finals = M.invasion_basin(A, invader_idx=1, resident_idx=0, n_points=11, n_steps=200)
    # l'envahisseur (idx 1) ne tient pas -> final ~ 0 partout sauf x0=1
    assert M.critical_fraction(x0s[:-1], finals[:-1]) is None  # excluant x0=1


# --------------------------------------------------------------------------- #
#  Gate 3 : effondrement sous bruit                                            #
# --------------------------------------------------------------------------- #
def test_noise_collapse_keys_and_ranges():
    rng = np.random.default_rng(20)
    strat = M.make_strategies(rng)
    grid = np.linspace(0.0, 0.3, 7)
    out = M.noise_collapse(strat, grid, n_rounds=80, n_reps=2, rng=rng)
    assert set(out.keys()) == set(strat.keys())
    for arr in out.values():
        assert arr.shape == (7,)
        assert np.all(arr >= 0.0) and np.all(arr <= 5.0)


def test_tft_collapses_more_than_gtft_under_noise():
    """Gate 3 (direction) : sous bruit eleve, TFT chute plus que GTFT (qui pardonne)."""
    rng = np.random.default_rng(21)
    strat = M.make_strategies(rng)
    grid = np.array([0.0, 0.1, 0.2, 0.3, 0.4])
    out = M.noise_collapse(strat, grid, n_rounds=150, n_reps=3, rng=rng)
    # chute de TFT = score a bruit haut - score a bruit nul
    drop_tft = out["tft"][0] - out["tft"][-1]
    drop_gtft = out["gtft"][0] - out["gtft"][-1]
    assert drop_tft > drop_gtft  # TFT chute davantage
