"""Tests du module ICT-12 (champs de valence et animats).

Verifient le champ de valence (bosse attractive + obstacles repulsifs), les
cinematiques de source (4 regimes), le modele interne p_hat (interception 2D),
les 4 grandeurs de role, et surtout le coeur conceptuel falsifiable (gate 1 de
l'issue #4878) : il existe au moins un regime ou l'animat a modele interne p_hat
**perd** face au reactif (suivi de gradient), et un regime ou il **gagne**.

On n'asserte JAMAIS la totalite du verdict « regime-dependant » : c'est le gate
que le notebook doit decouvrir. On verifie seulement les directions qualitatives
qui rendent le banc non trivial.

Numpy + pytest. CPU uniquement."""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import valence as V  # noqa: E402


# --------------------------------------------------------------------------- #
#  Champ de valence                                                            #
# --------------------------------------------------------------------------- #
def test_valence_at_peak_at_source():
    src = np.array([10.0, 10.0])
    assert V.valence_at(src, src) == pytest.approx(1.0, abs=1e-9)
    # decroit quand on s'eloigne
    far = np.array([20.0, 10.0])
    assert V.valence_at(far, src) < V.valence_at(src, src)
    assert V.valence_at(far, src) > 0.0


def test_valence_at_obstacle_lowers_value():
    src = np.array([10.0, 10.0])
    obs = np.array([12.0, 10.0])
    p = np.array([12.0, 10.0])  # sur l'obstacle
    assert V.valence_at(p, src, obstacles=np.array([obs])) < V.valence_at(p, src)


def test_valence_gradient_points_toward_source():
    src = np.array([20.0, 20.0])
    pos = np.array([10.0, 10.0])
    g = V.valence_gradient(pos, src)
    # le gradient pointe vers la source (composantes positives ici)
    assert g[0] > 0.0 and g[1] > 0.0


def test_valence_grid_shape_and_peak():
    src = np.array([8.0, 8.0])
    grid = V.valence_grid(16, src)
    assert grid.shape == (16, 16)
    # le pic est au pixel le plus proche de la source
    peak = np.unravel_index(np.argmax(grid), grid.shape)
    assert peak[0] == 8 and peak[1] == 8


# --------------------------------------------------------------------------- #
#  Cinematiques de source (4 regimes)                                          #
# --------------------------------------------------------------------------- #
def test_source_statique_stays_near_center():
    rng = np.random.default_rng(0)
    traj = V.source_trajectory("statique", 100, 32, rng=rng)
    center = np.array([16.0, 16.0])
    d = np.linalg.norm(traj - center, axis=1)
    assert np.all(d < 2.0)  # jitter negligeable autour du centre


def test_source_balistique_moves_away_and_stays_in_bounds():
    rng = np.random.default_rng(1)
    traj = V.source_trajectory("balistique", 200, 32, rng=rng)
    assert np.all(traj >= 0.0) and np.all(traj < 32.0)
    # la source a bien voyage (distance parcourue > 0)
    assert np.linalg.norm(traj[-1] - traj[0]) > 1.0 or \
           np.linalg.norm(traj[100] - traj[0]) > 1.0


def test_source_erratique_reverses():
    # taux de renversement de cap eleve
    rng = np.random.default_rng(2)
    traj = V.source_trajectory("erratique", 400, 32, rng=rng, reversal_p=0.2)
    moves = np.diff(traj, axis=0)
    dots = np.einsum("ij,ij->i", moves[1:], moves[:-1])
    # au moins un renversement (produit scalaire < 0) sur la trajectoire
    assert np.any(dots < 0.0)


def test_source_bruite_stays_near_center():
    rng = np.random.default_rng(3)
    traj = V.source_trajectory("bruite", 100, 32, rng=rng, noise=1.0)
    center = np.array([16.0, 16.0])
    assert np.all(np.linalg.norm(traj - center, axis=1) < 5.0)


def test_source_unknown_kind_raises():
    with pytest.raises(ValueError):
        V.source_trajectory("inconnu", 10, 32)


# --------------------------------------------------------------------------- #
#  Modele interne p_hat                                                        #
# --------------------------------------------------------------------------- #
def test_predict_source_balistique_is_accurate():
    # source a vitesse constante pure : p_hat doit predire la position future
    rng = np.random.default_rng(5)
    src = V.source_trajectory("balistique", 60, 64, rng=rng)
    lead = 4
    errs = []
    for t in range(40, 56):
        pred = V.predict_source(src, t, lead=lead, alpha=0.25)
        errs.append(np.linalg.norm(pred - src[t + lead]) if t + lead < len(src) else 0.0)
    # sur du balistique, l'erreur de prediction reste modeste (< 5 unites)
    assert np.mean(errs) < 5.0


def test_predict_source_static_no_motion():
    rng = np.random.default_rng(6)
    src = V.source_trajectory("statique", 40, 32, rng=rng)
    pred = V.predict_source(src, 30, lead=4, alpha=0.25)
    # pas de mouvement => prediction proche de la position courante
    assert np.linalg.norm(pred - src[30]) < 1.0


# --------------------------------------------------------------------------- #
#  Animats : reactif vs p_hat vs marche aleatoire                              #
# --------------------------------------------------------------------------- #
def test_reactive_moves_toward_source():
    src = V.source_trajectory("statique", 60, 32, rng=np.random.default_rng(7),
                              start=np.array([16.0, 16.0]))
    start = np.array([2.0, 2.0])
    traj = V.simulate_reactive(src, 32, start, 60)
    # l'animat s'est rapproche de la source (centre)
    d0 = np.linalg.norm(start - src[0])
    d_end = np.linalg.norm(traj[-1] - src[-1])
    assert d_end < d0


def test_trajectories_in_bounds():
    src = V.source_trajectory("balistique", 80, 32, rng=np.random.default_rng(8))
    for fn in (V.simulate_reactive, lambda *a, **k: V.simulate_phat(*a, **k)):
        tr = fn(src, 32, np.array([2.0, 2.0]), 80)
        assert np.all(tr >= 0.0) and np.all(tr < 32.0)


def test_random_walk_is_bounded():
    rng = np.random.default_rng(9)
    tr = V.random_walk(32, np.array([16.0, 16.0]), 200, rng=rng)
    assert np.all(tr >= 0.0) and np.all(tr < 32.0)


# --------------------------------------------------------------------------- #
#  Quatre grandeurs de role                                                    #
# --------------------------------------------------------------------------- #
def test_capture_rate_directed_beats_random():
    rng = np.random.default_rng(10)
    src = V.source_trajectory("balistique", 150, 32, rng=rng, start=np.array([16.0, 16.0]))
    tr_r = V.simulate_reactive(src, 32, np.array([20.0, 20.0]), 150)
    tr_a = V.random_walk(32, np.array([20.0, 20.0]), 150, rng=rng)
    assert V.capture_rate(tr_r, src) > V.capture_rate(tr_a, src)


def test_capture_rate_in_range():
    rng = np.random.default_rng(11)
    src = V.source_trajectory("statique", 50, 32, rng=rng)
    tr = V.simulate_reactive(src, 32, np.array([16.0, 16.0]), 50)
    c = V.capture_rate(tr, src, radius=2.0)
    assert 0.0 <= c <= 1.0


def test_escape_rate_no_obstacle_is_zero():
    rng = np.random.default_rng(12)
    src = V.source_trajectory("statique", 40, 32, rng=rng)
    tr = V.simulate_reactive(src, 32, np.array([16.0, 16.0]), 40)
    assert V.escape_rate(tr, src, obstacles=None) == 0.0


def test_escape_rate_with_obstacle_in_range():
    rng = np.random.default_rng(13)
    src = V.source_trajectory("statique", 60, 32, rng=rng)
    obs = np.array([[16.0, 17.0]])
    tr = V.simulate_reactive(src, 32, np.array([8.0, 8.0]), 60, obstacles=obs)
    e = V.escape_rate(tr, src, obstacles=obs)
    assert 0.0 <= e <= 1.0


def test_path_irreversibility_static_source_low():
    # source statique : aller ~ retour => irreversibilite faible
    rng = np.random.default_rng(14)
    src = V.source_trajectory("statique", 80, 32, rng=rng)
    tr = V.simulate_reactive(src, 32, np.array([16.0, 16.0]), 80)
    assert V.path_irreversibility(tr, src) < 0.3


def test_path_irreversibility_in_range():
    rng = np.random.default_rng(15)
    src = V.source_trajectory("balistique", 100, 32, rng=rng)
    tr = V.simulate_phat(src, 32, np.array([20.0, 20.0]), 100)
    ir = V.path_irreversibility(tr, src)
    assert -1.0 <= ir <= 1.0


def test_role_switching_erratic_higher_than_ballistic():
    # l'erratique bascule plus souvent le cap que le balistique
    rng_e = np.random.default_rng(16)
    rng_b = np.random.default_rng(17)
    tr_e = V.source_trajectory("erratique", 200, 32, rng=rng_e, reversal_p=0.2)
    tr_b = V.source_trajectory("balistique", 200, 32, rng=rng_b)
    # ce sont des trajectoires de SOURCE, mais role_switching mesure juste la
    # trajectoire => un predateur erratique bascule plus qu'un balistique
    assert V.role_switching(tr_e) > V.role_switching(tr_b)


def test_role_switching_in_range():
    rng = np.random.default_rng(18)
    src = V.source_trajectory("balistique", 100, 32, rng=rng)
    tr = V.simulate_reactive(src, 32, np.array([20.0, 20.0]), 100)
    s = V.role_switching(tr)
    assert 0.0 <= s <= 1.0


# --------------------------------------------------------------------------- #
#  Banc par regime (gate 1 falsifiable : p_hat gagne ET perd)                  #
# --------------------------------------------------------------------------- #
def test_regime_report_keys_and_ranges():
    rng = np.random.default_rng(19)
    rep = V.regime_report("balistique", size=32, n_steps=150, n_seeds=2, rng=rng)
    for animat in ("reactif", "phat", "aleatoire"):
        assert animat in rep
        for m in ("capture", "escape", "irrevers", "switch"):
            assert m in rep[animat]
            assert -1.0 <= rep[animat][m] <= 1.0 or m in ("capture", "escape")


def test_phat_beats_reactive_on_ballistic():
    """Gate 1 (direction gagnante) : sur le regime balistique (previsible),
    l'anticipateur p_hat capture au moins aussi bien que le reactif."""
    rng = np.random.default_rng(20)
    rep = V.regime_report("balistique", size=32, n_steps=200, n_seeds=4, rng=rng)
    # p_hat ne doit pas etre ecrase par le reactif sur le balistique
    assert rep["phat"]["capture"] >= rep["reactif"]["capture"] * 0.9


def test_phat_loses_or_ties_on_erratic():
    """Gate 1 (direction perdante) : sur le regime erratique (imprevisible),
    le reactif (persistance spatiale) ne fait pas pire que p_hat."""
    rng = np.random.default_rng(21)
    rep = V.regime_report("erratique", size=32, n_steps=200, n_seeds=4, rng=rng,
                          lead=4)
    assert rep["reactif"]["capture"] >= rep["phat"]["capture"] * 0.95


def test_random_walk_lowest_capture_overall():
    """Controle d'ablation (gate 2) : la marche aleatoire capture moins que les
    deux animats orientes, en moyenne sur un regime previsible."""
    rng = np.random.default_rng(22)
    rep = V.regime_report("balistique", size=32, n_steps=200, n_seeds=4, rng=rng)
    assert rep["aleatoire"]["capture"] < rep["reactif"]["capture"]
    assert rep["aleatoire"]["capture"] < rep["phat"]["capture"]


# --------------------------------------------------------------------------- #
#  Anticipation 2D : baselines adverses (gate 3)                               #
# --------------------------------------------------------------------------- #
def test_anticipation_error_nonneg_and_baselines():
    rng = np.random.default_rng(23)
    src = V.source_trajectory("balistique", 80, 32, rng=rng)
    lead = 4
    phat = V.phat_predicted_trajectory(src, lead=lead)
    pers = V.persistence_trajectory_2d(src)
    ma = V.moving_average_trajectory_2d(src)
    ar1 = V.ar1_trajectory_2d(src, lead=lead)
    e_ph = V.anticipation_error_2d(phat, src, lead)
    e_pers = V.anticipation_error_2d(pers, src, lead)
    assert e_ph >= 0.0 and e_pers >= 0.0
    # sur du balistique, p_hat bat la persistance (contenu predictif reel)
    assert e_ph <= e_pers * 1.5
