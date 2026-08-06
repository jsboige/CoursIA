"""Tests du module #7746 D2 experience A : coordination a vocabulaire fixe (Lewis/Skyrms).

Couvrent les proprietes mecaniques (MI, selection softmax, apprentissage Roth-Erev,
gardes de validation) ET les quatre verdicts falsifiables du banc d'essai :

1. **Emergence** — une convention emerge depuis des propensites uniformes (succes + MI
   montent, dominant nettement le controle sans-apprentissage).
2. **Goulot de vocabulaire** — un vocabulaire insuffisant limite strictement la
   signification (MI limited < MI full).
3. **Suivi MI-sens** — succes et MI co-croissent sur la trajectoire equilibree, et un
   etat dominant atteint un succes eleve sans signification (MI faible).
4. **Stabilite** — une convention etablie resiste a un choc modere et se reconstruit,
   tandis qu'un choc brutal l'effondre.

numpy + pytest, CPU uniquement. Les verdicts utilisent des graines deterministes
demontrant le phenomene ; l'emergence est empiriquement ~90% (pieux d'equilibre
partiel — un vrai phenomene de la litterature Skyrms, pas un bug), documente dans les
docstrings du module.
"""

import numpy as np
import pytest

from ict.signaling_convention import (
    SignalingGame,
    mutual_information,
    coordination_emerges_test,
    vocabulary_bottleneck_test,
    mi_tracks_meaning_test,
    convention_stability_test,
)


# --- Proprietes mecaniques ---


def test_mutual_information_extremes():
    """I(X;Y) = 0 pour l'independance, = log2(n) pour la bijection parfaite."""
    # Independance : chaque signal utilise pour chaque etat de facon uniforme.
    indep = np.full((4, 4), 1.0)
    assert mutual_information(indep) == pytest.approx(0.0, abs=1e-9)
    # Bijection : signal i <=> etat i, information mutuelle maximale = log2(4) = 2 bits.
    bijection = np.diag([1.0, 1.0, 1.0, 1.0])
    assert mutual_information(bijection) == pytest.approx(np.log2(4), abs=1e-9)


def test_mutual_information_zero_matrix():
    """Une matrice de comptes nulle renvoie MI = 0 (pas de division par zero)."""
    assert mutual_information(np.zeros((3, 3))) == 0.0


def test_initial_policy_is_near_uniform():
    """A l'init, aucun signal n'est prefere : le succes est ~1/n_states (hasard)."""
    g = SignalingGame(n_states=4, n_signals=4, temperature=0.5, rng=np.random.default_rng(0))
    # 800 tours sans renforcement = politique uniforme.
    for _ in range(800):
        g.play_round(reinforce=False)
    assert g.success_rate(800) == pytest.approx(0.25, abs=0.05)
    assert mutual_information(g.joint_state_signal) == pytest.approx(0.0, abs=0.05)


def test_reinforcement_raises_success():
    """L'apprentissage par renforcement monte le succes (vs controle sans-apprentissage)."""
    g_learn = SignalingGame(n_states=4, n_signals=4, temperature=0.6, rng=np.random.default_rng(1))
    g_learn.train(3000, anneal_to=0.15)
    g_ctrl = SignalingGame(n_states=4, n_signals=4, temperature=0.6, rng=np.random.default_rng(1))
    for _ in range(800):
        g_ctrl.play_round(reinforce=False)
    assert g_learn.success_rate(800) > 0.8
    assert g_ctrl.success_rate(800) < 0.35


def test_convention_is_bijection_when_learned():
    """Une convention apprise est (presque) bijective : chaque etat -> un signal dominant."""
    g = SignalingGame(n_states=4, n_signals=4, temperature=0.6, rng=np.random.default_rng(0))
    g.train(4000, anneal_to=0.15)
    # Pour chaque etat, un signal domine nettement (argmax distinct entre etats).
    dominant_signals = [int(np.argmax(g.Q_s[s])) for s in range(4)]
    assert len(set(dominant_signals)) == 4  # bijection : 4 signaux dominants distincts


# --- Gardes de validation ---


def test_invalid_dimensions_raise():
    with pytest.raises(ValueError):
        SignalingGame(n_states=0, n_signals=4)
    with pytest.raises(ValueError):
        SignalingGame(n_states=4, n_signals=0)


def test_invalid_temperature_raises():
    with pytest.raises(ValueError):
        SignalingGame(n_states=4, n_signals=4, temperature=0.0)


def test_invalid_state_dist_raises():
    with pytest.raises(ValueError):
        SignalingGame(n_states=4, n_signals=4, state_dist=[0.5, 0.5])  # mauvaise dimension
    with pytest.raises(ValueError):
        SignalingGame(n_states=4, n_signals=4, state_dist=[-0.1, 0.4, 0.4, 0.3])  # negatif


def test_reset_restores_fresh_state():
    """reset() ramene le jeu a l'etat initial : propensites uniformes, historique vide,
    MI nulle, succes nul. Le contrat « reinitialise » doit tenir apres apprentissage."""
    game = SignalingGame(n_states=3, n_signals=3, temperature=0.3, rng=np.random.default_rng(7))
    game.train(n_rounds=200, anneal_to=0.05)
    # Apres apprentissage : historique non vide, propensites non uniformes.
    assert len(game.success_history) == 200
    assert not np.allclose(game.Q_s, game.initial_q)
    # reset() : on revient a l'etat frais.
    game.reset()
    assert len(game.success_history) == 0
    assert game.success_rate() == 0.0
    assert game.state_signal_mi() == 0.0
    assert np.allclose(game.Q_s, game.initial_q)
    assert np.allclose(game.Q_r, game.initial_q)
    assert np.allclose(game.joint_state_signal, 0.0)


def test_train_negative_rounds_raises():
    """train(n_rounds < 0) leve ValueError (garde ligne 200-201)."""
    game = SignalingGame(n_states=2, n_signals=2, rng=np.random.default_rng(0))
    with pytest.raises(ValueError):
        game.train(n_rounds=-1)


def test_train_zero_rounds_is_noop():
    """train(n_rounds=0) est valide (boucle vide) : aucun tour joue, historique vide."""
    game = SignalingGame(n_states=2, n_signals=2, rng=np.random.default_rng(0))
    game.train(n_rounds=0)
    assert len(game.success_history) == 0


def test_train_anneal_restores_temperature():
    """Apres train(anneal_to=t_bas), la temperature revient a sa valeur initiale
    (restoration ligne 208) — l'annealing est transitoire, pas persistant."""
    game = SignalingGame(n_states=3, n_signals=3, temperature=0.5, rng=np.random.default_rng(0))
    t0 = game.temperature
    game.train(n_rounds=100, anneal_to=0.02)
    assert game.temperature == pytest.approx(t0)


def test_success_rate_window_larger_than_history():
    """success_rate(window > len(history)) renvoie la moyenne sur TOUT l'historique,
    sans crash (le slicing Python [-window:] couvre toute la liste)."""
    game = SignalingGame(n_states=2, n_signals=2, rng=np.random.default_rng(0))
    game.train(n_rounds=10)
    full = game.success_rate(window=10)
    oversize = game.success_rate(window=10_000)
    assert oversize == pytest.approx(full)


# --- Les quatre verdicts falsifiables (#7746 D2 experience A) ---


def test_coordination_emerges():
    """Verdict EMERGENCE : convention + signification emergent (controle sans-apprentissage domine)."""
    report = coordination_emerges_test(n_states=4, n_signals=4, seed=0)
    assert report["learned_success"] > 0.8
    assert report["learned_mi"] > 1.0  # > 0.5 * log2(4) = 1.0
    assert report["control_success"] < 0.35  # ~1/4, sans apprentissage
    assert report["control_mi"] < 0.1
    assert report["emerged"] == 1.0


def test_coordination_does_not_emerge_without_reinforcement_control():
    """Controle negatif : un jeu a tres faible renforcement n'emet pas le verdict.

    Verifie que le verdict n'est pas satisfait par construction — un 'apprentissage'
    trop court laisse la politique presqu'uniforme, donc emerged == 0."""
    report = coordination_emerges_test(n_states=4, n_signals=4, n_rounds=5, seed=0)
    assert report["learned_success"] < 0.5
    assert report["emerged"] == 0.0


def test_vocabulary_bottleneck():
    """Verdict GOULOT : vocabulaire insuffisant -> MI strictement < vocabulaire suffisant."""
    report = vocabulary_bottleneck_test(n_states=4, seed=0)
    assert report["mi_full_vocab"] > 1.0  # convention emerge avec assez de signaux
    assert report["mi_limited_vocab"] < 0.6 * report["mi_full_vocab"]
    assert report["bottleneck"] == 1.0


def test_mi_tracks_meaning():
    """Verdict SENS : MI co-croit avec le succes (equilibre), etat dominant = succes sans sens."""
    report = mi_tracks_meaning_test(n_states=4, seed=0)
    assert report["balanced_corr_mi_success"] > 0.6
    assert report["balanced_final_mi"] > 1.0
    # L'etat dominant atteint un succes eleve avec une MI plus faible (signification moindre).
    assert report["balanced_final_mi"] - report["dominant_final_mi"] > 0.3
    assert report["meaningful"] == 1.0


def test_convention_stability():
    """Verdict STABILITE : choc modere supporte, choc brutal effondre."""
    report = convention_stability_test(n_states=4, seed=0)
    assert report["established_success"] > 0.8
    assert report["moderate_immediate"] > 0.6
    assert report["moderate_recovered"] > 0.8
    assert report["brutal_immediate"] < report["moderate_immediate"] - 0.3
    assert report["stable"] == 1.0
