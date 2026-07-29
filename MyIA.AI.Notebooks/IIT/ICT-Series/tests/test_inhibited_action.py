"""Tests du module #7741 : animat inhibé (Laborit), contrôlabilité, inhibition.

Couvrent les quatres verdicts falsifiables du banc d'essai :

1. **Rigidification** — sous α=0 (inhibition totale), l'entropie d'action
   s'effondre (l'animat se replie sur le no-op) vs α=1 (exploration).
2. **Efficacité d'action orientée but** — l'animat ne peut plus atteindre/maintenir
   un but sous inhibition (la couverture d'états, elle, ne s'effondre pas : la
   dérive porte le corps partout).
3. **Estimation de contrôlabilité** — l'animat récupère α_true à ±0.1 près
   (prérequis : « savoir que ses actions ne contrôlent plus »).
4. **Pont dette d'irréversibilité I(R)** — sous inhibition, l'effet de l'action
   sur la dette s'annule (l'animat perd toute prise sur l'irréversibilité subie).

Plus les propriétés mécaniques (kernel stochastique, bouton α, gardes).
numpy + pytest, CPU uniquement.
"""

import numpy as np
import pytest

from ict.inhibited_action import (
    InhibitedEnvironment,
    action_entropy,
    adaptive_animat,
    controllability_estimation_test,
    estimate_controllability,
    goal_seeking_efficacy_test,
    irreversibility_debt_bridge,
    rigidification_test,
    state_coverage,
)


# --- Proprietes mecaniques de InhibitedEnvironment ---


def test_transition_kernel_rows_sum_to_one():
    """Chaque ligne du noyau de transition somme à 1 (stochastique)."""
    for alpha in (0.0, 0.3, 0.7, 1.0):
        env = InhibitedEnvironment(n_states=7, alpha=alpha, drift="uniform")
        for act in (-1, 0, 1):
            P = env.transition_kernel(act)
            np.testing.assert_allclose(P.sum(axis=0), np.ones(7), atol=1e-12)


def test_full_control_applies_action():
    """α=1 : la transition applique systematiquement l'action (controle total)."""
    env = InhibitedEnvironment(n_states=5, alpha=1.0, drift="uniform",
                               rng=np.random.default_rng(0))
    n = env.n_states
    for s in range(n):
        for a in (-1, 0, 1):
            assert env.transition(s, a) == env.intended(s, a)


def test_full_inhibition_ignores_action():
    """α=0 : l'action est ignoree (inhibition) — la transition ne vaut pas intended partout."""
    env = InhibitedEnvironment(n_states=5, alpha=0.0, drift="uniform",
                               rng=np.random.default_rng(0))
    # Sur assez de pas, la transition sous α=0 s'ecarte de l'effet attendu
    # (sinon l'action ne serait pas inhibee).
    mismatches = sum(env.transition(2, 1) != env.intended(2, 1) for _ in range(200))
    assert mismatches > 100  # la majorite des pas ignorent l'action.


def test_intended_is_modulo():
    """L'effet attendu est modulo n (anneau circulaire)."""
    env = InhibitedEnvironment(n_states=4, alpha=1.0)
    assert env.intended(3, 1) == 0   # (3 + 1) % 4
    assert env.intended(0, -1) == 3  # (0 - 1) % 4


# --- Gardes de validation ---


@pytest.mark.parametrize("bad_n", [0, 1, 2])
def test_invalid_n_states_raises(bad_n):
    with pytest.raises(ValueError):
        InhibitedEnvironment(n_states=bad_n, alpha=0.5)


@pytest.mark.parametrize("bad_alpha", [-0.1, 1.1, 2.0])
def test_invalid_alpha_raises(bad_alpha):
    with pytest.raises(ValueError):
        InhibitedEnvironment(n_states=5, alpha=bad_alpha)


def test_invalid_drift_raises():
    with pytest.raises(ValueError):
        InhibitedEnvironment(n_states=5, alpha=0.5, drift="sideways")


def test_transition_state_out_of_bounds_raises():
    env = InhibitedEnvironment(n_states=5, alpha=0.5)
    with pytest.raises(IndexError):
        env.transition(99, 1)


# --- estimate_controllability : propietes mecaniques ---


def test_estimate_controllability_endpoints():
    """Sous des transitions purement controlled / inhibées, l'estimateur recupere 1 / ~0."""
    n = 6
    rng = np.random.default_rng(0)
    states = rng.integers(0, n, size=2000)
    actions = rng.choice([-1, 0, 1], size=2000)
    # α=1 : next = intended partout.
    next_full = (states + actions) % n
    assert abs(estimate_controllability(states, actions, next_full, n) - 1.0) < 1e-9
    # α=0 : next aleatoire uniforme (independant de l'action).
    next_inhib = rng.integers(0, n, size=2000)
    assert estimate_controllability(states, actions, next_inhib, n) < 0.1


def test_estimate_controllability_empty():
    """Trajectoire vide -> estimateur 0 (pas de preuve de controle)."""
    assert estimate_controllability(np.array([]), np.array([]), np.array([]), 5) == 0.0


# --- Mesures de pathologie ---


def test_action_entropy_uniform_is_log3():
    """Actions −1/0/+1 uniformes -> entropie ln(3)."""
    a = np.tile([-1, 0, 1], 100)
    assert abs(action_entropy(a) - np.log(3)) < 1e-9


def test_action_entropy_collapsed_is_zero():
    """Une seule action repetee -> entropie 0 (rigidification)."""
    assert action_entropy(np.zeros(100, dtype=int)) == 0.0


def test_state_coverage_counts_distinct():
    assert state_coverage(np.array([0, 0, 1, 1, 2, 7]) % 10, 10) == 4


# --- Les quatre verdicts falsifiables #7741 ---


def test_rigidification_inhibited_drops_action_entropy():
    """Verdict RIGIDIFICATION : entropie sous α=0 nettement inférieure à α=1."""
    report = rigidification_test(n_states=9, n_steps=800, seed=0)
    assert report["action_entropy_controlled"] > 0.8  # ~ln(3) exploration
    assert report["chat_mean_inhibited"] < report["chat_mean_controlled"]
    assert report["entropy_drop"] > 0.3               # rigidification réelle
    assert report["rigidified"] == 1.0


def test_goal_seeking_efficacy_lost_under_inhibition():
    """Verdict EFFICACITÉ BUT : l'animat maintient moins bien la cible sous α=0."""
    report = goal_seeking_efficacy_test(n_states=9, n_steps=800, seed=0)
    assert report["target_fraction_controlled"] > report["target_fraction_inhibited"]
    assert report["efficacy_drop"] > 0.1
    assert report["lost_control"] == 1.0


def test_controllability_estimation_recovers_alpha():
    """Verdict ESTIMATION : alpha_hat recupere alpha_true a ±0.1 sur 3 régimes."""
    report = controllability_estimation_test(n_states=9, n_steps=2000, seed=0)
    assert report["max_abs_err"] < 0.1
    assert report["detected"] == 1.0


def test_irreversibility_debt_bridge_trapped():
    """Verdict PONT I(R) : sous inhibition, l'effet de l'action sur la dette s'annule."""
    report = irreversibility_debt_bridge(n_states=9)
    # Sous inhibition, changer d'action ne change plus la dette subie.
    assert report["action_effect_inhibited"] < 1e-9
    # À contrôle partiel, l'action modulait encore la dette.
    assert report["action_effect_partial_control"] > 0.5
    assert report["trapped"] == 1.0
