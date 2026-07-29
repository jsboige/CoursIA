"""Tests du module #7746 D2 experience C : adoption collective (seuil de performativite rho_c).

Couvrent les proprietes mecaniques (population, epinglage des instigateurs, appariement,
taux d'adoption), les gardes de validation ET les quatre verdicts falsifiables du banc
d'essai :

1. **Seuil de performativite** — il existe un ``rho_c`` critique : adoption faible
   sous le seuil, cascade au-dessus (courbe en S).
2. **Sous le seuil, la convention meurt** — a ``rho`` bas, l'adoption reste ~hasard.
3. **Au-dessus du seuil, cascade** — a ``rho`` haut, l'adoption -> proche de 1.
4. **Sans instigateur, pas de cascade** (controle negatif) — ``rho=0`` : pas de
   diffusion de la cible.

numpy + pytest, CPU uniquement.
"""

import numpy as np
import pytest

from ict.collective_adoption import (
    AdoptionGame,
    critical_threshold_test,
    below_threshold_dies_test,
    above_threshold_cascades_test,
    no_cascade_without_instigators_test,
)


# --- Proprietes mecaniques ---


def test_instigator_count_matches_fraction():
    """floor(rho * N) instigateurs exactement."""
    g = AdoptionGame(20, 3, instigator_fraction=0.3, rng=np.random.default_rng(0))
    assert g.n_instigators == 6
    assert g.n_naive == 14
    assert g.is_instigator.sum() == 6


def test_instigators_pinned_on_target():
    """Les instigateurs ont leur argmax Q_s/Q_r exactement sur la bijection cible."""
    g = AdoptionGame(10, 3, instigator_fraction=0.4, instigator_strength=10.0,
                     rng=np.random.default_rng(0))
    for a in range(g.n_agents):
        if g.is_instigator[a]:
            for s in range(3):
                assert np.argmax(g.Q_s[a, s]) == s
            for m in range(3):
                assert np.argmax(g.Q_r[a, m]) == m


def test_naive_start_uniform():
    """Les agents naifs demarrent a initial_q uniforme (aucune preference)."""
    g = AdoptionGame(10, 3, instigator_fraction=0.3, initial_q=1.0,
                     rng=np.random.default_rng(0))
    for a in range(g.n_agents):
        if not g.is_instigator[a]:
            assert g.Q_s[a] == pytest.approx(1.0)
            assert g.Q_r[a] == pytest.approx(1.0)


def test_all_instigators_full_adoption():
    """rho=1 (tous instigateurs) : population_adoption = 1.0, adoption_rate = 1.0."""
    g = AdoptionGame(8, 3, instigator_fraction=1.0, rng=np.random.default_rng(0))
    g.train(100)
    assert g.n_naive == 0
    assert g.adoption_rate() == 1.0
    assert g.population_adoption() == 1.0


def test_play_round_returns_payoff_in_unit_interval():
    """play_round renvoie un taux de coordination dans [0, 1]."""
    g = AdoptionGame(10, 3, instigator_fraction=0.3, temperature=0.5,
                     rng=np.random.default_rng(0))
    payoff = g.play_round()
    assert 0.0 <= payoff <= 1.0


def test_pairing_uses_all_agents():
    """Apres plusieurs tours, chaque agent a ete au moins une fois emetteur (compte joint > 0)."""
    g = AdoptionGame(8, 3, instigator_fraction=0.25, temperature=0.6,
                     rng=np.random.default_rng(1))
    g.train(400)
    # Chaque agent a du jouer en position emetteur au moins une fois.
    for a in range(g.n_agents):
        assert g.joint_state_signal[a].sum() > 0.0


def test_training_reinforces_naive():
    """Apres entrainement, les Q des naifs ont evolue (different de l'uniforme initial)."""
    g = AdoptionGame(10, 3, instigator_fraction=0.5, temperature=0.5,
                     rng=np.random.default_rng(2))
    init_q_naive = g.Q_s[~g.is_instigator].copy()
    g.train(1500, anneal_to=0.15)
    after_q_naive = g.Q_s[~g.is_instigator]
    assert not np.allclose(init_q_naive, after_q_naive)


def test_instigator_q_unchanged_after_training():
    """Les instigateurs epingles ne sont PAS modifies par l'entrainement."""
    g = AdoptionGame(10, 3, instigator_fraction=0.4, pin_instigators=True,
                     rng=np.random.default_rng(3))
    init_instig = g.Q_s[g.is_instigator].copy()
    g.train(1500, anneal_to=0.15)
    after_instig = g.Q_s[g.is_instigator]
    assert np.allclose(init_instig, after_instig)


# --- Gardes de validation ---


def test_invalid_n_agents_raises():
    with pytest.raises(ValueError):
        AdoptionGame(1, 3)  # < 2 impossible d'apparier


def test_invalid_n_states_raises():
    with pytest.raises(ValueError):
        AdoptionGame(10, 1)


def test_invalid_instigator_fraction_raises():
    with pytest.raises(ValueError):
        AdoptionGame(10, 3, instigator_fraction=-0.1)
    with pytest.raises(ValueError):
        AdoptionGame(10, 3, instigator_fraction=1.5)


def test_invalid_instigator_strength_raises():
    with pytest.raises(ValueError):
        AdoptionGame(10, 3, instigator_strength=0.0)


def test_invalid_temperature_raises():
    with pytest.raises(ValueError):
        AdoptionGame(10, 3, temperature=0.0)


def test_invalid_initial_q_raises():
    with pytest.raises(ValueError):
        AdoptionGame(10, 3, initial_q=-1.0)


# --- Les quatre verdicts falsifiables (#7746 D2 experience C) ---


def test_critical_threshold_exists():
    """Verdict SEUIL : il existe un rho_c critique (courbe en S)."""
    report = critical_threshold_test(n_agents=24, n_states=3, n_seeds=3, seed=0)
    assert report["adoption_at_low_rho"] < 0.20
    assert report["adoption_at_high_rho"] > 0.75
    assert report["max_jump"] > 0.25
    assert 0.25 < report["rho_c"] < 0.75
    assert report["threshold_exists"] == 1.0


def test_below_threshold_dies():
    """Verdict SOUS LE SEUIL : a rho=0.1, l'adoption reste ~hasard."""
    report = below_threshold_dies_test(n_agents=24, n_states=3, n_seeds=4, seed=0)
    assert report["adoption_at_low_rho"] < report["chance_level"] + 0.15
    assert report["dies"] == 1.0


def test_above_threshold_cascades():
    """Verdict AU-DESSUS DU SEUIL : a rho=0.8, l'adoption cascade."""
    report = above_threshold_cascades_test(n_agents=24, n_states=3, n_seeds=4, seed=0)
    assert report["adoption_at_high_rho"] > 0.75
    assert report["cascades"] == 1.0


def test_no_cascade_without_instigators_control():
    """Controle negatif : rho=0 -> pas de cascade vers la cible."""
    report = no_cascade_without_instigators_test(n_agents=24, n_states=3, n_seeds=4, seed=0)
    assert report["adoption_at_rho_zero"] < 0.20
    assert report["no_cascade"] == 1.0
