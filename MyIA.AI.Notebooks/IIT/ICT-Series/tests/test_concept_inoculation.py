"""Tests du module #7746 D2 experience D : inoculation d'un cadrage (concept/persona).

Couvrent les proprietes mecaniques (inoculation de la graine, transmission
opportuniste, oubli des convertis, exemption/decay des instigateurs, suivi des
expositions), les gardes de validation ET les quatre verdicts falsifiables du banc
d'essai :

1. **Transmission** — le concept se diffuse au-dela des graines initiales.
2. **Biais de confirmation** — un biais croissant freine (throttle) la fraction finale.
3. **Declin post-instigateur** — sans la source, l'oubli fait decliner le concept.
4. **Controle negatif** — ``transmission_rate=0`` ne convertit personne.

numpy + pytest, CPU uniquement.
"""

import numpy as np
import pytest

from ict.concept_inoculation import (
    ConceptInoculation,
    transmission_grows_test,
    confirmation_bias_throttles_test,
    instigator_removal_decline_test,
    no_transmission_control_test,
)


# --- Proprietes mecaniques ---


def test_construction_and_reset():
    """reset inocule floor(seed*N) agents, le reste a 0."""
    g = ConceptInoculation(10, seed_fraction=0.3, rng=np.random.default_rng(0))
    assert g.n_seeds == 3
    assert int(g.opinion.sum()) == 3
    assert int(g.is_instigator.sum()) == 3
    # Les instigateurs sont exactement les porteurs initiaux.
    assert np.all(g.opinion[g.is_instigator] == 1)
    assert np.all(g.opinion[~g.is_instigator] == 0)


def test_play_round_returns_fraction_in_unit_interval():
    """play_round renvoie la fraction de porteurs dans [0, 1]."""
    g = ConceptInoculation(20, seed_fraction=0.2, transmission_rate=0.5,
                           rng=np.random.default_rng(0))
    frac = g.play_round()
    assert 0.0 <= frac <= 1.0


def test_history_length_matches_rounds():
    """Un point d'historique par tour joue."""
    g = ConceptInoculation(30, seed_fraction=0.1, transmission_rate=0.3,
                           rng=np.random.default_rng(0))
    g.train(100)
    assert len(g.history) == 100


def test_transmission_converts_non_carrier():
    """transmission_rate=1.0 convertit tout non-porteur expose."""
    g = ConceptInoculation(30, seed_fraction=3 / 30, transmission_rate=1.0,
                           rng=np.random.default_rng(0))
    g.train(50, burn_in=0)
    # Avec rate=1.0, le concept sature tres vite : convertis au-dela de la graine > 0.
    assert g.converted_beyond_seed() > 0
    assert g.final_fraction() > 0.5


def test_zero_transmission_no_conversion():
    """transmission_rate=0 -> aucun converti au-dela de la graine."""
    g = ConceptInoculation(30, seed_fraction=3 / 30, transmission_rate=0.0,
                           rng=np.random.default_rng(0))
    g.train(50, burn_in=0)
    assert g.converted_beyond_seed() == 0
    assert g.final_fraction() == pytest.approx(3 / 30)


def test_exposure_increments_on_contact():
    """Un non-porteur en contact avec un porteur voit son compteur d'exposition croitre."""
    g = ConceptInoculation(30, seed_fraction=3 / 30, transmission_rate=0.0,
                           rng=np.random.default_rng(1))
    g.train(30, burn_in=0)
    # Avec rate=0, aucune conversion mais des expositions : au moins un non-porteur expose.
    assert int((g.exposure > 0).sum()) > 0


def test_instigators_exempt_from_forget_while_present():
    """Tant que l'instigateur est present, il n'oublie pas (opinion reste 1)."""
    g = ConceptInoculation(30, seed_fraction=5 / 30, transmission_rate=0.2,
                           forget_rate=1.0, rng=np.random.default_rng(0))
    g.train(50, burn_in=0)  # instigateur present tout le long (burn_in=0)
    assert np.all(g.opinion[g.is_instigator] == 1)


def test_instigator_decay_when_removed():
    """Avec decay=1.0 et instigateur retire, les graines retombent a 0."""
    # transmission_rate=0 : seules les graines portent le concept.
    g = ConceptInoculation(40, seed_fraction=0.2, transmission_rate=0.0,
                           instigator_decay=1.0, forget_rate=0.0,
                           rng=np.random.default_rng(0))
    g.train(50, burn_in=10)  # apres t=10, instigateur retire
    assert g.final_fraction() < 0.01  # toutes les graines sont tombees
    # Controle : sans decay, les graines persistent.
    g0 = ConceptInoculation(40, seed_fraction=0.2, transmission_rate=0.0,
                            instigator_decay=0.0, forget_rate=0.0,
                            rng=np.random.default_rng(0))
    g0.train(50, burn_in=10)
    assert g0.final_fraction() == pytest.approx(0.2, abs=0.05)


def test_forget_rate_reduces_fraction_when_instigator_absent():
    """forget_rate>0 avec instigateur retire -> fraction finale plus basse."""
    common = dict(n_agents=40, seed_fraction=0.1, transmission_rate=0.2,
                  instigator_decay=0.8)
    no_forget = []
    high_forget = []
    for s in range(4):
        g0 = ConceptInoculation(**common, forget_rate=0.0, rng=np.random.default_rng(s))
        g0.train(200, burn_in=30)
        no_forget.append(g0.final_fraction())
        g1 = ConceptInoculation(**common, forget_rate=0.5, rng=np.random.default_rng(s))
        g1.train(200, burn_in=30)
        high_forget.append(g1.final_fraction())
    assert np.mean(high_forget) < np.mean(no_forget)


def test_carrier_fraction_method():
    """carrier_fraction reflete l'etat courant."""
    g = ConceptInoculation(20, seed_fraction=0.25, transmission_rate=0.0,
                           rng=np.random.default_rng(0))
    assert g.carrier_fraction() == pytest.approx(0.25, abs=0.05)


# --- Gardes de validation ---


def test_invalid_n_agents_raises():
    with pytest.raises(ValueError):
        ConceptInoculation(1)


def test_invalid_seed_fraction_raises():
    with pytest.raises(ValueError):
        ConceptInoculation(30, seed_fraction=1.5)


def test_invalid_transmission_rate_raises():
    with pytest.raises(ValueError):
        ConceptInoculation(30, transmission_rate=2.0)


def test_invalid_confirmation_bias_raises():
    with pytest.raises(ValueError):
        ConceptInoculation(30, confirmation_bias=-0.1)


def test_invalid_instigator_decay_raises():
    with pytest.raises(ValueError):
        ConceptInoculation(30, instigator_decay=1.5)


def test_invalid_forget_rate_raises():
    with pytest.raises(ValueError):
        ConceptInoculation(30, forget_rate=2.0)


def test_invalid_n_rounds_raises():
    g = ConceptInoculation(30, rng=np.random.default_rng(0))
    with pytest.raises(ValueError):
        g.train(-1)


# --- Les quatre verdicts falsifiables (#7746 D2 experience D) ---


def test_transmission_grows():
    """Verdict TRANSMISSION : le concept se diffuse au-dela des graines."""
    report = transmission_grows_test(n_agents=30, n_seeds=3, seed=0)
    assert report["mean_converted_beyond_seed"] > 0
    assert report["transmits"] == 1.0


def test_confirmation_bias_throttles():
    """Verdict BIAIS DE CONFIRMATION : un biais croissant freine la diffusion."""
    report = confirmation_bias_throttles_test(n_agents=40, n_seeds=5, seed=0)
    assert report["final_at_no_bias"] > 0.9
    assert report["final_at_strong_bias"] < 0.6
    assert report["throttles"] == 1.0


def test_instigator_removal_decline():
    """Verdict DECLIN POST-INSTIGATEUR : sans la source, l'oubli fait decliner."""
    report = instigator_removal_decline_test(n_agents=40, n_seeds=4, seed=0)
    assert report["persistent_fraction"] > 0.9
    assert report["persistent_fraction"] - report["removed_fraction"] > 0.15
    assert report["declines"] == 1.0


def test_no_transmission_control():
    """Controle negatif : transmission_rate=0 ne convertit personne."""
    report = no_transmission_control_test(n_agents=30, n_seeds=3, seed=0)
    assert report["mean_converted_beyond_seed"] == 0.0
    assert report["no_transmission"] == 1.0
