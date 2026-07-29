"""Tests du module #7746 D2 experience E : inhibition de l'innovation (Laborit).

Couvrent les proprietes mecaniques (sous-classement du moteur B, accumulation
d'inhibition, porte d'inhibition sur l'invention), les gardes de validation ET les
quatre verdicts falsifiables du banc d'essai :

1. **Rigidification** — balayer ``inhibition_growth`` gele le vocabulaire (S-curve
   decroissante) : libre (growth=0) invente vers ``n_states``, inhibe fige sous-optimal.
2. **Impuissance apprise** — l'inhibition croît, plafonne a 1.0, et piege l'agent
   (coordination reste imparfaite).
3. **Piege permanent** — le double de cycles d'entrainement ne rescussite pas l'inhibe
   (piege structurel, pas un manque de calcul).
4. **Controle negatif** — ``inhibition_growth=0`` se comporte comme l'experience B
   (l'agent s'echappe).

numpy + pytest, CPU uniquement.
"""

import numpy as np
import pytest

from ict.inhibited_invention import (
    InhibitedInventingGame,
    inhibition_traps_rigidification_test,
    learned_helplessness_test,
    trap_persists_under_more_compute_test,
    no_inhibition_escapes_control_test,
)


# --- Proprietes mecaniques ---


def test_inherits_symbol_invention():
    """InhibitedInventingGame sous-classe InventingSignalingGame (moteur B reuse)."""
    from ict.symbol_invention import InventingSignalingGame
    assert issubclass(InhibitedInventingGame, InventingSignalingGame)


def test_zero_inhibition_behaves_like_B():
    """growth=0 = aucune inhibition : le jeu invente vers n_states (comportement B)."""
    g = InhibitedInventingGame(4, 1, temperature=0.6, invention_rate=0.1,
                               inhibition_growth=0.0, rng=np.random.default_rng(0))
    g.train(4000, anneal_to=0.15)
    assert g.final_vocab_size() >= 4
    assert g.success_rate(500) > 0.8
    assert g.final_inhibition() == pytest.approx(0.0)


def test_inhibition_accumulates_on_failure():
    """Chaque echec augmente le niveau d'inhibition (jusqu'a plafond 1.0)."""
    g = InhibitedInventingGame(4, 1, temperature=0.6, invention_rate=0.1,
                               inhibition_growth=0.5, rng=np.random.default_rng(0))
    g.train(300)
    # Avec growth=0.5 et de frequentes defaillances initiales, l'inhibition doit avoir monte.
    assert g.final_inhibition() > 0.0
    assert max(g.inhibition_history) <= 1.0  # plafond respecte


def test_inhibition_caps_at_one():
    """L'inhibition ne depasse jamais 1.0."""
    g = InhibitedInventingGame(4, 1, temperature=0.6, invention_rate=0.1,
                               inhibition_growth=2.0, rng=np.random.default_rng(0))
    g.train(500)
    assert max(g.inhibition_history) <= 1.0 + 1e-9


def test_full_inhibition_blocks_invention():
    """inhibition_level=1.0 bloque totalement l'invention (_invent renvoie False)."""
    g = InhibitedInventingGame(4, 1, max_signals=4, inhibition_growth=0.0,
                               rng=np.random.default_rng(0))
    g.inhibition_level = 1.0
    assert g._invent() is False
    assert g.n_signals == 1  # rien invente


def test_inhibition_decay_on_success():
    """Sans decay l'inhibition est non-decroissante ; avec decay il y a recuperation."""
    # Sans decay : l'inhibition ne decroit jamais (croissance seule sur echec).
    g0 = InhibitedInventingGame(4, 1, temperature=0.6, invention_rate=0.1,
                                inhibition_growth=0.1, inhibition_decay=0.0,
                                rng=np.random.default_rng(0))
    g0.train(2000, anneal_to=0.15)
    diffs0 = np.diff(g0.inhibition_history)
    assert np.all(diffs0 >= -1e-9)
    # Avec decay : au moins une recuperation (un succes a reduit l'inhibition).
    g1 = InhibitedInventingGame(4, 1, temperature=0.6, invention_rate=0.1,
                                inhibition_growth=0.1, inhibition_decay=0.3,
                                rng=np.random.default_rng(0))
    g1.train(2000, anneal_to=0.15)
    diffs1 = np.diff(g1.inhibition_history)
    assert np.any(diffs1 < -1e-9)


def test_play_round_returns_coherent_tuple():
    """play_round renvoie (etat, signal, action, net) avec types coherents."""
    g = InhibitedInventingGame(3, 2, temperature=0.5, inhibition_growth=0.1,
                               rng=np.random.default_rng(0))
    state, signal, action, net = g.play_round()
    assert 0 <= state < 3
    assert 0 <= signal < g.n_signals
    assert 0 <= action < 3


def test_inhibition_history_length_matches_rounds():
    """Un point d'inhibition par tour joue."""
    g = InhibitedInventingGame(3, 1, temperature=0.5, inhibition_growth=0.1,
                               rng=np.random.default_rng(0))
    g.train(100, anneal_to=0.15)
    assert len(g.inhibition_history) == 100


# --- Gardes de validation ---


def test_invalid_inhibition_growth_raises():
    with pytest.raises(ValueError):
        InhibitedInventingGame(4, 1, inhibition_growth=-0.1)


def test_invalid_inhibition_decay_raises():
    with pytest.raises(ValueError):
        InhibitedInventingGame(4, 1, inhibition_decay=-0.5)


# --- Les quatre verdicts falsifiables (#7746 D2 experience E) ---


def test_inhibition_rigidifies():
    """Verdict RIGIDIFICATION : growth croissant gele le vocabulaire (S-curve)."""
    report = inhibition_traps_rigidification_test(n_states=4, n_seeds=3, seed=0)
    assert report["vocab_at_free_inhibition"] >= 4
    assert report["vocab_at_max_inhibition"] <= 2.0
    assert report["rigidifies"] == 1.0


def test_learned_helplessness():
    """Verdict IMPUISSANCE APPRISE : inhibition plafonne, agent piege."""
    report = learned_helplessness_test(n_states=4, n_seeds=3, seed=0)
    assert report["inhibition_at_end"] > 0.8
    assert report["final_coord"] < 0.9
    assert report["helplessness"] == 1.0


def test_trap_persists_under_more_compute():
    """Verdict PIEGE PERMANENT : 2x cycles ne rescussite pas l'inhibe."""
    report = trap_persists_under_more_compute_test(n_states=4, n_seeds=3, seed=0)
    assert report["inhibited_coord_2n"] < 0.5
    assert report["free_coord_2n"] > 0.8
    assert report["persistent_trap"] == 1.0


def test_no_inhibition_escapes_control():
    """Controle negatif : growth=0 -> comportement B (l'agent s'echappe)."""
    report = no_inhibition_escapes_control_test(n_states=4, n_seeds=3, seed=0)
    assert report["vocab_without_inhibition"] >= 4
    assert report["coord_without_inhibition"] > 0.8
    assert report["escapes"] == 1.0
