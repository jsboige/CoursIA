"""Tests du module #7746 D2 experience B : invention de symboles (vocabulaire croissant).

Couvrent les proprietes mecaniques (invention dynamique, plafond, softmax,
extension des dimensions), les gardes de validation ET les quatre verdicts
falsifiables du banc d'essai :

1. **Croissance-a-la-mesure** — le vocabulaire croît jusqu'a ``n_states`` (et la
   coordination monte), dominant le controle sans-invention.
2. **Seuil de cout** — il existe un cout d'invention critique au-dessus duquel
   l'invention est inhibee (vocabulaire sous-optimal fige).
3. **Gain de compression** — l'invention accroît strictement l'information
   mutuelle etat-signal ( leve le plafond du goulot de vocabulaire de l'exp A).
4. **Diversite d'ontologies** — les conventions emergentes sont distinctes d'une
   graine a l'autre (convention arbitraire de Lewis).

numpy + pytest, CPU uniquement.
"""

import numpy as np
import pytest

from ict.symbol_invention import (
    InventingSignalingGame,
    vocabulary_grows_to_fit_test,
    invention_cost_tradeoff_test,
    compression_gain_test,
    ontology_diversity_test,
)


# --- Proprietes mecaniques ---


def test_invention_grows_vocabulary():
    """Avec invention active, le vocabulaire croît au-dela de sa taille initiale."""
    g = InventingSignalingGame(4, 1, temperature=0.6, invention_rate=0.05,
                               rng=np.random.default_rng(0))
    g.train(6000, anneal_to=0.15)
    assert g.final_vocab_size() > 1
    assert g.n_inventions >= 1


def test_no_invention_keeps_vocab():
    """Sans invention (rate=0), le vocabulaire reste a sa taille initiale."""
    g = InventingSignalingGame(4, 2, temperature=0.6, invention_rate=0.0,
                               rng=np.random.default_rng(0))
    g.train(3000, anneal_to=0.15)
    assert g.final_vocab_size() == 2
    assert g.n_inventions == 0


def test_max_signals_cap_respected():
    """L'invention s'arrete au plafond max_signals (anti-proliferation)."""
    g = InventingSignalingGame(4, 1, max_signals=3, temperature=0.6,
                               invention_rate=0.1, rng=np.random.default_rng(0))
    g.train(5000, anneal_to=0.15)
    assert g.final_vocab_size() <= 3


def test_invent_extends_dimensions():
    """_invent ajoute une colonne a Q_s et une ligne a Q_r (dimensions coherentes)."""
    g = InventingSignalingGame(3, 1, max_signals=3)
    assert g.Q_s.shape == (3, 1)
    assert g.Q_r.shape == (1, 3)
    assert g._invent() is True
    assert g.Q_s.shape == (3, 2)
    assert g.Q_r.shape == (2, 3)
    assert g._invent() is True
    assert g.Q_s.shape == (3, 3)
    # Plafond atteint : l'invention echoue (False), dimensions stables.
    assert g._invent() is False
    assert g.Q_s.shape == (3, 3)


def test_invented_signal_neutral_at_birth():
    """Un signal nouvellement invente demarre a initial_q (neutre, non evite)."""
    g = InventingSignalingGame(2, 1, max_signals=2, initial_q=1.0)
    g._invent()
    # La colonne du nouveau signal dans Q_s vaut initial_q partout.
    assert g.Q_s[:, 1] == pytest.approx(1.0)
    # La ligne du nouveau signal dans Q_r vaut initial_q partout.
    assert g.Q_r[1, :] == pytest.approx(1.0)


def test_initial_policy_near_uniform():
    """A l'init, la coordination est ~1/n_states (hasard, politique uniforme)."""
    g = InventingSignalingGame(4, 4, temperature=0.5, rng=np.random.default_rng(0))
    for _ in range(800):
        g.play_round(reinforce=False)
    assert g.success_rate(800) == pytest.approx(0.25, abs=0.06)


def test_play_round_returns_net_payoff():
    """play_round renvoie (etat, signal, action, paiement_net) avec types coherents."""
    g = InventingSignalingGame(3, 2, temperature=0.5, rng=np.random.default_rng(0))
    state, signal, action, net = g.play_round()
    assert 0 <= state < 3
    assert 0 <= signal < g.n_signals
    assert 0 <= action < 3
    assert net <= 1.0  # coordination (1) moins un cout eventuel


# --- Gardes de validation ---


def test_invalid_n_states_raises():
    with pytest.raises(ValueError):
        InventingSignalingGame(0, 1)


def test_invalid_n_signals_init_raises():
    with pytest.raises(ValueError):
        InventingSignalingGame(4, 0)


def test_max_signals_lt_init_raises():
    with pytest.raises(ValueError):
        InventingSignalingGame(4, 3, max_signals=2)


def test_invalid_temperature_raises():
    with pytest.raises(ValueError):
        InventingSignalingGame(4, 1, temperature=0.0)


def test_invalid_invention_rate_raises():
    with pytest.raises(ValueError):
        InventingSignalingGame(4, 1, invention_rate=-0.1)
    with pytest.raises(ValueError):
        InventingSignalingGame(4, 1, invention_rate=1.5)


def test_invalid_invention_cost_raises():
    with pytest.raises(ValueError):
        InventingSignalingGame(4, 1, invention_cost=-0.5)


def test_invalid_state_dist_raises():
    with pytest.raises(ValueError):
        InventingSignalingGame(4, 1, state_dist=[0.5, 0.5])  # mauvaise dimension
    with pytest.raises(ValueError):
        InventingSignalingGame(4, 1, state_dist=[-0.1, 0.4, 0.4, 0.3])  # negatif


# --- Les quatre verdicts falsifiables (#7746 D2 experience B) ---


def test_vocabulary_grows_to_fit():
    """Verdict CROISSANCE : vocabulaire croît vers n_states, dominant le controle."""
    report = vocabulary_grows_to_fit_test(n_states=4, seed=0)
    assert report["invented_vocab"] >= 4
    assert report["invented_success"] > 0.8
    assert report["control_vocab"] <= 1
    assert report["control_success"] < 0.5
    assert report["grew_to_fit"] == 1.0


def test_vocabulary_does_not_grow_without_invention_control():
    """Controle negatif : sans invention (rate=0), le verdict n'est pas satisfait."""
    report = vocabulary_grows_to_fit_test(n_states=4, invention_rate=0.0, seed=0)
    assert report["invented_vocab"] <= 1
    assert report["grew_to_fit"] == 0.0


def test_invention_cost_tradeoff():
    """Verdict SEUIL DE COUT : le vocabulaire final decroît quand le cout augmente."""
    report = invention_cost_tradeoff_test(n_states=6, seed=0)
    assert report["vocab_at_free_cost"] >= 6
    assert report["vocab_at_high_cost"] < 6
    v = report["vocab_per_cost"]
    assert any(v[i] > v[i + 1] for i in range(len(v) - 1))  # au moins un palier
    assert report["cost_threshold"] == 1.0


def test_compression_gain():
    """Verdict COMPRESSION : l'invention accroît strictement la MI etat-signal."""
    report = compression_gain_test(n_states=4, seed=0)
    assert report["mi_with_invention"] > 0.5 * report["max_mi"]
    assert report["mi_with_invention"] > report["mi_without_invention"]
    assert report["compression_gain"] == 1.0


def test_compression_no_gain_without_invention_control():
    """Controle negatif : sans invention, pas de gain de compression."""
    report = compression_gain_test(n_states=4, invention_rate=0.0, seed=0)
    assert report["compression_gain"] == 0.0


def test_ontology_diversity():
    """Verdict DIVERSITE : les conventions emergentes sont distinctes (Lewis)."""
    report = ontology_diversity_test(n_states=4, n_seeds=6)
    assert report["all_runs_bijections"] == 1.0
    assert report["n_distinct_conventions"] >= 2
    assert report["mean_final_success"] > 0.7
    assert report["diverse"] == 1.0


# --- Contrats mecaniques supplementaires (gaps de couverture) ---


def test_reset_restores_fresh_state():
    """reset() ramene le jeu a l'etat frais : vocabulaire a ``n_signals_init``,
    propensites uniformes (``initial_q``), historiques vides, ``n_inventions`` 0,
    joint nulle. Le contrat doit tenir apres apprentissage et inventions."""
    g = InventingSignalingGame(
        n_states=4, n_signals_init=1, invention_cost=0.0, rng=np.random.default_rng(7)
    )
    g.train(n_rounds=400)
    # Apres apprentissage : historique non vide, vocabulaire a potentiellement cru.
    assert len(g.success_history) == 400
    # reset() : retour a l'etat frais.
    g.reset()
    assert g.n_signals == g.n_signals_init
    assert g.n_inventions == 0
    assert len(g.success_history) == 0
    assert len(g.payoff_history) == 0
    assert len(g.vocab_history) == 0
    assert g.success_rate() == 0.0
    assert g.net_payoff_rate() == 0.0
    assert np.allclose(g.Q_s, g.initial_q)
    assert np.allclose(g.Q_r, g.initial_q)
    assert np.allclose(g.joint_state_signal, 0.0)


def test_train_negative_rounds_raises():
    """train(n_rounds < 0) leve ValueError (garde explicite)."""
    g = InventingSignalingGame(n_states=3, n_signals_init=2, rng=np.random.default_rng(0))
    with pytest.raises(ValueError):
        g.train(n_rounds=-5)


def test_train_zero_rounds_is_noop():
    """train(n_rounds=0) est valide (boucle vide) : aucun tour joue, aucune invention."""
    g = InventingSignalingGame(n_states=3, n_signals_init=2, rng=np.random.default_rng(0))
    g.train(n_rounds=0)
    assert len(g.success_history) == 0
    assert g.n_inventions == 0


def test_train_anneal_restores_temperature():
    """Apres train(anneal_to=t_bas), la temperature revient a sa valeur initiale
    (restoration finale) — l'annealing est transitoire, pas persistant."""
    g = InventingSignalingGame(
        n_states=3, n_signals_init=2, temperature=0.5, rng=np.random.default_rng(0)
    )
    t0 = g.temperature
    g.train(n_rounds=100, anneal_to=0.02)
    assert g.temperature == pytest.approx(t0)


def test_invent_returns_false_at_cap_without_side_effects():
    """_invent() renvoie False au plafond SANS etendre les matrices ni incrementer
    ``n_inventions``. Le garde de plafond doit etre sans effet de bord."""
    g = InventingSignalingGame(
        n_states=4, n_signals_init=2, max_signals=3, rng=np.random.default_rng(0)
    )
    # Sous le plafond : _invent() etend les matrices et renvoie True.
    assert g._invent() is True
    assert g.n_signals == 3
    assert g.n_inventions == 1
    assert g.Q_s.shape == (4, 3) and g.Q_r.shape == (3, 4)
    # Au plafond : _invent() renvoie False, ne change rien.
    assert g._invent() is False
    assert g.n_signals == 3
    assert g.n_inventions == 1
    assert g.Q_s.shape == (4, 3) and g.Q_r.shape == (3, 4)


def test_dominant_signal_per_state_empty_then_convention():
    """Sans aucun tour joue (joint nulle), ``dominant_signal_per_state`` renvoie
    -1 partout. Apres apprentissage, chaque etat porte un signal dominant valide
    et une convention emerge (au moins 2 signaux distincts)."""
    g = InventingSignalingGame(
        n_states=4, n_signals_init=1, invention_cost=0.0, rng=np.random.default_rng(0)
    )
    # Etat frais : joint nulle -> -1 partout.
    assert g.dominant_signal_per_state() == [-1, -1, -1, -1]
    g.train(n_rounds=4000, anneal_to=0.15)
    dom = g.dominant_signal_per_state()
    assert len(dom) == 4
    assert all(d >= 0 for d in dom), f"apres apprentissage chaque etat a un signal dominant, recu {dom}"
    assert len(set(dom)) >= 2, f"une convention emerge (signaux distincts), recu {dom}"
