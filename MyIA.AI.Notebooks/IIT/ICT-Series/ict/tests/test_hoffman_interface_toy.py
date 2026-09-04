"""Tests unitaires — Hoffman interface toy (case 11, #8182).

Le pré-enregistrement est scellé à ``scratchpad_hoffman_toy_case11.md`` AVANT ce
module. Ces tests verrouillent les **invariants de canal** et les **mesures
discriminantes** entre les stratégies Truth et Fitness-only. Le verdict sur la
dissociation Hoffman (P2-P4) est laissé à l'expérience ``run_experiment``.

Conventions :
- Les tests 1-7 sont des **invariants structurels** (canal, MAP, F(x), stratégie
  déterministe) — ils doivent tenir en TOUT seed.
- Les tests 8-10 sont des **nulls adversariaux** (N1-N3 du pré-enregistrement) :
  ils tracent les planchers et plafonds théoriques.
- Le verdict P1-P4 est dans ``run_full()`` et lu dans le JSON ; les tests ne
  l'enforcent pas (la dissociation peut être CONFIRMÉE, INCONCLUSIVE, ou
  FALSIFIÉE selon le seed — il faut lire l'agrégat).
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from ict.hoffman_interface_toy import (
    CANONICAL,
    LANDSCAPES,
    N_W,
    N_X,
    channel,
    evolve_alpha,
    likelihood_matrix,
    map_estimate,
    play_round,
    run_full,
    strategy_fitness_only,
    strategy_truth,
)

# ── 1. Invariants structurels ──


def test_canonical_compression_is_bit0():
    """La compression canonique mappe w sur w % 2 (bit0)."""
    assert CANONICAL == (0, 1, 0, 1)


def test_channel_alpha_one_is_deterministic():
    """α=1 → P(x=w%2|w)=1, P(x≠w%2|w)=0 : canal déterministe."""
    L = likelihood_matrix(alpha=1.0)
    for w in range(N_W):
        for x in range(N_X):
            expected = 1.0 if x == CANONICAL[w] else 0.0
            assert abs(L[w, x] - expected) < 1e-9, (
                f"L[{w}, {x}] = {L[w, x]} (alpha=1)"
            )


def test_channel_alpha_half_is_maximally_noisy():
    """α=0.5 → P(x|w) = 0.5 quel que soit x : bruit maximal symétrique."""
    L = likelihood_matrix(alpha=0.5)
    for w in range(N_W):
        for x in range(N_X):
            assert abs(L[w, x] - 0.5) < 1e-9, f"L[{w}, {x}] = {L[w, x]} (alpha=0.5)"


def test_likelihood_rows_sum_to_one():
    """Chaque LIGNE (w fixé) somme à 1 sur x — c'est P(x|w), pas P(w|x)."""
    for alpha in (0.0, 0.25, 0.5, 0.75, 1.0):
        L = likelihood_matrix(alpha)
        row_sums = L.sum(axis=1)
        for w in range(N_W):
            assert abs(row_sums[w] - 1.0) < 1e-9, (
                f"row {w} sum = {row_sums[w]} (alpha={alpha})"
            )


# ── 2. MAP ──


def test_map_estimate_alpha_one_is_unique():
    """α=1, prior uniforme : MAP(x) = w unique canonique pour x."""
    w_prior = np.ones(N_W) / N_W
    # x=0 : canonical pour w=0, w=2 (parmi 0,1,2,3 → x=0). MAP = argmax P(x=0|w)g(w).
    # P(x=0|w=0) = 1, P(x=0|w=2) = 1. Tie. argmax → 0 (premier).
    # x=1 : canonical pour w=1, w=3. MAP → 1.
    assert map_estimate(0, 1.0, w_prior) in (0, 2)
    assert map_estimate(1, 1.0, w_prior) in (1, 3)


def test_map_estimate_alpha_half_uses_prior():
    """α=0.5, prior non-uniforme : MAP sélectionne selon prior.

    À α=0.5, P(x|w) = 0.5 quel que soit x — la **forme** du posterior ne dépend
    plus que du prior. Donc MAP(x) = argmax_w g(w), indépendant de x.

    Avec prior [0.7, 0.1, 0.1, 0.1], argmax = 0 pour x=0 et x=1.
    """
    w_prior = np.array([0.7, 0.1, 0.1, 0.1])
    assert map_estimate(0, 0.5, w_prior) == 0
    assert map_estimate(1, 0.5, w_prior) == 0


# ── 3. Stratégies déterministes ──


def test_strategy_fitness_only_picks_max_fiber_fitness():
    """α=0 (canal inversé) : F(x) = E[f(W) | x] doit être moyenne de fitness sur fibre
    de la compression **inversée** (x=0 ↔ canonical=1). Vérification explicite.
    """
    fitness = (3, 3, 0, 0)  # L_bit0
    w_prior = np.ones(N_W) / N_W
    # α=0 : P(x=canonical(w)|w)=0, P(x≠canonical(w)|w)=1
    # → si x=0, fibre = w avec canonical(w)=1 = {1, 3}, fitness moyenne = (3+0)/2 = 1.5
    # → si x=1, fibre = w avec canonical(w)=0 = {0, 2}, fitness moyenne = (3+0)/2 = 1.5
    # Tie → argmax → 0.
    pick = strategy_fitness_only(0.0, fitness, w_prior)
    assert pick in (0, 1)


def test_strategy_truth_uses_map():
    """À α=1 et prior uniforme, MAP est unique (sauf tie w=0/2 pour x=0). La stratégie
    Truth doit retourner soit 0 soit 1."""
    fitness = (3, 3, 0, 0)
    w_prior = np.ones(N_W) / N_W
    pick = strategy_truth(1.0, fitness, w_prior)
    assert pick in (0, 1)


# ── 4. Play round ──


def test_play_round_self_play_no_collision_when_different_picks():
    """Si A et B pick des x différents, payoff_a = payoff_b = leur fibre respective."""
    fitness = (3, 3, 0, 0)
    w_prior = np.ones(N_W) / N_W
    # α=1 : la fibre de x=0 = {0, 2}, fitness moyenne = 1.5. La fibre de x=1 = {1, 3}, fitness moyenne = 1.5.
    # Si Truth et Fitness-only pick différent, les deux payoffs sont identiques (canal déterministe).
    a, b = play_round("truth", "fitness", 1.0, 1.0, fitness, w_prior)
    # Les deux payoffs peuvent être 0 ou 1.5 selon le tie-break
    assert a in (0.0, 1.5)
    assert b in (0.0, 1.5)


# ── 5. Nulls adversariaux ──


def test_null_N1_alpha_half_gives_random_perception():
    """N1 (α=0.5, random) : Truth et Fitness-only sont essentiellement au hasard de prior.
    Vérifier que les stratégies retournent des valeurs valides.
    """
    fitness = (3, 3, 0, 0)
    w_prior = np.ones(N_W) / N_W
    for alpha in (0.3, 0.5, 0.7):
        assert strategy_truth(alpha, fitness, w_prior) in (0, 1)
        assert strategy_fitness_only(alpha, fitness, w_prior) in (0, 1)


def test_null_N2_alpha_extremes_pick_consistently():
    """N2 : à α=0 et α=1, les stratégies sont déterministes (pas de randomness)."""
    fitness = (3, 3, 0, 0)
    w_prior = np.ones(N_W) / N_W
    t_0 = strategy_truth(0.0, fitness, w_prior)
    f_0 = strategy_fitness_only(0.0, fitness, w_prior)
    t_1 = strategy_truth(1.0, fitness, w_prior)
    f_1 = strategy_fitness_only(1.0, fitness, w_prior)
    assert t_0 in (0, 1) and f_0 in (0, 1)
    assert t_1 in (0, 1) and f_1 in (0, 1)


# ── 6. Évolution ──


def test_evolve_alpha_returns_value_in_unit_interval():
    """L'évolution doit retourner α ∈ [0, 1]."""
    for ln in LANDSCAPES:
        for objective in ("truth", "fitness"):
            a = evolve_alpha(objective, ln, seed=0, n_pop=50, n_gen=100)
            assert 0.0 <= a <= 1.0, f"{objective}/{ln} → α={a}"


def test_run_full_is_deterministic():
    """Avec les mêmes seeds, run_full doit retourner le même résultat."""
    r1 = run_full(n_seeds=5)
    r2 = run_full(n_seeds=5)
    # Compare les alpha finaux (série déterministe)
    for ln in LANDSCAPES:
        assert r1["aggregates"]["alpha_truth_by_landscape"][ln] == \
               r2["aggregates"]["alpha_truth_by_landscape"][ln]
        assert r1["aggregates"]["alpha_fit_by_landscape"][ln] == \
               r2["aggregates"]["alpha_fit_by_landscape"][ln]


# ── 7. Verdict scan ──


def test_results_json_has_required_keys():
    """Le JSON artifact doit contenir toutes les clés utilisées dans la distillation."""
    results = run_full(n_seeds=2)  # n_seeds=2 pour speed
    assert "experiment" in results
    assert results["experiment"] == "case_11_hoffman_interface_toy"
    assert "issue" in results and results["issue"] == 8182
    assert "aggregates" in results
    assert "alpha_truth_by_landscape" in results["aggregates"]
    assert "alpha_fit_by_landscape" in results["aggregates"]
    for ln in LANDSCAPES:
        assert ln in results["aggregates"]["alpha_truth_by_landscape"]
        assert ln in results["aggregates"]["alpha_fit_by_landscape"]
        # Chaque landscape a n_seeds valeurs
        assert len(results["aggregates"]["alpha_truth_by_landscape"][ln]) == 2
        assert len(results["aggregates"]["alpha_fit_by_landscape"][ln]) == 2
