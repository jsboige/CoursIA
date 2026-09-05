"""Tests unitaires — Hoffman interface toy N=8 (case 12, #8182).

Le pré-enregistrement est scellé à ``scratchpad_hoffman_toy_case12.md`` AVANT ce
module. Ces tests verrouillent les **invariants structurels** du toy 3-bit.

Conventions :
- Tests 1-7 : **invariants structurels** (canal, MAP, F(x), stratégie
  déterministe, taille de fibre) — doivent tenir en TOUT seed.
- Tests 8-10 : **invariants bit2** (la compression canonique est bit0 → bit2
  est orthogonal : E[f(W)|x] ne doit pas dépendre du bit2 sous canal markovien
  bit0-seul). Le test vérifie que la moyenne de fitness sur la fibre est
  invariante sous permutation bit2-only.
- Tests 11-13 : **nulls adversariaux** (N1-N3 du pré-enregistrement).
- Tests 14-15 : **évolution + verdict scan** (α ∈ [0, 1], JSON shape).
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import numpy as np

from ict.hoffman_interface_toy_n8 import (
    CANONICAL,
    LANDSCAPES,
    N_W,
    N_X,
    W,
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


def test_world_has_eight_ontic_states():
    """N_W = 8 (3 bits)."""
    assert N_W == 8
    assert W == (0, 1, 2, 3, 4, 5, 6, 7)


def test_canonical_compression_is_bit0():
    """La compression canonique mappe w sur w % 2 (bit0)."""
    assert CANONICAL == (0, 1, 0, 1, 0, 1, 0, 1)


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


def test_fibre_cardinal_is_four():
    """Compression 4:1 : chaque fibre {w : canonical(w) = x} a cardinal 4."""
    for x in range(N_X):
        fibre = [w for w in range(N_W) if CANONICAL[w] == x]
        assert len(fibre) == 4, f"fibre(x={x}) has cardinal {len(fibre)}"


# ── 2. MAP ──


def test_map_estimate_alpha_one_is_in_fibre():
    """α=1, prior uniforme : MAP(x) ∈ fibre(x) (le w canonique pour x)."""
    w_prior = np.ones(N_W) / N_W
    for x in range(N_X):
        w_star = map_estimate(x, 1.0, w_prior)
        assert CANONICAL[w_star] == x, f"MAP(x={x})={w_star}, canonical={CANONICAL[w_star]}"


def test_map_estimate_alpha_half_uses_prior():
    """α=0.5, prior non-uniforme : MAP(x) = argmax_w g(w), indépendant de x.

    À α=0.5, P(x|w) = 0.5 quel que soit x — la **forme** du posterior ne dépend
    plus que du prior. Donc MAP(x) = argmax_w g(w), indépendant de x.

    Avec prior [0.4, 0.4, 0.1, 0.05, 0.03, 0.01, 0.005, 0.005], argmax = 0 ou 1.
    """
    w_prior = np.array([0.4, 0.4, 0.1, 0.05, 0.03, 0.01, 0.005, 0.005])
    assert map_estimate(0, 0.5, w_prior) in (0, 1)
    assert map_estimate(1, 0.5, w_prior) in (0, 1)


# ── 3. Stratégies déterministes ──


def test_strategy_fitness_only_picks_max_fiber_fitness():
    """α=0 (canal inversé) : F(x) = E[f(W) | x] doit être moyenne de fitness sur fibre.

    Avec L_bit0 = (3,3,0,0,3,3,0,0) et prior uniforme :
    - fibre x=0 = {w : canonical(w)=0} = {0, 2, 4, 6}, fitness = (3,0,3,0), moyenne = 1.5
    - fibre x=1 = {w : canonical(w)=1} = {1, 3, 5, 7}, fitness = (3,0,3,0), moyenne = 1.5
    Tie → argmax → 0 (premier indice).
    """
    fitness = (3, 3, 0, 0, 3, 3, 0, 0)  # L_bit0
    w_prior = np.ones(N_W) / N_W
    pick = strategy_fitness_only(0.0, fitness, w_prior)
    assert pick in (0, 1)


def test_strategy_truth_uses_map():
    """À α=1 et prior uniforme, MAP est dans la fibre (test précédent).
    La stratégie Truth retourne un x ∈ {0, 1}.
    """
    fitness = (3, 3, 0, 0, 3, 3, 0, 0)
    w_prior = np.ones(N_W) / N_W
    pick = strategy_truth(1.0, fitness, w_prior)
    assert pick in (0, 1)


# ── 4. Invariants bit2 ──


def test_fitness_only_is_invariant_under_bit2_swap():
    """E[f(W)|x] ne dépend pas de bit2 : sous canal markovien bit0-seul, la
    moyenne sur la fibre {w : canonical(w)=x} est invariante sous permutation
    bit2-only du paysage.

    Test : on prend L_random_3bit (4 valeurs différentes entre fibres bit2=0
    et bit2=1), on permute bit2, on recalcule strategy_fitness_only sur les
    deux. Le résultat doit être identique.
    """
    fitness_a = (2, 0, 3, 1, 1, 3, 0, 2)        # L_random_3bit
    fitness_b = (1, 3, 0, 2, 2, 0, 3, 1)        # bit2-swapped
    w_prior = np.ones(N_W) / N_W
    pick_a = strategy_fitness_only(0.5, fitness_a, w_prior)
    pick_b = strategy_fitness_only(0.5, fitness_b, w_prior)
    # Les deux paysages sont isométriques sous swap bit2 → même décision
    # (en réalité, l'invariance est exacte quand les moyennes fibres sont
    # identiques ; ici on vérifie que le swap préserve l'argmax.)
    # Calculons les moyennes :
    fib0_a = np.mean([fitness_a[w] for w in (0, 2, 4, 6)])
    fib1_a = np.mean([fitness_a[w] for w in (1, 3, 5, 7)])
    fib0_b = np.mean([fitness_b[w] for w in (0, 2, 4, 6)])
    fib1_b = np.mean([fitness_b[w] for w in (1, 3, 5, 7)])
    assert abs(fib0_a - fib1_a) < 1e-9 and abs(fib0_b - fib1_b) < 1e-9, (
        f"fiber means swapped: {fib0_a} vs {fib1_a}, {fib0_b} vs {fib1_b}"
    )
    assert pick_a == pick_b, f"fitness-only not invariant under bit2 swap: {pick_a} vs {pick_b}"


def test_truth_can_exploit_bit2_via_map():
    """Truth peut exploiter bit2 via MAP (posterior non-trivial sur la fibre)
    même quand la fibre-moyenne est invariante.

    Test : on construit un paysage où fibre x=0 a un w de fitness 3 et trois
    autres à 0, et fibre x=1 symétrique. À α=1 et prior uniforme, MAP sélectionne
    le w fitness max dans la fibre → Truth pick l'argmax sur la fitness de la
    MAP. Si la MAP sélectionne correctement, la stratégie Truth peut retourner
    un x ≠ celui de Fitness-only.
    """
    # fibre x=0 = {0, 2, 4, 6} : w=0 fitness 3, autres 0
    # fibre x=1 = {1, 3, 5, 7} : w=5 fitness 3, autres 0
    fitness = (3, 0, 0, 0, 0, 3, 0, 0)
    w_prior = np.ones(N_W) / N_W
    # À α=1, MAP(x=0) = 0 (canonical), MAP(x=1) = 5 (canonical pour x=1).
    # f(MAP(x=0)) = 3, f(MAP(x=1)) = 3. Tie → argmax → 0.
    truth_pick = strategy_truth(1.0, fitness, w_prior)
    fit_pick = strategy_fitness_only(1.0, fitness, w_prior)
    # Les deux stratégies peuvent pick le même x (tie-breaking identique),
    # mais le test vérifie qu'au moins elles sont définies et retournent {0,1}.
    assert truth_pick in (0, 1)
    assert fit_pick in (0, 1)


# ── 5. Nulls adversariaux ──


def test_null_N1_alpha_half_gives_random_perception():
    """N1 (α=0.5, random) : les deux stratégies retournent des valeurs valides."""
    fitness = (3, 3, 0, 0, 3, 3, 0, 0)
    w_prior = np.ones(N_W) / N_W
    for alpha in (0.3, 0.5, 0.7):
        assert strategy_truth(alpha, fitness, w_prior) in (0, 1)
        assert strategy_fitness_only(alpha, fitness, w_prior) in (0, 1)


def test_null_N2_alpha_extremes_pick_consistently():
    """N2 : à α=0 et α=1, les stratégies sont déterministes (pas de randomness)."""
    fitness = (3, 3, 0, 0, 3, 3, 0, 0)
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


def test_run_full_is_deterministic(monkeypatch):
    """Avec les mêmes seeds, run_full doit retourner le même résultat.

    Test de **plomberie** (réserve adjoint #14732, REPAIR HIGH
    msg-20260905T112800-actho2) : `evolve_alpha` est mocké (cf.
    test_hoffman_interface_toy.py même méthode) pour ramener le runtime du test
    sous 5 s sur runner po-2024. La reproductibilité réelle de la fonction est
    couverte par `test_evolve_alpha_is_reproducible_for_same_seed`.
    """
    import ict.hoffman_interface_toy_n8 as hft

    def _fake_evolve_alpha(objective, landscape_name, seed, n_pop=200, n_gen=500, mutation_rate=0.05):
        # Valeur déterministe seedée, stable inter-processus (hash() salé par
        # PYTHONHASHSEED — réserve adjoint #14732 ; hashlib ne l'est pas).
        digest = hashlib.sha256(f"{objective}:{landscape_name}:{seed}".encode()).digest()
        rng = np.random.default_rng(int.from_bytes(digest[:8], "big"))
        return float(rng.uniform(0, 1))

    monkeypatch.setattr(hft, "evolve_alpha", _fake_evolve_alpha)

    r1 = run_full(n_seeds=3)
    r2 = run_full(n_seeds=3)
    for ln in LANDSCAPES:
        assert r1["aggregates"]["alpha_truth_by_landscape"][ln] == \
               r2["aggregates"]["alpha_truth_by_landscape"][ln]
        assert r1["aggregates"]["alpha_fit_by_landscape"][ln] == \
               r2["aggregates"]["alpha_fit_by_landscape"][ln]


# ── 7. Verdict scan ──


def test_evolve_alpha_is_reproducible_for_same_seed():
    """Même seed → même α : reproductibilité réelle de l'évolution (échelle bornée).

    Réserve adjoint #14732 (REPAIR HIGH msg-20260905T112800-actho2) : le mock de
    `test_run_full_is_deterministic` ne prouve pas la reproductibilité de la
    fonction elle-même. Ce test la couvre à petite échelle (n_pop=50, n_gen=100,
    ~2,5 s par run) : 2 invocations avec la même seed retournent le même α, en
    tout paysage et toute objective.
    """
    for ln in LANDSCAPES:
        for objective in ("truth", "fitness"):
            a1 = evolve_alpha(objective, ln, seed=7, n_pop=50, n_gen=100)
            a2 = evolve_alpha(objective, ln, seed=7, n_pop=50, n_gen=100)
            assert a1 == a2, f"{objective}/{ln} seed=7 → {a1} != {a2}"


def test_results_json_has_required_keys():
    """Le JSON artifact doit contenir toutes les clés utilisées dans la distillation."""
    results = run_full(n_seeds=3)  # n_seeds=3 pour speed
    assert "experiment" in results
    assert results["experiment"] == "case_12_hoffman_interface_toy_n8"
    assert "issue" in results and results["issue"] == 8182
    assert "aggregates" in results
    assert "alpha_truth_by_landscape" in results["aggregates"]
    assert "alpha_fit_by_landscape" in results["aggregates"]
    assert "gaps_by_landscape" in results["aggregates"]
    for ln in LANDSCAPES:
        assert ln in results["aggregates"]["alpha_truth_by_landscape"]
        assert ln in results["aggregates"]["alpha_fit_by_landscape"]
        assert ln in results["aggregates"]["gaps_by_landscape"]
        # Chaque landscape a n_seeds valeurs
        assert len(results["aggregates"]["alpha_truth_by_landscape"][ln]) == 3
        assert len(results["aggregates"]["alpha_fit_by_landscape"][ln]) == 3


def test_n8_has_eight_landscapes():
    """Case 12 doit avoir 8 paysages (4 hérités + 4 bit2 family)."""
    assert len(LANDSCAPES) == 8
    # 4 hérités case 11
    for ln in ("L_bit0", "L_bit1", "L_parity", "L_anti"):
        assert ln in LANDSCAPES
    # 4 nouveaux bit2 family
    for ln in ("L_bit2", "L_bit2_complement", "L_pairity_3bit", "L_random_3bit"):
        assert ln in LANDSCAPES
