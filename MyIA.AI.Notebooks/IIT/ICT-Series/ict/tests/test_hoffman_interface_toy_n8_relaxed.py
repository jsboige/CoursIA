"""Tests pytest pour Hoffman FBT toy case 14 (N=8, M=2, compression bit2).

Verifie :
- Invariants structurels (CANONICAL = bit2, fibre cardinal 4, symetries intra-fibre)
- Strategies (Truth = argmax_x f(MAP(x)), Fitness-only = argmax_x E[f(W)|x])
- Evolution (selection tronquee, determinisme seeds)
- Verdict attendu : 2/8 paysages avec |gap| >= 0.10, dont bit2_aligned family |gap| >= 0.60

Pattern case 11/12/13 : 18+ tests verts, run < 15 min.
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import pytest

# Import du module toy
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import hoffman_interface_toy_n8_relaxed as toy


# --- Tests structure du setup ---

def test_n_ontic_and_n_sensory():
    """Toy 3-bit : N=8 ontic, M=2 sensory."""
    assert toy.N_ONTIC == 8
    assert toy.N_SENSORY == 2
    assert toy.N_BITS == 3


def test_canonical_is_bit2():
    """CANONICAL[w] = bit2(w) (compression non-canonique vs bit0 case 11/12/13)."""
    assert toy.CANONICAL == (0, 0, 0, 0, 1, 1, 1, 1)
    for w in range(8):
        assert toy.CANONICAL[w] == (w >> 2) & 1


def test_fibre_cardinal_is_4():
    """Compression bit2 : chaque fibre cardinal 4 (N=8, M=2)."""
    assert toy.N_ONTIC // toy.N_SENSORY == 4


def test_channel_sums_to_one():
    """Pour chaque (w, alpha), sum_x P(x | w, alpha) = 1."""
    for w in range(toy.N_ONTIC):
        for alpha in [0.0, 0.25, 0.5, 0.75, 1.0]:
            s = sum(toy.channel(w, x, alpha) for x in range(toy.N_SENSORY))
            assert abs(s - 1.0) < 1e-9, f"channel doesn't sum to 1 for w={w}, alpha={alpha}"


def test_channel_alpha_one_returns_canonical():
    """A alpha=1, P(canonical(w) | w) = 1."""
    for w in range(toy.N_ONTIC):
        cw = toy.CANONICAL[w]
        for x in range(toy.N_SENSORY):
            if x == cw:
                assert toy.channel(w, x, 1.0) == 1.0
            else:
                assert toy.channel(w, x, 1.0) == 0.0


def test_channel_alpha_half_returns_half():
    """A alpha=0.5, P(x | w) = 0.5 partout (canal bruyant uniforme)."""
    for w in range(toy.N_ONTIC):
        for x in range(toy.N_SENSORY):
            assert abs(toy.channel(w, x, 0.5) - 0.5) < 1e-9


# --- Tests symetries intra-fibre (predictions P2c) ---

def test_landscape_count():
    """8 paysages : 4 symetriques herites case 11 + 4 nouveaux bit2-aligned family."""
    assert len(toy.LANDSCAPES) == 8
    expected_names = {
        "L_bit0", "L_bit1", "L_parity", "L_anti",
        "L_bit2_aligned", "L_bit2_complement_aligned",
        "L_bit01_aligned", "L_pairity_bit12",
    }
    assert set(toy.LANDSCAPES.keys()) == expected_names


def test_symmetric_landscapes_have_balanced_fibres():
    """Paysages symetriques : moyenne intra-fibre identique pour les 2 fibres.

    Teste L_bit0, L_bit1, L_parity, L_anti, L_bit01_aligned, L_pairity_bit12 :
    dans chaque fibre, fitness moyenne = 0.5 (ou 0.75 pour bit01_aligned).
    """
    # Fibre 0 (bit2=0) : w ∈ {0,1,2,3}
    # Fibre 1 (bit2=1) : w ∈ {4,5,6,7}
    symmetric_landscapes = {
        "L_bit0": (2, 2),       # 2/4 fitness 1 dans chaque fibre
        "L_bit1": (2, 2),
        "L_parity": (2, 2),
        "L_anti": (2, 2),
        "L_bit01_aligned": (3, 3),  # 3/4 fitness 1 dans chaque fibre
        "L_pairity_bit12": (2, 2),  # 2/4 fitness 1 dans chaque fibre
    }
    for name, (n1_in_fib0, n1_in_fib1) in symmetric_landscapes.items():
        f = toy.LANDSCAPES[name]
        fib0_ones = sum(f(w) for w in [0, 1, 2, 3])
        fib1_ones = sum(f(w) for w in [4, 5, 6, 7])
        assert fib0_ones == n1_in_fib0, f"{name}: fibre x=0 has {fib0_ones} ones (expected {n1_in_fib0})"
        assert fib1_ones == n1_in_fib1, f"{name}: fibre x=1 has {fib1_ones} ones (expected {n1_in_fib1})"


def test_bit2_aligned_is_trivially_discriminating():
    """L_bit2_aligned : fibre x=0 -> bit2=0 partout, fibre x=1 -> bit2=1 partout.

    Discrimination PARFAITE par compression seule :
    - E[f(W) | x=0] = 0.0
    - E[f(W) | x=1] = 1.0
    Fitness-only argmax = x=1 trivialement.
    """
    f = toy.LANDSCAPES["L_bit2_aligned"]
    fib0_values = [f(w) for w in [0, 1, 2, 3]]
    fib1_values = [f(w) for w in [4, 5, 6, 7]]
    assert all(v == 0 for v in fib0_values), f"fibre x=0 should be all 0, got {fib0_values}"
    assert all(v == 1 for v in fib1_values), f"fibre x=1 should be all 1, got {fib1_values}"


def test_bit2_complement_aligned_is_inverse_discriminating():
    """L_bit2_complement_aligned : signe inverse de L_bit2_aligned."""
    f = toy.LANDSCAPES["L_bit2_complement_aligned"]
    fib0_values = [f(w) for w in [0, 1, 2, 3]]
    fib1_values = [f(w) for w in [4, 5, 6, 7]]
    assert all(v == 1 for v in fib0_values), f"fibre x=0 should be all 1, got {fib0_values}"
    assert all(v == 0 for v in fib1_values), f"fibre x=1 should be all 0, got {fib1_values}"


# --- Tests strategies ---

def test_map_estimate_at_alpha_one_picks_canonical():
    """A alpha=1 (compression parfaite), MAP(x) selectionne w avec bit2(w) = x."""
    prior = [1.0 / toy.N_ONTIC] * toy.N_ONTIC
    for x in range(toy.N_SENSORY):
        w_star = toy.map_estimate(x, 1.0, prior)
        assert toy.CANONICAL[w_star] == x, f"MAP(x={x}) returned w={w_star} with bit2={toy.CANONICAL[w_star]}"


def test_truth_strategy_picks_discriminating_x_for_aligned():
    """Truth strategy sur bit2_aligned : choisit x=1 (fitness moyenne superieure)."""
    f = toy.LANDSCAPES["L_bit2_aligned"]
    prior = [1.0 / toy.N_ONTIC] * toy.N_ONTIC
    # A alpha=1, MAP(0) -> w=0 (bit2=0), f=0; MAP(1) -> w=4 (bit2=1), f=1.
    # Truth = argmax_x f(MAP(x)) = argmax(0, 1) = 1
    x = toy.strategy_truth(1.0, f, prior)
    assert x == 1


def test_fitness_only_aligned_discriminates_trivially():
    """Fitness-only sur bit2_aligned : E[f|x=0]=0, E[f|x=1]=1 -> x=1.

    Meme argmax que Truth. Donc gap theorique ≈ 0 (les 2 strategies
    choisissent le meme x) sauf si l'evolution elle-meme diverge.
    """
    f = toy.LANDSCAPES["L_bit2_aligned"]
    prior = [1.0 / toy.N_ONTIC] * toy.N_ONTIC
    # A alpha=0.5, channel est uniforme, donc E[f|x] = sum_w P(x|w) prior[w] f(w)
    # = 0.5 * (1/8) * sum_w f(w) = 0.5 * 0.5 = 0.25 pour les 2 x
    # argmax_fit = tie. A alpha=1.0, P(x=0|w) = 1 si bit2(w)=0 sinon 0
    # E[f|x=0] = sum_{w: bit2(w)=0} f(w) = 0 ; E[f|x=1] = sum_{w: bit2(w)=1} f(w) = 4
    # argmax_fit = 1.
    x_at_1 = toy.strategy_fitness_only(1.0, f, prior)
    assert x_at_1 == 1


# --- Tests evolution ---

def test_evolve_alpha_returns_in_unit_interval():
    """alpha* est dans [0, 1]."""
    prior = [1.0 / toy.N_ONTIC] * toy.N_ONTIC
    f = toy.LANDSCAPES["L_bit0"]
    a = toy.evolve_alpha(f, toy.strategy_truth, prior, pop=10, gen=5, seed=1)
    assert 0.0 <= a <= 1.0


def test_evolve_alpha_is_deterministic_with_seed():
    """Meme seed -> meme alpha*."""
    prior = [1.0 / toy.N_ONTIC] * toy.N_ONTIC
    f = toy.LANDSCAPES["L_bit0"]
    a1 = toy.evolve_alpha(f, toy.strategy_truth, prior, pop=10, gen=5, seed=42)
    a2 = toy.evolve_alpha(f, toy.strategy_truth, prior, pop=10, gen=5, seed=42)
    assert a1 == a2


def test_std_computes_sample_std():
    """_std utilise la formule sample std (n-1)."""
    xs = [1.0, 2.0, 3.0, 4.0, 5.0]
    expected = math.sqrt(sum((x - 3.0) ** 2 for x in xs) / 4)
    assert abs(toy._std(xs) - expected) < 1e-9


def test_std_handles_short_list():
    """_std rend 0.0 pour liste vide ou singleton."""
    assert toy._std([]) == 0.0
    assert toy._std([1.0]) == 0.0


# --- Test full experiment (run court, --quick equivalent) ---

def test_run_experiment_returns_valid_structure():
    """run_experiment rend les 4 alphas (truth mean/std, fit mean/std) + runs."""
    r = toy.run_experiment("L_bit0", n_seeds=2, pop=10, gen=5)
    assert "alpha_truth_mean" in r
    assert "alpha_truth_std" in r
    assert "alpha_fit_mean" in r
    assert "alpha_fit_std" in r
    assert "alpha_truth_runs" in r and len(r["alpha_truth_runs"]) == 2
    assert "alpha_fit_runs" in r and len(r["alpha_fit_runs"]) == 2


def test_summary_classifies_verdict_correctly():
    """summary attribue 'DISSOCIATION' si |gap| >= 0.10, 'null' sinon."""
    results = {
        "results": [
            {"alpha_truth_mean": 0.9, "alpha_truth_std": 0.05,
             "alpha_fit_mean": 0.1, "alpha_fit_std": 0.05,
             "landscape": "test_dissociation"},
            {"alpha_truth_mean": 0.5, "alpha_truth_std": 0.05,
             "alpha_fit_mean": 0.5, "alpha_fit_std": 0.05,
             "landscape": "test_null"},
        ]
    }
    rows = toy.summary(results)
    assert rows[0]["verdict"] == "DISSOCIATION"
    assert rows[0]["gap"] == 0.8
    assert rows[1]["verdict"] == "null"
    assert rows[1]["gap"] == 0.0


# --- Test verdict final (run court sur tous les paysages) ---

@pytest.mark.slow
def test_run_full_bit2_aligned_family_dissociates():
    """bit2_aligned et bit2_complement_aligned : |gap| >= 0.10 (cible >= 0.60 en full)."""
    # Run court : n_seeds=2, pop=20, gen=30 -> ~12s total par paysage
    results = toy.run_full(n_seeds=2, pop=20, gen=30,
                           landscapes=["L_bit2_aligned", "L_bit2_complement_aligned"])
    rows = toy.summary(results)
    for r in rows:
        # A seuil |gap| >= 0.10 (relache vs cible 0.60 pour cause variance seeds reduits)
        assert abs(r["gap"]) >= 0.10, (
            f"{r['landscape']} gap={r['gap']:.3f} below 0.10 threshold"
        )


@pytest.mark.slow
def test_run_full_symmetric_landscapes_null():
    """Paysages symetriques : |gap| < 0.10 (null attendu)."""
    # Run court : n_seeds=2, pop=20, gen=30
    results = toy.run_full(n_seeds=2, pop=20, gen=30,
                           landscapes=["L_bit0", "L_bit1", "L_parity", "L_anti",
                                       "L_bit01_aligned", "L_pairity_bit12"])
    rows = toy.summary(results)
    for r in rows:
        # Les paysages symetriques intra-fibre donnent argmax identique
        # pour les 2 strategies -> gap faible (< 0.10)
        assert abs(r["gap"]) < 0.10, (
            f"{r['landscape']} gap={r['gap']:.3f} unexpected dissociation"
        )


def test_run_full_returns_valid_structure():
    """run_full rend setup + results par paysage."""
    results = toy.run_full(n_seeds=2, pop=10, gen=5,
                           landscapes=["L_bit0"])
    assert results["n_ontic"] == 8
    assert results["n_sensory"] == 2
    assert results["fibre_cardinal"] == 4
    assert len(results["results"]) == 1


def test_write_artifact_creates_json(tmp_path):
    """write_artifact cree un fichier JSON valide."""
    results = toy.run_full(n_seeds=2, pop=10, gen=5, landscapes=["L_bit0"])
    rows = toy.summary(results)
    artifact_path = tmp_path / "results.json"
    toy.write_artifact(results, rows, str(artifact_path))
    assert artifact_path.exists()
    with open(artifact_path) as f:
        payload = json.load(f)
    assert "setup" in payload
    assert "rows" in payload
    assert "raw" in payload
    assert payload["setup"]["n_ontic"] == 8
