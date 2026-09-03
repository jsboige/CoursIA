"""Hoffman interface theory toy N=16 / M=2 (case 13, #8182).

Suites directes des case 11 (PR #14535, N=4 null) et case 12 (PR #14544, N=8 dissociation emergente).
Passe a N=16 ontic states (4 bits), M=2 sensory states, compression 8:1.
Fibre cardinal 8 = MAP exploite structure intra-fibre largement plus riche qu'en N=8.

Setup : Prakash, Stephens, Hoffman, Singh & Fields (2017) "Fitness Beats Truth in the
Evolution of Perception", arXiv:1505.04322, section 4 (toy formel).

16 paysages (4 herites case 11 + 4 herites case 12 + 8 nouveaux bit3 family).
"""

from __future__ import annotations

import json
import math
import random
from typing import Callable, Dict, List, Sequence, Tuple

# --- Setup canonique (identique case 11/12) ---

N_BITS = 4
N_ONTIC = 1 << N_BITS  # 16 ontic states
N_SENSORY = 2

CANONICAL = tuple(w % N_SENSORY for w in range(N_ONTIC))  # bit0


def bit(w: int, k: int) -> int:
    """Return bit k of w (k=0 least significant)."""
    return (w >> k) & 1


def popcount_even(w: int) -> int:
    """Parity : 1 if popcount of w is even else 0."""
    return bin(w).count("1") % 2


def is_bit_set(w: int, k: int) -> int:
    """Alias for bit()."""
    return bit(w, k)


# --- Paysages (16 total) ---

def L_bit0(w: int) -> int:
    """Fitness = bit0 of w (compression-aligned, herite case 11/12)."""
    return bit(w, 0)


def L_bit1(w: int) -> int:
    """Fitness = bit1 (orthogonal compression, herite case 11)."""
    return bit(w, 1)


def L_parity(w: int) -> int:
    """Fitness = parite popcount(w) sur 2 bits (herite case 11)."""
    return popcount_even(w & 0b11)


def L_anti(w: int) -> int:
    """Fitness = NOT bit0 (herite case 11)."""
    return 1 - bit(w, 0)


def L_bit2(w: int) -> int:
    """Fitness = bit2 (herite case 12, bit2 family)."""
    return bit(w, 2)


def L_bit2_complement(w: int) -> int:
    """Fitness = NOT bit2 (herite case 12)."""
    return 1 - bit(w, 2)


def L_pairity_3bit(w: int) -> int:
    """Fitness = parite popcount sur 3 bits (herite case 12)."""
    return popcount_even(w & 0b111)


def L_random_3bit(w: int) -> int:
    """Pseudo-aleatoire stable sur 3 bits (herite case 12)."""
    return ((w * 7 + 3) & 0b111) % 2  # depends on bit0..2 only


# --- Nouveaux paysages bit3 family (case 13) ---

def L_bit3(w: int) -> int:
    """Fitness = bit3 (nouveau, decouvre le 4eme bit)."""
    return bit(w, 3)


def L_bit3_complement(w: int) -> int:
    """Fitness = NOT bit3."""
    return 1 - bit(w, 3)


def L_bit01(w: int) -> int:
    """Fitness = OR(bit0, bit1) -- structure 2 bits orthogonaux."""
    return bit(w, 0) | bit(w, 1)


def L_bit23(w: int) -> int:
    """Fitness = OR(bit2, bit3) -- structure 2 bits hauts."""
    return bit(w, 2) | bit(w, 3)


def L_bit01_xor(w: int) -> int:
    """Fitness = XOR(bit0, bit1) -- structure 2 bits."""
    return bit(w, 0) ^ bit(w, 1)


def L_bit3_weighted(w: int) -> int:
    """Fitness = 3*bit3 + bit0 (continuiste, expose structure lineaire)."""
    return 3 * bit(w, 3) + bit(w, 0)


def L_random_4bit_seed1(w: int) -> int:
    """Pseudo-aleatoire stable sur 4 bits (seed 1)."""
    return (w * 13 + 5) & 0b1111


def L_random_4bit_seed2(w: int) -> int:
    """Pseudo-aleatoire stable sur 4 bits (seed 2, independant seed 1)."""
    return ((w * 11 + 7) ^ 0b1010) & 0b1111


LANDSCAPES: Dict[str, Callable[[int], int]] = {
    # Herites case 11 (4)
    "L_bit0": L_bit0,
    "L_bit1": L_bit1,
    "L_parity": L_parity,
    "L_anti": L_anti,
    # Herites case 12 (4)
    "L_bit2": L_bit2,
    "L_bit2_complement": L_bit2_complement,
    "L_pairity_3bit": L_pairity_3bit,
    "L_random_3bit": L_random_3bit,
    # Nouveaux bit3 family case 13 (8)
    "L_bit3": L_bit3,
    "L_bit3_complement": L_bit3_complement,
    "L_bit01": L_bit01,
    "L_bit23": L_bit23,
    "L_bit01_xor": L_bit01_xor,
    "L_bit3_weighted": L_bit3_weighted,
    "L_random_4bit_seed1": L_random_4bit_seed1,
    "L_random_4bit_seed2": L_random_4bit_seed2,
}


# --- Canal markovien (identique case 11/12) ---

def channel(w: int, x: int, alpha: float) -> float:
    """P(x | w, alpha) : canonical(w) recu avec proba alpha."""
    canonical_w = CANONICAL[w]
    p_correct = alpha
    return p_correct if x == canonical_w else (1.0 - p_correct)


def likelihood_matrix(alpha: float) -> List[List[float]]:
    """Matrice P(x | w), dimensions [N_ONTIC][N_SENSORY] (w en ligne, x en colonne).

    Convention identique case 11/12 (Prakash et al. 2017 §4 toy).
    Chaque ligne w somme a 1 (les probabilites sur x somment a 1 pour un w fixe).
    """
    return [
        [channel(w, x, alpha) for x in range(N_SENSORY)]
        for w in range(N_ONTIC)
    ]


# --- Strategies ---

def map_estimate(
    x: int, alpha: float, prior: Sequence[float]
) -> int:
    """MAP(x) = argmax_w P(x | w, alpha) * prior[w]."""
    best_w = 0
    best_score = -math.inf
    for w in range(N_ONTIC):
        score = channel(w, x, alpha) * prior[w]
        if score > best_score:
            best_score = score
            best_w = w
    return best_w


def strategy_truth(
    alpha: float, fitness: Callable[[int], int], prior: Sequence[float]
) -> int:
    """argmax_x f(MAP(x))."""
    return max(
        range(N_SENSORY),
        key=lambda x: fitness(map_estimate(x, alpha, prior)),
    )


def strategy_fitness_only(
    alpha: float, fitness: Callable[[int], int], prior: Sequence[float]
) -> int:
    """argmax_x E[f(W) | x] = sum_w P(x | w) * prior[w] * fitness(w).

    Note : la moyenne depend des poids P(x|w) * prior[w] / sum_w' P(x|w') * prior[w'].
    Pour rendre la strategie invariante sous le facteur de normalisation,
    on prend le numerateur (l'argmax est preserve).
    """
    return max(
        range(N_SENSORY),
        key=lambda x: sum(
            channel(w, x, alpha) * prior[w] * fitness(w) for w in range(N_ONTIC)
        ),
    )


# --- Self-play / evolution (identique case 11/12, parametres ajustes) ---

def play_round(
    alpha: float,
    strategy: Callable[[float, Callable[[int], int], Sequence[float]], int],
    fitness: Callable[[int], int],
    prior: Sequence[float],
) -> float:
    """Renvoie fitness(w) ou w = strategy(x), x ~ P(x | w*, alpha), w* uniform."""
    w_star = random.randrange(N_ONTIC)
    p_x = [channel(w_star, x, alpha) for x in range(N_SENSORY)]
    x = random.choices(range(N_SENSORY), weights=p_x, k=1)[0]
    w_hat = strategy(alpha, fitness, prior)
    return fitness(w_hat)


def evolve_alpha(
    fitness: Callable[[int], int],
    strategy: Callable[[float, Callable[[int], int], Sequence[float]], int],
    prior: Sequence[float],
    pop: int = 60,
    gen: int = 150,
    alpha_init: float = 0.5,
    mutation: float = 0.05,
    tournament_k: int = 3,
    seed: int | None = None,
) -> float:
    """Selection truncée sur alpha (survie des alphas qui produisent plus de fitness)."""
    if seed is not None:
        random.seed(seed)

    population = [max(0.0, min(1.0, alpha_init + random.uniform(-0.1, 0.1)))
                  for _ in range(pop)]

    for _ in range(gen):
        scores = []
        for a in population:
            # 5 trials par individu pour stabiliser
            trial = sum(
                play_round(a, strategy, fitness, prior) for _ in range(5)
            )
            scores.append(trial / 5.0)

        # Selection : garder la moitié superieure, cloner + muter
        order = sorted(range(pop), key=lambda i: scores[i], reverse=True)
        survivors = [population[i] for i in order[: pop // 2]]
        new_pop = list(survivors)
        while len(new_pop) < pop:
            parent = random.choice(survivors)
            child = parent + random.uniform(-mutation, mutation)
            child = max(0.0, min(1.0, child))
            new_pop.append(child)
        population = new_pop

    # alpha* = moyenne des survivants
    final_scores = []
    for a in population:
        trial = sum(play_round(a, strategy, fitness, prior) for _ in range(5))
        final_scores.append(trial / 5.0)
    best_idx = max(range(pop), key=lambda i: final_scores[i])
    return population[best_idx]


def run_experiment(
    landscape_name: str,
    n_seeds: int = 5,
    pop: int = 60,
    gen: int = 150,
) -> Dict[str, object]:
    """Execute l'evolution pour les 2 strategies, retourne stats."""
    fitness = LANDSCAPES[landscape_name]
    prior = [1.0 / N_ONTIC] * N_ONTIC  # prior uniforme

    alphas_truth = []
    alphas_fit = []

    for s in range(n_seeds):
        a_t = evolve_alpha(
            fitness, strategy_truth, prior,
            pop=pop, gen=gen, seed=s * 1000 + 1,
        )
        alphas_truth.append(a_t)
        a_f = evolve_alpha(
            fitness, strategy_fitness_only, prior,
            pop=pop, gen=gen, seed=s * 1000 + 2,
        )
        alphas_fit.append(a_f)

    return {
        "landscape": landscape_name,
        "n_seeds": n_seeds,
        "pop": pop,
        "gen": gen,
        "alpha_truth_mean": sum(alphas_truth) / n_seeds,
        "alpha_truth_std": _std(alphas_truth),
        "alpha_fit_mean": sum(alphas_fit) / n_seeds,
        "alpha_fit_std": _std(alphas_fit),
        "alpha_truth_runs": alphas_truth,
        "alpha_fit_runs": alphas_fit,
    }


def _std(xs: Sequence[float]) -> float:
    if len(xs) <= 1:
        return 0.0
    mean = sum(xs) / len(xs)
    var = sum((x - mean) ** 2 for x in xs) / (len(xs) - 1)
    return math.sqrt(var)


def run_full(
    n_seeds: int = 5,
    pop: int = 60,
    gen: int = 150,
    landscapes: Sequence[str] | None = None,
) -> Dict[str, object]:
    """Execute pour tous les paysages (16 par defaut)."""
    if landscapes is None:
        landscapes = list(LANDSCAPES.keys())

    results = []
    for name in landscapes:
        r = run_experiment(name, n_seeds=n_seeds, pop=pop, gen=gen)
        results.append(r)

    return {
        "n_ontic": N_ONTIC,
        "n_sensory": N_SENSORY,
        "n_bits": N_BITS,
        "fibre_cardinal": N_ONTIC // N_SENSORY,
        "n_seeds": n_seeds,
        "pop": pop,
        "gen": gen,
        "n_landscapes": len(landscapes),
        "results": results,
    }


def summary(results: Dict[str, object]) -> List[Dict[str, object]]:
    """Calcule gap + verdict par paysage."""
    rows = []
    for r in results["results"]:
        gap = r["alpha_truth_mean"] - r["alpha_fit_mean"]
        verdict = (
            "DISSOCIATION"
            if abs(gap) >= 0.10
            else "null"
        )
        rows.append({
            "landscape": r["landscape"],
            "alpha_truth_mean": round(r["alpha_truth_mean"], 4),
            "alpha_truth_std": round(r["alpha_truth_std"], 4),
            "alpha_fit_mean": round(r["alpha_fit_mean"], 4),
            "alpha_fit_std": round(r["alpha_fit_std"], 4),
            "gap": round(gap, 4),
            "verdict": verdict,
        })
    return rows


def write_artifact(results: Dict[str, object], rows: List[Dict[str, object]], path: str) -> None:
    """Ecrit l'artefact JSON."""
    payload = {
        "setup": {
            "n_ontic": results["n_ontic"],
            "n_sensory": results["n_sensory"],
            "n_bits": results["n_bits"],
            "fibre_cardinal": results["fibre_cardinal"],
            "n_seeds": results["n_seeds"],
            "pop": results["pop"],
            "gen": results["gen"],
            "n_landscapes": results["n_landscapes"],
        },
        "rows": rows,
        "raw": results,
    }
    with open(path, "w") as f:
        json.dump(payload, f, indent=2, default=float)


if __name__ == "__main__":
    import sys

    print("Hoffman FBT toy N=16 (case 13, #8182)")
    print(f"  N_ONTIC = {N_ONTIC}, N_SENSORY = {N_SENSORY}")
    print(f"  Fibre cardinal = {N_ONTIC // N_SENSORY}")
    print(f"  Landscapes : {len(LANDSCAPES)}")
    if "--quick" in sys.argv:
        results = run_full(n_seeds=3, pop=40, gen=80)
    else:
        results = run_full(n_seeds=5, pop=60, gen=150)
    rows = summary(results)
    n_dissociation = sum(1 for r in rows if r["verdict"] == "DISSOCIATION")
    print(f"\nResultats ({len(rows)} paysages) :")
    for r in rows:
        print(
            f"  {r['landscape']:25s} "
            f"truth = {r['alpha_truth_mean']:.3f} ± {r['alpha_truth_std']:.3f}  "
            f"fit = {r['alpha_fit_mean']:.3f} ± {r['alpha_fit_std']:.3f}  "
            f"gap = {r['gap']:+.3f}  {r['verdict']}"
        )
    print(f"\nScore FBT : {n_dissociation}/{len(rows)} paysages avec gap |>= 0.10")
