"""Case 11 (#8182) — Hoffman interface theory : Fitness-only > Truth sous compression.

Le pré-enregistrement (bandes P1-P4, nulls N1-N3, verdict attendu) est scellé au
fichier scratchpad ``hoffman_toy_design.md`` AVANT ce module — pattern case 8/10.

La case teste la dissociation Hoffman (Prakash, Stephens, Hoffman, Singh & Fields
2017, *Fitness Beats Truth in the Evolution of Perception*) en toy jouet 2-bit.
Le setup suit le §4 du papier : deux stratégies utilisent **la même** map
perceptive p, mais différent dans **comment** elles choisissent leur action.

- 4 ontic states ``W = {0, 1, 2, 3}``.
- 2 sensory states ``X = {0, 1}`` (compression 2:1, l'icon-théorie).
- Perceptual map **à dispersion** ``P(x | w)`` : c'est une chaîne markovienne
  paramétrée par ``α ∈ [0, 1]``, où ``α = P(x = canonical(w) | w)`` et
  ``canonical(w) = w % 2`` (bit0 — la compression canonique). Le reste de la
  probabilité est uniformément répartie sur l'autre x : ``P(x=1-bit0(w)|w) = 1-α``.
- Fitness landscape : ``L(w) ∈ {0, 1, 2, 3}`` (4 niveaux), **non-uniforme**.

Les **deux stratégies** (Prakash et al. 2017 §4) utilisent la même map p :

- **Truth** : ``a_truth = argmax_x f(MAP(x))``, où ``MAP(x) = argmax_w P(x|w) g(w)``
  (l'estimée MAP bayésienne de l'état du monde, puis on prend la fitness de cette
  estimée).
- **Fitness-only** : ``a_fit = argmax_x F(x)``, où ``F(x) = E[f(W) | x]``
  (l'espérance de fitness sachant la perception — pas d'estimée d'état).

Le test critique : **la map (α, structure) qui maximise la survie sous
Fitness-only est DIFFÉRENTE de la map qui maximise la survie sous Truth**.
C'est la signature toy de la dissociation Hoffman.

Concrètement : on entraîne **α** (le noise level) sur un paysage L, sous
chaque pression (Truth vs Fitness-only), et on observe les α* finaux. La
prédiction Hoffman est α*_truth < α*_fitness (Truth exige moins de bruit pour
discriminer ; Fitness-only tolère le bruit parce qu'elle moyenne).

Pour le transfert : une map entraînée sous Fitness-only sur L1 et **transférée**
à L2 (sans ré-entraînement) doit être **robuste** au changement de paysage
(parce qu'elle moyenne sur la fibre). Une map entraînée sous Truth doit **moins
bien** transférer (parce que la MAP-trackée est fragile au changement de
prédiction MAP quand le paysage change la fitness relative).
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

# ── World ──

W = (0, 1, 2, 3)
N_W = 4
N_X = 2  # compression 2:1

# 4 paysages non-uniformes
LANDSCAPES: dict[str, tuple[int, ...]] = {
    "L_bit0":   (3, 3, 0, 0),    # bit0=0 (W=0,1) à fitness haute
    "L_bit1":   (3, 0, 3, 0),    # bit1=0 (W=0,2) à fitness haute
    "L_parity": (3, 0, 0, 3),    # parity even (W=0,3) à fitness haute
    "L_anti":   (0, 3, 3, 0),    # anti-diagonale
}

# Map canonique : x = w % 2 (bit0)
CANONICAL = (0, 1, 0, 1)


# ── Map à dispersion ──

def channel(w: int, x: int, alpha: float) -> float:
    """P(x | w) sous la chaîne : alpha probabilité de suivre canonical, 1-alpha de s'inverser.

    Avec ``alpha=1`` : canal déterministe ``P(x=w%2 | w) = 1``.
    Avec ``alpha=0.5`` : bruit maximal (P(x=w%2|w) = 0.5, P(x≠w%2|w) = 0.5).
    """
    if x == CANONICAL[w]:
        return alpha
    return 1.0 - alpha


def likelihood_matrix(alpha: float) -> np.ndarray:
    """Matrice 4x2 : P(x | w)."""
    L = np.zeros((N_W, N_X))
    for w in range(N_W):
        for x in range(N_X):
            L[w, x] = channel(w, x, alpha)
    return L


# ── Stratégies ──

def map_estimate(x: int, alpha: float, w_prior: np.ndarray) -> int:
    """MAP(x) = argmax_w P(x | w) P(w)."""
    L = likelihood_matrix(alpha)
    posterior = np.array([L[w, x] * w_prior[w] for w in range(N_W)])
    return int(np.argmax(posterior))


def strategy_truth(
    alpha: float, fitness: tuple[int, ...], w_prior: np.ndarray
) -> int:
    """Truth : argmax_x f(MAP(x))."""
    map_fit = np.zeros(N_X)
    for x in range(N_X):
        w_star = map_estimate(x, alpha, w_prior)
        map_fit[x] = fitness[w_star]
    return int(np.argmax(map_fit))


def strategy_fitness_only(
    alpha: float, fitness: tuple[int, ...], w_prior: np.ndarray
) -> int:
    """Fitness-only : argmax_x E[f(W) | x]."""
    L = likelihood_matrix(alpha)
    P_x = L.T @ w_prior  # shape (N_X,)
    F_x = np.zeros(N_X)
    for x in range(N_X):
        if P_x[x] > 0:
            # E[f(W) | x] = sum_w f(w) P(x | w) P(w) / P(x)
            F_x[x] = sum(fitness[w] * L[w, x] * w_prior[w] for w in range(N_W)) / P_x[x]
        else:
            F_x[x] = -np.inf
    return int(np.argmax(F_x))


# ── Payoff en concurrence ──

def play_round(
    strategy_a: str,
    strategy_b: str,
    alpha_a: float,
    alpha_b: float,
    fitness: tuple[int, ...],
    w_prior: np.ndarray,
) -> tuple[float, float]:
    """Un round : deux territoires, payoff = fitness moyenne du territoire choisi."""
    if strategy_a == "truth":
        a_pick = strategy_truth(alpha_a, fitness, w_prior)
    elif strategy_a == "fitness":
        a_pick = strategy_fitness_only(alpha_a, fitness, w_prior)
    else:
        raise ValueError(f"unknown strategy_a: {strategy_a}")
    if strategy_b == "truth":
        b_pick = strategy_truth(alpha_b, fitness, w_prior)
    elif strategy_b == "fitness":
        b_pick = strategy_fitness_only(alpha_b, fitness, w_prior)
    else:
        raise ValueError(f"unknown strategy_b: {strategy_b}")
    # Calcul du payoff pour chaque : E[f(W) | pick]
    L = likelihood_matrix((alpha_a + alpha_b) / 2.0)  # canal moyen
    P_pick = {}
    for pick in (0, 1):
        P_pick[pick] = sum(L[w, pick] * w_prior[w] for w in range(N_W))
    def payoff(pick: int, alpha: float) -> float:
        L_local = likelihood_matrix(alpha)
        P_x = L_local.T @ w_prior
        if P_x[pick] > 0:
            return sum(fitness[w] * L_local[w, pick] * w_prior[w] for w in range(N_W)) / P_x[pick]
        return 0.0
    if a_pick == b_pick:
        # B prend l'autre territoire (2e choix)
        b_payoff = payoff(1 - b_pick, alpha_b)
    else:
        b_payoff = payoff(b_pick, alpha_b)
    a_payoff = payoff(a_pick, alpha_a)
    return a_payoff, b_payoff


# ── Évolution de α sous pression ──

def evolve_alpha(
    objective: str,
    landscape_name: str,
    seed: int,
    n_pop: int = 200,
    n_gen: int = 500,
    mutation_rate: float = 0.05,
) -> float:
    """Évolue α ∈ [0, 1] sous la pression choisie (self-play).

    objective='truth' : α qui maximise le payoff Truth (self-play)
    objective='fitness' : α qui maximise le payoff Fitness-only (self-play)
    """
    rng = np.random.default_rng(seed)
    fitness = LANDSCAPES[landscape_name]
    w_prior = np.ones(N_W) / N_W

    # Init : population = α ∈ [0, 1]
    pop = rng.uniform(0, 1, size=n_pop)

    def score(alpha: float) -> float:
        a, _ = play_round(objective, objective, alpha, alpha, fitness, w_prior)
        return a

    for gen in range(n_gen):
        fits = np.array([score(a) for a in pop])
        # Truncation top 50%
        n_survive = n_pop // 2
        order = np.argsort(fits)[::-1]
        survivors = pop[order[:n_survive]]
        offspring = survivors.copy()
        for i in range(n_survive):
            if rng.random() < mutation_rate:
                offspring[i] = rng.uniform(0, 1)
        pop[:n_survive] = survivors
        pop[n_survive:] = offspring

    final_fits = np.array([score(a) for a in pop])
    best_idx = int(np.argmax(final_fits))
    return float(pop[best_idx])


# ── Expérience ──

def run_experiment(seed: int) -> dict:
    """Train Truth et Fitness-only sur chaque paysage, mesure le transfert."""
    results = {}
    for landscape_name in LANDSCAPES:
        alpha_truth = evolve_alpha("truth", landscape_name, seed)
        alpha_fit = evolve_alpha("fitness", landscape_name, seed)
        # Transfert cross-paysage
        transfer_truth = {}
        transfer_fit = {}
        w_prior = np.ones(N_W) / N_W
        for target_landscape in LANDSCAPES:
            if target_landscape == landscape_name:
                continue
            # Fitness-only vs Truth en self-play sur le paysage cible
            _, fit_payoff = play_round(
                "fitness", "truth", alpha_fit, alpha_truth,
                LANDSCAPES[target_landscape], w_prior
            )
            truth_payoff, _ = play_round(
                "fitness", "truth", alpha_fit, alpha_truth,
                LANDSCAPES[target_landscape], w_prior
            )
            # Self-play fitness-only sur cible
            fit_self, _ = play_round(
                "fitness", "fitness", alpha_fit, alpha_fit,
                LANDSCAPES[target_landscape], w_prior
            )
            truth_self, _ = play_round(
                "truth", "truth", alpha_truth, alpha_truth,
                LANDSCAPES[target_landscape], w_prior
            )
            transfer_truth[target_landscape] = truth_self
            transfer_fit[target_landscape] = fit_self
        results[landscape_name] = {
            "alpha_truth": alpha_truth,
            "alpha_fit": alpha_fit,
            "transfer_truth": transfer_truth,
            "transfer_fit": transfer_fit,
            "self_truth": play_round("truth", "truth", alpha_truth, alpha_truth,
                                      LANDSCAPES[landscape_name], w_prior)[0],
            "self_fit": play_round("fitness", "fitness", alpha_fit, alpha_fit,
                                    LANDSCAPES[landscape_name], w_prior)[0],
        }
    return results


def run_full(n_seeds: int = 5) -> dict:
    seeds = [0, 1, 7, 42, 99][:n_seeds]
    runs = [run_experiment(s) for s in seeds]

    # Agrégats : alpha Truth vs alpha Fit par paysage
    alpha_truth_by_ln = {ln: [] for ln in LANDSCAPES}
    alpha_fit_by_ln = {ln: [] for ln in LANDSCAPES}
    for run in runs:
        for ln in LANDSCAPES:
            alpha_truth_by_ln[ln].append(run[ln]["alpha_truth"])
            alpha_fit_by_ln[ln].append(run[ln]["alpha_fit"])

    return {
        "experiment": "case_11_hoffman_interface_toy",
        "issue": 8182,
        "n_seeds": n_seeds,
        "seeds": seeds,
        "world_size": N_W,
        "sensory_size": N_X,
        "canonical_compression": list(CANONICAL),
        "landscapes": list(LANDSCAPES.keys()),
        "runs": runs,
        "aggregates": {
            "alpha_truth_by_landscape": alpha_truth_by_ln,
            "alpha_fit_by_landscape": alpha_fit_by_ln,
        },
    }


def main() -> None:
    results = run_full(n_seeds=5)
    out_dir = Path(__file__).parent / "results"
    out_dir.mkdir(exist_ok=True)
    out_path = out_dir / "hoffman_interface_toy_results.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"written: {out_path}")

    print("\n=== Verdicts sommaires (alpha moyen Truth vs Fitness par paysage) ===")
    for ln in LANDSCAPES:
        truth = results["aggregates"]["alpha_truth_by_landscape"][ln]
        fit = results["aggregates"]["alpha_fit_by_landscape"][ln]
        print(f"{ln}: α*_truth={np.mean(truth):.3f}±{np.std(truth):.3f}, "
              f"α*_fit={np.mean(fit):.3f}±{np.std(fit):.3f}, "
              f"gap={np.mean(truth) - np.mean(fit):+.3f}")


if __name__ == "__main__":
    main()
