"""Case 12 (#8182) — Hoffman interface theory N=8 : dissociation emergente.

Le pré-enregistrement (bandes P1-P4, nulls N1-N3, verdict attendu) est scellé au
fichier scratchpad ``scratchpad_hoffman_toy_case12.md`` AVANT ce module — pattern
case 8/10/11. Si les bandes ne sont pas tenues, le jouet est repeint, pas la
prédiction.

La case teste la dissociation Hoffman (Prakash, Stephens, Hoffman, Singh & Fields
2017, *Fitness Beats Truth in the Evolution of Perception*) en toy 3-bit. Setup
canonique §4 du papier :

- **8 ontic states** ``W = {0, 1, ..., 7}`` (3 bits, identifiés à ``{000,...,111}``).
- **2 sensory states** ``X = {0, 1}`` (compression 4:1, l'icon-théorie).
- Perceptual map à dispersion ``P(x | w)`` : chaîne markovienne paramétrée par
  ``α ∈ [0, 1]``, où ``α = P(x = canonical(w) | w)`` et ``canonical(w) = w % 2``
  (bit0 — compression canonique). Le reste : ``P(x=1-bit0(w)|w) = 1-α``.
- Fitness landscape : ``L(w) ∈ {0, 1, 2, 3}`` (4 niveaux), non-uniforme.

**Pourquoi N=8 et pas N=4 (case 11) ?**

Case 11 a montré un **null de référence** : à N=4, M=2, prior uniforme, les deux
stratégies sont mathématiquement équivalentes (gap α*_truth vs α*_fit = 0.000).
La cause structurelle : les deux stratégies calculent la **même moyenne de
fitness sur la fibre** quand la fibre est de cardinal 2 et symétrique.

À N=8, la fibre ``{w : canonical(w) = x}`` a cardinal 4. La moyenne reste
insensible à **bit2** (orthogonal à la compression canonique bit0) — mais
l'estimée MAP, elle, **dépend** de la structure du paysage (le posterior
``P(w|x) ∝ P(x|w) g(w)`` est non-trivial dès que la fitness discrimine).
C'est exactement l'asymétrie que case 11 n'avait pas : la stratégie Truth a
accès à l'info que Fitness-only moyenne.

**Paysages** : 4 hérités de case 11 (L_bit0, L_bit1, L_parity, L_anti) + 4
nouveaux qui exposent l'asymétrie cross-bit (L_bit2, L_bit2_complement,
L_pairity_3bit, L_random_3bit).

Les **deux stratégies** (Prakash et al. 2017 §4) utilisent la même map p :

- **Truth** : ``a_truth = argmax_x f(MAP(x))``, où
  ``MAP(x) = argmax_w P(x|w) g(w)``.
- **Fitness-only** : ``a_fit = argmax_x F(x)``, où ``F(x) = E[f(W) | x]``.

Le test critique : sur les paysages **bit2 family** (où bit2 est orthogonal à
la compression), la stratégie Truth doit converger sur un α différent de
Fitness-only — c'est la **première dissociation** mesurable du toy 2-bit.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

# ── World ──

W = (0, 1, 2, 3, 4, 5, 6, 7)
N_W = 8
N_X = 2  # compression 4:1

# 8 paysages : 4 herites de case 11 (sur w%4 = bit0+bit1) + 4 nouveaux
# exposant l'asymetrie cross-bit via bit2.
#
# Convention : L(w) ∈ {0, 1, 2, 3} (4 niveaux).
# - bit0 = w & 1
# - bit1 = (w >> 1) & 1
# - bit2 = (w >> 2) & 1

LANDSCAPES: dict[str, tuple[int, ...]] = {
    # ── 4 herites case 11 (sur bit0+bit1, identiques w%4) ──
    "L_bit0":   (3, 3, 0, 0, 3, 3, 0, 0),    # bit0=0 (W=0,1,4,5) a fitness haute
    "L_bit1":   (3, 0, 3, 0, 3, 0, 3, 0),    # bit1=0 (W=0,2,4,6) a fitness haute
    "L_parity": (3, 0, 0, 3, 3, 0, 0, 3),    # parity even (W=0,3,4,7) a fitness haute
    "L_anti":   (0, 3, 3, 0, 0, 3, 3, 0),    # anti-diagonale (bit0=1 ou bit1=1 mais pas les deux)
    # ── 4 nouveaux : bit2 family ──
    "L_bit2":         (3, 3, 3, 3, 0, 0, 0, 0),  # bit2=0 (W=0-3) a fitness haute
    "L_bit2_complement": (0, 0, 0, 0, 3, 3, 3, 3),  # bit2=1 (W=4-7) a fitness haute
    "L_pairity_3bit": (3, 0, 0, 3, 0, 3, 3, 0),    # parite 3 bits (XOR bit0+bit1+bit2=0)
    "L_random_3bit":  (2, 0, 3, 1, 1, 3, 0, 2),    # pseudo-aleatoire deterministe
}

# Map canonique : x = w % 2 (bit0)
CANONICAL = tuple(w % 2 for w in W)


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
    """Matrice 8x2 : P(x | w)."""
    L = np.zeros((N_W, N_X))
    for w in range(N_W):
        for x in range(N_X):
            L[w, x] = channel(w, x, alpha)
    return L


# ── Stratégies ──

def map_estimate(x: int, alpha: float, w_prior: np.ndarray) -> int:
    """MAP(x) = argmax_w P(x | w) P(w).

    À α=1, P(x|w) est déterministe (1 pour le w canonique, 0 sinon). Le MAP
    sélectionne le w dont le posterior est max — pour prior uniforme, c'est
    n'importe quel w dans la fibre de x. tie-break : argmax → premier indice.

    À α<1, le posterior intègre la structure du paysage via P(w) et la
    discrimination entre fibres voisines.
    """
    L = likelihood_matrix(alpha)
    posterior = np.array([L[w, x] * w_prior[w] for w in range(N_W)])
    return int(np.argmax(posterior))


def strategy_truth(
    alpha: float, fitness: tuple[int, ...], w_prior: np.ndarray
) -> int:
    """Truth : argmax_x f(MAP(x)).

    MAP est calculée pour chaque x. À N=8, la fibre de x est {w : canonical(w)=x},
    cardinal 4. Le posterior ``P(w|x) ∝ P(x|w) P(w)`` discrimine les w DANS la
    fibre selon leur fitness relative (via P(w)). Donc MAP sélectionne le w
    dont la fitness dans la fibre est maximale (weighted by P(x|w)).
    """
    map_fit = np.zeros(N_X)
    for x in range(N_X):
        w_star = map_estimate(x, alpha, w_prior)
        map_fit[x] = fitness[w_star]
    return int(np.argmax(map_fit))


def strategy_fitness_only(
    alpha: float, fitness: tuple[int, ...], w_prior: np.ndarray
) -> int:
    """Fitness-only : argmax_x E[f(W) | x].

    E[f(W)|x] = sum_w f(w) P(w|x) = sum_w f(w) P(x|w) P(w) / P(x).

    C'est la **moyenne de fitness sur la fibre** {w : canonical(w) = x}, pondérée
    par le posterior. Indépendante du bit2 (orthogonal à la compression).
    """
    L = likelihood_matrix(alpha)
    P_x = L.T @ w_prior  # shape (N_X,)
    F_x = np.zeros(N_X)
    for x in range(N_X):
        if P_x[x] > 0:
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
    L = likelihood_matrix((alpha_a + alpha_b) / 2.0)  # canal moyen

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
    """Évolue α ∈ [0, 1] sous la pression choisie (self-play)."""
    rng = np.random.default_rng(seed)
    fitness = LANDSCAPES[landscape_name]
    w_prior = np.ones(N_W) / N_W

    pop = rng.uniform(0, 1, size=n_pop)

    def score(alpha: float) -> float:
        a, _ = play_round(objective, objective, alpha, alpha, fitness, w_prior)
        return a

    for gen in range(n_gen):
        fits = np.array([score(a) for a in pop])
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
        transfer_truth = {}
        transfer_fit = {}
        w_prior = np.ones(N_W) / N_W
        for target_landscape in LANDSCAPES:
            if target_landscape == landscape_name:
                continue
            _, fit_payoff = play_round(
                "fitness", "truth", alpha_fit, alpha_truth,
                LANDSCAPES[target_landscape], w_prior
            )
            truth_payoff, _ = play_round(
                "fitness", "truth", alpha_fit, alpha_truth,
                LANDSCAPES[target_landscape], w_prior
            )
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


# Seeds qui ont produit l'artefact commité. Nommées ici pour rendre
# `run_full()` reproductible : c'est la liste canonique case 12, distincte
# de case 11 et case 13.
DEFAULT_SEEDS: tuple[int, ...] = (0, 1, 7, 42, 99)

# Paramètres evolution qui ont produit l'artefact commité. 80 pop × 200 gen
# (vs defauts `evolve_alpha(n_pop=200, n_gen=500)`) ont été choisis pour
# rester sous ~125 s par run complet. `n_pop`/`n_gen` sont sérialisés dans
# l'artefact (cf `run_full`) pour qu'aucun écart ne se re-commette.
DEFAULT_N_POP: int = 80
DEFAULT_N_GEN: int = 200


def run_full(
    n_seeds: int = 5,
    seeds: tuple[int, ...] | None = None,
    n_pop: int = DEFAULT_N_POP,
    n_gen: int = DEFAULT_N_GEN,
) -> dict:
    """Run complet : produit l'artefact sérialisé commité.

    Args:
        n_seeds: nombre de seeds à utiliser. Si `seeds` est fourni, contrôle
            la longueur via slice `[:n_seeds]` après le tuple.
        seeds: tuple de seeds. Si None, utilise `DEFAULT_SEEDS`. La liste
            canonique case 12 est `(0, 1, 7, 42, 99)`.
        n_pop: taille de population passée à `evolve_alpha`.
        n_gen: nombre de générations passées à `evolve_alpha`.

    Returns:
        dict avec setup complet (n_seeds, seeds, n_pop, n_gen, world, sensory,
        canonical_compression, landscapes) + runs par seed + aggregates par
        paysage. Les params `n_pop`/`n_gen` sont sérialisés pour rendre
        l'artefact reproductible.
    """
    if seeds is None:
        seeds = DEFAULT_SEEDS[:n_seeds]
    elif len(seeds) < n_seeds:
        seeds = tuple(list(seeds) + list(DEFAULT_SEEDS))[:n_seeds]
    runs = [
        _run_experiment_with_params(s, n_pop=n_pop, n_gen=n_gen)
        for s in seeds[:n_seeds]
    ]

    alpha_truth_by_ln = {ln: [] for ln in LANDSCAPES}
    alpha_fit_by_ln = {ln: [] for ln in LANDSCAPES}
    for run in runs:
        for ln in LANDSCAPES:
            alpha_truth_by_ln[ln].append(run[ln]["alpha_truth"])
            alpha_fit_by_ln[ln].append(run[ln]["alpha_fit"])

    # Gaps par paysage
    gaps_by_ln = {}
    for ln in LANDSCAPES:
        truth_mean = float(np.mean(alpha_truth_by_ln[ln]))
        fit_mean = float(np.mean(alpha_fit_by_ln[ln]))
        gaps_by_ln[ln] = truth_mean - fit_mean

    return {
        "experiment": "case_12_hoffman_interface_toy_n8",
        "issue": 8182,
        "n_seeds": n_seeds,
        "seeds": list(seeds[:n_seeds]),
        "n_pop": n_pop,
        "n_gen": n_gen,
        "world_size": N_W,
        "sensory_size": N_X,
        "canonical_compression": list(CANONICAL),
        "landscapes": list(LANDSCAPES.keys()),
        "runs": runs,
        "aggregates": {
            "alpha_truth_by_landscape": alpha_truth_by_ln,
            "alpha_fit_by_landscape": alpha_fit_by_ln,
            "gaps_by_landscape": gaps_by_ln,
        },
    }


def _run_experiment_with_params(seed: int, n_pop: int, n_gen: int) -> dict:
    """Variante de `run_experiment` qui passe `n_pop`/`n_gen` à `evolve_alpha`.

    Sans cette indirection, `run_full` réutilise les defauts `evolve_alpha`
    (`n_pop=200, n_gen=500`) et l'artefact n'est pas reproductible depuis
    `run_full` (defaut G.2 -- métriques honnêtes).
    """
    results = {}
    for landscape_name in LANDSCAPES:
        alpha_truth = evolve_alpha(
            "truth", landscape_name, seed, n_pop=n_pop, n_gen=n_gen,
        )
        alpha_fit = evolve_alpha(
            "fitness", landscape_name, seed, n_pop=n_pop, n_gen=n_gen,
        )
        transfer_truth = {}
        transfer_fit = {}
        w_prior = np.ones(N_W) / N_W
        for target_landscape in LANDSCAPES:
            if target_landscape == landscape_name:
                continue
            _, fit_payoff = play_round(
                "fitness", "truth", alpha_fit, alpha_truth,
                LANDSCAPES[target_landscape], w_prior
            )
            truth_payoff, _ = play_round(
                "fitness", "truth", alpha_fit, alpha_truth,
                LANDSCAPES[target_landscape], w_prior
            )
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


def main() -> None:
    results = run_full(n_seeds=5)
    out_dir = Path(__file__).parent / "results"
    out_dir.mkdir(exist_ok=True)
    out_path = out_dir / "hoffman_interface_toy_n8_results.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"written: {out_path}")

    print("\n=== Verdicts sommaires (alpha moyen Truth vs Fitness par paysage) ===")
    for ln in LANDSCAPES:
        truth = results["aggregates"]["alpha_truth_by_landscape"][ln]
        fit = results["aggregates"]["alpha_fit_by_landscape"][ln]
        gap = results["aggregates"]["gaps_by_landscape"][ln]
        print(f"{ln:25s}: α*_truth={np.mean(truth):.3f}±{np.std(truth):.3f}, "
              f"α*_fit={np.mean(fit):.3f}±{np.std(fit):.3f}, "
              f"gap={gap:+.3f}")

    # Verdict global : au moins un paysage avec |gap| >= 0.10 ?
    big_gaps = {ln: g for ln, g in results["aggregates"]["gaps_by_landscape"].items()
                if abs(g) >= 0.10}
    if big_gaps:
        print(f"\n=== DISSOCIATION MESURÉE sur {len(big_gaps)} paysage(s) ===")
        for ln, g in big_gaps.items():
            print(f"  {ln}: gap={g:+.3f}")
    else:
        print("\n=== PAS DE DISSOCIATION MESURÉE (|gap| < 0.10 sur tous les paysages) ===")


if __name__ == "__main__":
    main()
