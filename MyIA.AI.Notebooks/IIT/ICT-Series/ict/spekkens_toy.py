"""Case 10 (#8182) — toy bit de Spekkens : restriction épistémique ⟂ contextualité.

Le pré-enregistrement (bandes P1/P2/S1, nulls adversariaux) est scellé au
commit ``82e187e5f`` AVANT ce module — pattern case 8 (prédiction avant jouet).

Le toy bit (Spekkens, arXiv quant-ph/0401052 §IV) : 4 états ontiques, principe
d'équilibre de connaissance — la connaissance maximale est un état épistémique
pur, uniforme sur une paire. Les mesures valides sont les 3 partitions en
paires. La case teste la dissociation :

- **P1** la restriction reproduit la signature quantique de perturbation par
  mesure (P(X+|Y intercalé) = 1/2, parité QM exacte) alors que l'observateur
  « clairvoyant » (restriction levée) garde P = 1 ;
- **P2** mais le jouet reste classique sur CHSH : max S ≤ 2.00 sur
  l'énumération exhaustive des états joints, là où le singulet QM mesuré dans
  le même scénario donne 2√2 ;
- **S1** le clonage déterministe en base fixe d'un état pur inconnu échoue
  (fidélité exacte 1/3) — reproduction qualitative du no-cloning.
"""

from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

import numpy as np

# ── Ontique et états épistémiques ──

ONTIC = (1, 2, 3, 4)

PURE_STATES: tuple[frozenset[int], ...] = tuple(
    frozenset(p) for p in combinations(ONTIC, 2)
)

# ── Mesures valides : les 3 partitions en paires ──

MEASUREMENTS: dict[str, tuple[frozenset[int], frozenset[int]]] = {
    "X": (frozenset({1, 2}), frozenset({3, 4})),
    "Y": (frozenset({1, 3}), frozenset({2, 4})),
    "Z": (frozenset({1, 4}), frozenset({2, 3})),
}

OUTCOME = ("+", "-")


ONTIC_SET = frozenset(ONTIC)


def measure(state: frozenset[int], m: str) -> tuple[str, frozenset[int]]:
    """Mesure de la partition m sur un état épistémique pur.

    Probabilité d'une issue = part du support dans la cellule. Posterior =
    **cellule révélée** (règle de disturbance, Spekkens §IV) : pour une mesure
    incompatible, support ∩ cellule serait un singleton — plus que la
    connaissance maximale autorisée — donc la mesure perturbe l'ontique,
    re-randomisé dans la cellule. Pour une mesure compatible, la cellule
    révélée EST le support (pas de disturbance).
    """
    plus, minus = MEASUREMENTS[m]
    outcome = "+" if state & plus else "-"
    cell = plus if outcome == "+" else minus
    return outcome, cell


def measure_dist(
    dist: dict[frozenset[int], float], m: str
) -> dict[frozenset[int], float]:
    """Applique la mesure m à une distribution sur états épistémiques purs."""
    new: dict[frozenset[int], float] = {}
    for state, p in dist.items():
        for cell in MEASUREMENTS[m]:
            p_out = p * len(state & cell) / len(state)
            if p_out > 0:
                new[cell] = new.get(cell, 0.0) + p_out
    return new

# ── P1 : perturbation par mesure ──


def sequence_prob_exact(intermediate: str | None) -> float:
    """P(X+) exact après préparation X+ = {1,2} et mesure intercalée."""
    dist = {frozenset({1, 2}): 1.0}
    if intermediate is not None:
        dist = measure_dist(dist, intermediate)
    plus, _ = MEASUREMENTS["X"]
    return sum(p * len(st & plus) / len(st) for st, p in dist.items())


def sequence_mc(
    intermediate: str | None,
    seed: int,
    n: int = 10_000,
) -> float:
    """Monte Carlo : échantillonne l'ontique, applique l'update épistémique.

    L'observateur restreint, après l'intermédiaire, ne connaît que la cellule
    révélée par l'ontique tiré — sa probabilité prédite de X+ suit le posterior
    (cellule), conformément à la règle de disturbance.
    """
    rng = np.random.default_rng(seed)
    state = frozenset({1, 2})
    ontic_samples = rng.choice(sorted(state), size=n)
    plus_x, _ = MEASUREMENTS["X"]
    if intermediate is None:
        return float(np.isin(ontic_samples, sorted(plus_x)).mean())
    hits = 0.0
    for o in ontic_samples:
        cell = next(c for c in MEASUREMENTS[intermediate] if o in c)
        hits += len(cell & plus_x) / len(cell)
    return hits / n


def clairvoyant_control() -> float:
    """Contrôle restriction levée : l'observateur lit l'ontique sans update.

    Connaissant l'ontique ∈ {1,2}, sa prédiction X+ reste certaine à travers
    toute séquence — la signature de perturbation (1/2) est portée par la
    restriction épistémique, pas par le formalisme de mesure.
    """
    state = frozenset({1, 2})
    plus_x, _ = MEASUREMENTS["X"]
    return float(len(state & plus_x) / len(state))


# ── P2 : CHSH sur deux toy bits ──


def _local_outcome(coord: int, m: str) -> int:
    """Issue déterministe ±1 de la mesure locale m sur une coordonnée ontique."""
    plus, _ = MEASUREMENTS[m]
    return 1 if coord in plus else -1


def chsh_value(support: frozenset[tuple[int, int]], a: str, a2: str, b: str, b2: str) -> float:
    """S = E(a,b) - E(a,b') + E(a',b) + E(a',b') sur un support joint uniforme."""
    def e(m1: str, m2: str) -> float:
        acc = sum(
            _local_outcome(i, m1) * _local_outcome(j, m2) for i, j in support
        )
        return acc / len(support)

    return e(a, b) - e(a, b2) + e(a2, b) + e(a2, b2)


def chsh_exhaustive() -> dict:
    """Énumération exhaustive : C(16,4) états joints × 9 combos de settings.

    Surensemble assumé du critère de validité du papier (pré-enregistrement
    case 10) : tout viol sur un sous-ensemble non valide n'en serait pas moins
    un finding.
    """
    pairs = [(i, j) for i in ONTIC for j in ONTIC]
    settings = list(MEASUREMENTS)
    combos = [
        (a, a2, b, b2)
        for a, a2 in combinations(settings, 2)
        for b, b2 in combinations(settings, 2)
    ]
    best_s, best_state, best_combo = 0.0, None, None
    for support_tuple in combinations(pairs, 4):
        support = frozenset(support_tuple)
        for combo in combos:
            s = abs(chsh_value(support, *combo))
            if s > best_s:
                best_s, best_state, best_combo = s, support, combo
    return {
        "max_S": best_s,
        "n_states": len(list(combinations(pairs, 4))),
        "n_combos": len(combos),
        "argmax_support": sorted(sorted(t) for t in best_state),
        "argmax_combo": best_combo,
    }


# ── P2b : référence QM (singulet) ──


def qm_reference() -> dict:
    """Singulet |Ψ−⟩, observables cos σz + sin σx — CHSH canonique de Bell."""
    psi = np.array([0.0, 1.0, -1.0, 0.0]) / np.sqrt(2.0)

    def pauli_component(theta: float) -> np.ndarray:
        # observable A(θ) = cos θ σz + sin θ σx, bipartite sur un côté
        sz = np.array([[1.0, 0.0], [0.0, -1.0]])
        sx = np.array([[0.0, 1.0], [1.0, 0.0]])
        return np.cos(theta) * sz + np.sin(theta) * sx

    def kron_left(op: np.ndarray) -> np.ndarray:
        return np.kron(op, np.eye(2))

    def kron_right(op: np.ndarray) -> np.ndarray:
        return np.kron(np.eye(2), op)

    def expect(op: np.ndarray) -> float:
        return float(np.real(psi.conj() @ (op @ psi)))

    def correl(ta: float, tb: float) -> float:
        return expect(kron_left(pauli_component(ta)) @ kron_right(pauli_component(tb)))

    # angles canoniques : a=0, a'=π/2 ; b=π/4, b'=3π/4
    s = (
        correl(0.0, np.pi / 4)
        - correl(0.0, 3 * np.pi / 4)
        + correl(np.pi / 2, np.pi / 4)
        + correl(np.pi / 2, 3 * np.pi / 4)
    )
    return {"S_qm": abs(s), "S_qm_theoretical": float(np.sqrt(8.0))}


# ── S1 : clonage déterministe en base fixe ──


def no_cloning_fixed_basis() -> dict:
    """Fidélité exacte du meilleur clonage déterministe en base fixe.

    Stratégie : mesurer dans une base M ∈ {X,Y,Z}, préparer 2 copies du
    posterior. Exact-match : le clone reproduit l'état d'entrée ssi le
    posterior EST l'entrée. Pour une base fixe, seuls les 2 états de la famille
    de M sont clonés exactement ; les 4 autres reçoivent un posterior d'une
    autre famille. F = 2/6 = 1/3 exact (dérivation pré-enregistrée S1).
    """
    per_basis = {}
    for m in MEASUREMENTS:
        hits = 0
        for state in PURE_STATES:
            _, posterior = measure(state, m)
            hits += 1 if posterior == state else 0
        per_basis[m] = hits / len(PURE_STATES)
    return {
        "fidelity_per_basis": per_basis,
        "best_fidelity": max(per_basis.values()),
        "clairvoyant_fidelity": 1.0,
    }


# ── Orchestration ──

BASE_DIR = Path(__file__).parent
RESULTS_PATH = BASE_DIR / "results" / "spekkens_toy_results.json"

BANDS = {
    "P1a": (0.99, 1.01),
    "P1b_exact": (0.48, 0.52),
    "P1c": (0.99, 1.01),
    "max_S_toy": (1.99, 2.01),
    "S_qm": (2.82, 2.83),
}


def run() -> dict:
    results = {
        "case": "case 10 — restriction épistémique ⟂ contextualité (Spekkens toy)",
        "pre_registration_commit": "82e187e5f",
        "P1a_no_disturbance": sequence_prob_exact(None),
        "P1b_exact_Y": sequence_prob_exact("Y"),
        "P1b_exact_Z": sequence_prob_exact("Z"),
        "P1b_mc_5seeds": {
            m: [round(sequence_mc(m, seed), 4) for seed in (0, 1, 7, 42, 99)]
            for m in ("Y", "Z")
        },
        "P1c_clairvoyant": clairvoyant_control(),
        "P2_chsh_toy": chsh_exhaustive(),
        "P2_qm_reference": qm_reference(),
        "S1_no_cloning": no_cloning_fixed_basis(),
    }
    verdict_p1 = (
        "PASS"
        if BANDS["P1a"][0] <= results["P1a_no_disturbance"] <= BANDS["P1a"][1]
        and BANDS["P1b_exact"][0] <= results["P1b_exact_Y"] <= BANDS["P1b_exact"][1]
        and BANDS["P1c"][0] <= results["P1c_clairvoyant"] <= BANDS["P1c"][1]
        else "FAIL"
    )
    max_s = results["P2_chsh_toy"]["max_S"]
    s_qm = results["P2_qm_reference"]["S_qm"]
    if max_s > 2.01:
        verdict_p2 = "FALSIFIED (S_toy > 2.01 — la restriction générerait de la contextualité)"
    elif max_s < 1.5:
        verdict_p2 = "INCONCLUSIF (énumération creuse, plafond non atteint)"
    else:
        verdict_p2 = "PASS" if 1.99 <= max_s <= 2.01 and 2.82 <= s_qm <= 2.83 else "FAIL"
    results["verdicts"] = {"P1": verdict_p1, "P2": verdict_p2}
    results["bands"] = BANDS

    RESULTS_PATH.parent.mkdir(parents=True, exist_ok=True)
    RESULTS_PATH.write_text(
        json.dumps(results, indent=2, ensure_ascii=False), encoding="utf-8"
    )
    print(json.dumps(results, indent=2, ensure_ascii=False))
    return results


if __name__ == "__main__":
    run()
