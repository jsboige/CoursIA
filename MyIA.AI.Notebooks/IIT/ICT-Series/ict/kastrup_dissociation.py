"""Jouet « dissociation cosmique » pour la distillation Kastrup (case 18, #8182 iceberg L5 — idéalisme analytique).

La thèse formalise ELLE-MÊME sa dissociation comme déconnexion d'un graphe
d'évocation : « Ordinary phenomenal activity in cosmic consciousness can thus
be modeled as a connected directed graph » (§3.10) et « Dissociation entails
that some phenomenal contents cease to be able to evoke others » — le graphe
de la figure 3.1a devient celui de la figure 3.1b, dont les composantes sont
les alters, tandis que la figure 3.5 maintient les alters « immersed in a
common phenomenal environment ». Ce module rend la triple structure
falsifiable AU NIVEAU SIGNAL (grade C documentaire — aucune phénoménologie
n'est mesurée ni revendiquée) :

- P1 vie intérieure : chaque composante reste intégrée (corrélation
  intra-alter préservée par la dissociation) ;
- P2 vie privée : l'évocation directe inter-alters cesse (« Why can I not
  read your thoughts by simply shifting the focus of my attention? », §3.8b)
  — corrélation partielle inter-alters contrôlant l'environnement ;
- P3 immersion commune : le canal d'environnement survit à la séparation que
  le canal direct ne survit pas (figure 3.5).

Anti-duplication : case 13 = direction montante (combinaison des sujets) ;
case 18 = direction descendante (décombinaison d'un champ unifié). Case 14 =
séparabilité connectivité/cause commune pour la détection de frontière ; case
18 = réalisabilité du triple sous un calendrier de dissociation. La machinerie
de corrélation partielle est partagée, la variable manipulée et le verdict
sont distincts.

Le scellé (bandes, graines, nulls, portes, verdicts) vit dans
docs/ict/kastrup-dissociation-pre-enregistrement.md — ce module ne le
redéfinit pas, il l'exécute.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path

import numpy as np

__all__ = [
    "EvocationField",
    "fisher_mean",
    "partial_corr_given",
    "measure",
    "random_damage_W",
    "verdict",
    "run_seed",
    "TEST_SEEDS",
    "CALIB_SEEDS",
]

# Paramètres gelés par le scellé v1 (pré-enregistrement §4).
N_NODES = 120
K_ALTERS = 3
ALTER_SIZE = 40
P_IN = 0.10
ALPHA = 0.85
ENV_PHI = 0.9
BETA_LO, BETA_HI = 0.5, 1.0
SIGMA = 1.0
T_STEPS = 20_000
BURN_IN = 2_000
DISSOCIATION_GRID = (0.0, 0.5, 0.8, 1.0)
TEST_SEEDS = (0, 1, 7, 42, 99)
CALIB_SEEDS = (11, 22, 33)

# Calibration gelée par l'amendement v3 (pré-enregistrement §6ter) :
# graines disjointes 11/22/33, lectures a d = 0 uniquement.
CALIBRATED_P_OUT = 0.02
CALIBRATED_BETA_SCALE = 0.3

# Bandes du scellé v1 — une seule source de vérité pour les tests et le verdict.
BANDS = {
    "p1_ratio_min": 0.80,
    "p2_direct_max": 0.10,
    "p3_env_min": 0.30,
    "p3_dominance": 3.0,
    "null_a_direct0_min": 0.15,
    "door_intra0_min": 0.30,
}


@dataclass
class EvocationField:
    """Graphe d'évocation clusterisé + chargements d'environnement d'une graine."""

    W: np.ndarray            # row-stochastique × ALPHA, entrées inter-blocs POSITIVES au repos
    beta: np.ndarray         # chargements environnementaux par nœud
    labels: np.ndarray       # alter de chaque nœud (0..K_ALTERS-1)
    intra_mask: np.ndarray   # arêtes intra-alter
    inter_mask: np.ndarray   # arêtes inter-alters

    @classmethod
    def build(cls, seed: int, p_out: float, beta_scale: float = 1.0) -> "EvocationField":
        rng = np.random.default_rng(seed)
        labels = np.repeat(np.arange(K_ALTERS), ALTER_SIZE)
        same = labels[:, None] == labels[None, :]
        A = (rng.random((N_NODES, N_NODES)) < np.where(same, P_IN, p_out)).astype(float)
        np.fill_diagonal(A, 0.0)
        weights = rng.uniform(0.5, 1.5, size=A.shape) * A
        row_sums = weights.sum(axis=1, keepdims=True)
        # Un nœud sans arête (possible si p_out très bas) reçoit une boucle
        # unité : l'évocation y est réduite au bruit privé, jamais un NaN.
        empty = row_sums[:, 0] == 0.0
        if empty.any():
            weights[empty, empty] = 1.0
            row_sums = weights.sum(axis=1, keepdims=True)
        W = ALPHA * weights / row_sums
        beta = rng.uniform(BETA_LO, BETA_HI, size=N_NODES) * beta_scale
        return cls(W=W, beta=beta, labels=labels, intra_mask=same, inter_mask=~same)

    def W_at(self, d: float) -> np.ndarray:
        """Calendrier de dissociation : entrées inter-blocs × (1 - d), lignes renormalisées.

        Amendement v4 (pré-exécution, §6quater) : la renormalisation préserve la
        masse d'évocation de chaque nœud — couper l'évocation inter-alters ne
        doit pas assombrir les alters (mesure graine 555 : sans renorm, ratio P1
        = 0.42 pour la seule perte de masse ; avec, 0.99).
        """
        if d == 0.0:
            return self.W
        W = self.W * (1.0 - d * self.inter_mask)
        target = self.W.sum(axis=1, keepdims=True)
        cur = W.sum(axis=1, keepdims=True)
        cur[cur == 0.0] = 1.0  # noeud sans arête restante : ligne déjà nulle
        return W * (target / cur)

    def connected_at_rest(self) -> bool:
        """Contrôle mécanique : figure 3.1a — le graphe au repos est connexe.

        Fermature transitive numpy (booléens, 120 nœuds — trivial), sans
        dépendance : depuis du nœud 0, la clôture doit couvrir tout le graphe.
        """
        adj = (np.abs(self.W) > 0)
        reach = adj | adj.T | np.eye(N_NODES, dtype=bool)
        closure = reach.copy()
        for _ in range(N_NODES):
            nxt = (closure @ reach) | closure
            if nxt.sum() == closure.sum():
                break
            closure = nxt
        return bool(closure[0].all())

    def simulate(self, d: float, rng: np.random.Generator,
                 t_steps: int | None = None, burn_in: int | None = None) -> tuple[np.ndarray, np.ndarray]:
        """VAR(1) d'évocation + environnement AR(1) commun ; retourne (x, e) stationnaires."""
        t_total = T_STEPS if (t_steps is None) else t_steps
        b_total = BURN_IN if (burn_in is None) else burn_in
        W = self.W_at(d)
        e = np.empty(t_total + b_total)
        e[0] = rng.normal(0.0, math.sqrt(1.0 - ENV_PHI**2))
        noise_e = rng.normal(0.0, 1.0, size=e.shape)
        for t in range(1, e.shape[0]):
            e[t] = ENV_PHI * e[t - 1] + noise_e[t] * math.sqrt(1.0 - ENV_PHI**2)
        x = np.empty((t_total + b_total, N_NODES))
        x[0] = rng.normal(0.0, 1.0, size=N_NODES)
        eta = rng.normal(0.0, SIGMA, size=x.shape)
        for t in range(1, x.shape[0]):
            x[t] = W @ x[t - 1] + self.beta * e[t - 1] + eta[t]
        return x[b_total:], e[b_total:]


def fisher_mean(corr: np.ndarray) -> float:
    """Moyenne de corrélations via Fisher-z (bornée, non dégénérée aux extrêmes)."""
    z = np.arctanh(np.clip(corr, -0.999999, 0.999999))
    return float(np.tanh(z.mean()))


def partial_corr_given(x: np.ndarray, controls: np.ndarray) -> np.ndarray:
    """Matrice de corrélations partielles des colonnes de x contrôlant `controls`.

    Amendement v2 (pré-exécution, scellé §6bis) : l'environnement est une
    cause commune DYNAMIQUE — l'AR(1) pénètre chaque nœud à tous les décalages
    via l'évocation (beta·e(t-1), W·beta·e(t-2), ...). Contrôler le seul e(t)
    laisse les parts décalées : sur le jouet, rho_direct(1.0 | e(t) seul)
    mesurait 0.41, entièrement environnemental. `controls` porte la matrice
    [e(t), e(t-1), ..., e(t-L)] avec L couvrant la relaxation.
    """
    design = np.column_stack([np.ones(len(controls)), controls])
    coef, *_ = np.linalg.lstsq(design, x, rcond=None)
    xr = x - design @ coef
    return np.corrcoef(xr, rowvar=False)


ENV_LAGS = 60  # alpha**60 ~ 3e-5 << bruit d'échantillon 1/sqrt(T)


def env_control_matrix(e: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Retourne (e_lags, e_head) : lignes alignées de [e(t), ..., e(t-L)] et e tronqué."""
    cols = [e[ENV_LAGS - lag: e.shape[0] - lag] for lag in range(ENV_LAGS + 1)]
    return np.column_stack(cols), e[ENV_LAGS:]


def measure(field: EvocationField, d: float, rng: np.random.Generator,
            t_steps: int | None = None, burn_in: int | None = None) -> dict:
    """Observables du scellé §4 (amendement v3) à un niveau de dissociation donné.

    Inter-alters : niveau ALTER (moyenne des 40 activations de chaque alter) —
    amendement v3 (§6ter) : la partielle par paires de noeuds est structurellement
    aveugle sur ce substrat (melange row-stochastique => correlations par paires
    O(1/N), mesurees ~0.02 pour tout p_out). Intra : niveau noeuds, inchange.
    """
    x, e = field.simulate(d, rng, t_steps=t_steps, burn_in=burn_in)
    controls, _ = env_control_matrix(e)
    x_head = x[ENV_LAGS:]
    corr = np.corrcoef(x, rowvar=False)
    corr_pe_nodes = partial_corr_given(x_head, controls)
    x_agg = np.column_stack([x[:, field.labels == a].mean(axis=1) for a in range(K_ALTERS)])
    corr_pe_agg = partial_corr_given(x_agg[ENV_LAGS:], controls)
    corr_agg = np.corrcoef(x_agg, rowvar=False)
    lab = field.labels
    same = lab[:, None] == lab[None, :]
    off = ~np.eye(N_NODES, dtype=bool)
    off_agg = ~np.eye(K_ALTERS, dtype=bool)
    intra_vals = corr[same & off]
    return {
        "d": d,
        "rho_intra": fisher_mean(np.asarray(intra_vals)),
        "rho_direct_partial_env": float(np.mean(corr_pe_agg[off_agg])),
        "rho_cross_marginal": float(np.mean(corr_agg[off_agg])),
        "rho_direct_node_pairs": float(np.mean(corr_pe_nodes[~same])),
    }


def random_damage_W(field: EvocationField, rng: np.random.Generator) -> np.ndarray:
    """Null (b) : dommage aléatoire de même masse totale que la dissociation complète.

    La dissociation à d = 1 retire TOUTE la masse inter-alters ; ce bras
    retire la même masse en échantillonnant uniformément parmi TOUTES les
    arêtes (intra comprises) — le dommage sans la structure. Amendement v4 :
    lignes renormalisées à la masse d'origine, comme le bras dissociation —
    la comparaison porte sur la PLACEMENT de la masse, pas sur la masse.
    """
    W = field.W.copy()
    inter_mass = float(W[field.inter_mask].sum())
    edges = np.argwhere(W > 0)
    order = rng.permutation(len(edges))
    removed = 0.0
    for idx in order:
        i, j = edges[idx]
        w = W[i, j]
        if removed + w > inter_mass and removed > 0:
            # Dernière arête partielle : on retranche le reliquat exact.
            W[i, j] -= inter_mass - removed
            removed = inter_mass
            break
        W[i, j] = 0.0
        removed += w
        if removed >= inter_mass - 1e-12:
            break
    target = field.W.sum(axis=1, keepdims=True)
    cur = W.sum(axis=1, keepdims=True)
    cur[cur == 0.0] = 1.0
    return W * (target / cur)


def _count(passes: list[bool]) -> int:
    return sum(1 for p in passes if p)


def verdict(per_seed: list[dict], null_b_ratios: list[float]) -> dict:
    """Verdict borné du scellé §4 — aucune bande n'est relue ici, seulement BANDS."""
    n = len(per_seed)
    ratios = [s["rho_intra"] / s["rho_intra_0"] for s in per_seed]
    directs = [abs(s["rho_direct_1"]) for s in per_seed]
    envs = [s["rho_env"] for s in per_seed]
    directs_0 = [abs(s["rho_direct_0"]) for s in per_seed]
    intra0 = [s["rho_intra_0"] for s in per_seed]

    p1 = _count(r >= BANDS["p1_ratio_min"] for r in ratios) >= n - 1
    p2 = _count(dr <= BANDS["p2_direct_max"] for dr in directs) >= n - 1
    p3 = _count(
        en >= BANDS["p3_env_min"]
        and en >= BANDS["p3_dominance"] * dr
        for en, dr in zip(envs, directs)
    ) >= n - 1
    door = _count(i0 < BANDS["door_intra0_min"] for i0 in intra0) >= 3
    null_a = _count(d0 >= BANDS["null_a_direct0_min"] for d0 in directs_0) >= n - 1
    null_b = _count(nb < BANDS["p1_ratio_min"] for nb in null_b_ratios) >= n - 1

    checks = {
        "P1_alter_integrity": p1,
        "P2_privacy": p2,
        "P3_common_immersion": p3,
        "null_a_instrument_sight": null_a,
        "null_b_structure_load_bearing": null_b,
        "door_not_triggered": not door,
    }
    if door:
        outcome = "NON_CONCLUSIF_INSTRUMENT (porte : rho_intra(0) < plancher)"
    elif not null_a:
        outcome = "NON_CONCLUSIF (null a : la cause commune avale le signal direct)"
    elif not null_b:
        outcome = "NON_CONCLUSIF (null b : le dommage aleatoire passe P1, structure sans travail)"
    elif p1 and p2 and p3:
        outcome = "SUPPORTED"
    elif not p1:
        outcome = "NOT_SUPPORTED (P1 : la decombination detruit l'integration interieure)"
    elif not p2:
        outcome = "NOT_SUPPORTED (P2 : le canal direct survit a la separation complete)"
    else:
        outcome = "NOT_SUPPORTED (P3 : le canal d'environnement meurt avec le direct)"
    return {"verdict": outcome, "checks": checks}


def run_seed(seed: int, p_out: float, beta_scale: float = 1.0) -> dict:
    """Une graine complète : grille de dissociation + bras dommage aléatoire."""
    field = EvocationField.build(seed, p_out, beta_scale)
    assert field.connected_at_rest(), "contrôle mécanique : le graphe au repos doit être connexe"
    rng = np.random.default_rng(10_000 + seed)
    grid = {}
    for d in DISSOCIATION_GRID:
        grid[str(d)] = measure(field, d, rng)
    rng_nb = np.random.default_rng(20_000 + seed)
    W_rand = random_damage_W(field, rng_nb)
    damaged = EvocationField(
        W=W_rand, beta=field.beta, labels=field.labels,
        intra_mask=field.intra_mask, inter_mask=field.inter_mask,
    )
    m_rand = measure(damaged, 0.0, np.random.default_rng(30_000 + seed))
    null_b_ratio = m_rand["rho_intra"] / grid["0.0"]["rho_intra"]
    return {
        "seed": seed,
        "grid": grid,
        "null_b_random_damage": {
            "rho_intra": m_rand["rho_intra"],
            "p1_ratio": null_b_ratio,
        },
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seeds", type=int, nargs="+", default=list(TEST_SEEDS))
    parser.add_argument("--p-out", type=float, default=CALIBRATED_P_OUT,
                        help="valeur gelée par la calibration (amendement v3, §6ter)")
    parser.add_argument("--beta-scale", type=float, default=CALIBRATED_BETA_SCALE)
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args(argv)

    runs = [run_seed(s, args.p_out, args.beta_scale) for s in args.seeds]
    per_seed = [
        {
            "rho_intra": r["grid"]["1.0"]["rho_intra"],
            "rho_intra_0": r["grid"]["0.0"]["rho_intra"],
            "rho_direct_1": r["grid"]["1.0"]["rho_direct_partial_env"],
            "rho_direct_0": r["grid"]["0.0"]["rho_direct_partial_env"],
            "rho_env": r["grid"]["1.0"]["rho_cross_marginal"],
        }
        for r in runs
    ]
    result = {
        "frozen": {"p_out": args.p_out, "beta_scale": args.beta_scale,
                   "p_in": P_IN, "alpha": ALPHA, "T": T_STEPS},
        "runs": runs,
        "per_seed_summary": per_seed,
        "verdict": verdict(per_seed, [r["null_b_random_damage"]["p1_ratio"] for r in runs]),
    }
    text = json.dumps(result, indent=2, ensure_ascii=False)
    if args.out:
        args.out.write_text(text, encoding="utf-8")
        print(f"written: {args.out}")
    print(json.dumps(result["verdict"], indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
