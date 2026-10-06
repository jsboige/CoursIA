"""Dehaene F2 — dissociation self-model vs K-features (test proxy, CPU-only).

Issue #19343 (T3 Dehaene F2, Part of #8182). Test proxy : on mesure la
dispersion de la discrimination inter-catégories (code_python vs prose_fr)
sur les traces ICT-21 disponibles localement, en faisant varier le K de
la signature (top-K des features d'activation moyenne).

F2 Dehaene prédit que la conscience = accès au global workspace, et que le
self-model est une SORTIE du workspace. Si on réduit l'accès (K-features
plus petit), la discrimination (self/other, ou catégorie A vs B) doit
CHUTER proportionnellement à K.

Falsification (proxy) : la discrimination inter-catégories reste
CONSTANTE à K variable, donc la signature d'accès est invariante à la
résolution (proxy pour F2 falsifié sur ce substrat).

Le test direct (K-sweep sur case 4 self/other) requiert les traces des
bras principaux de self_model_minimal, qui sont GPU-only (Tell c.8236
RECOVERABLE-MACHINE — po-2023/po-2024 GPU 24+ Go). Ce module pose la
méthodologie et un proxy mesurable localement.

References
----------
S. Dehaene, *Consciousness and the Brain*, Johns Hopkins University Press
2014. Pré-enregistrement F2 : `docs/ict/dissociations-matrix.md` §F2.
"""
from __future__ import annotations

import json
import math
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

from .sae_traces import densify, mean_activation_by_set


@dataclass
class DissociationK:
    """Résultat du sweep K sur la discrimination neutre (obj1/obj2)."""

    p1_by_k: dict[int, float]
    p2_by_k: dict[int, float]
    r_by_k: dict[int, float]
    log_r_range: float  # max(log(r)) - min(log(r)), proxy de constance
    verdict: str
    kill_details: list[str] = field(default_factory=list)


@dataclass
class NullResult:
    """Résultat du témoin nul (permutation + Dirichlet)."""

    null_kind: str  # "shape_perm" | "dirichlet" | "paired_split"
    n_perm: int
    log_range_distribution: list[float]
    mean: float
    std: float
    p_value: float  # fraction de log_range nulls >= observé
    seed: int


def _log_range(r_by_k: dict[int, float]) -> float:
    """log-range = max(log r) - min(log r) sur les valeurs finies > 0."""
    valid = [r for r in r_by_k.values() if math.isfinite(r) and r > 0]
    if not valid:
        return float("inf")
    log_r = [math.log(r) for r in valid]
    return max(log_r) - min(log_r)


def dissociation_f2_null(category_means: dict[str, np.ndarray], *,
                          cat_a: str = "code_python",
                          cat_b: str = "prose_fr",
                          k_grid: tuple[int, ...] = (1, 2, 4, 8, 16, 32, 64),
                          n_perm: int = 100,
                          seed: int = 0) -> NullResult:
    """Témoin nul par permutation de composantes (forme préservée, features mêlées).

    Pour chaque itération, on permute uniformément les composantes de
    `cat_a`, on renormalise (le vecteur reste une distribution qui
    somme à 1, avec la même courbe de Lorenz), et on calcule R(K)
    sur (cat_a, cat_a_perm). Le log_range null est la distribution
    sous H0 : « la forme de la distribution seule explique la
    variation R(K) ». C'est le témoin proposé par ai-01 sur la CR
    de #19345 (permutation au niveau des comptes).

    C'est un témoin *shape-matched* : il a la même sparsity profile
    que cat_a, donc R(K) → 1 reste vrai à K → d_sae, mais
    l'évolution de R(K) sur le K-grid dépend de la concentration.
    Si le log_range observé (cat_a vs cat_b) est dans la queue
    supérieure de ce témoin, alors l'écart cat_a/cat_b dépasse
    l'écart entre deux distributions de même forme.
    """
    if cat_a not in category_means:
        return NullResult("shape_perm", n_perm, [], float("nan"),
                          float("nan"), float("nan"), seed)
    act_a = category_means[cat_a].astype(np.float64)
    d_sae = act_a.shape[0]
    kk_grid = [min(k, d_sae) for k in k_grid]
    rng = np.random.default_rng(seed)
    null_log_ranges: list[float] = []
    for _ in range(n_perm):
        perm = rng.permutation(d_sae)
        act_a_perm = act_a[perm]
        act_a_perm = act_a_perm / act_a_perm.sum()
        p1_by_k = {}
        p2_by_k = {}
        r_by_k = {}
        for k, kk in zip(k_grid, kk_grid):
            idx_a = np.argsort(act_a)[::-1][:kk]
            idx_b = np.argsort(act_a_perm)[::-1][:kk]
            p1 = float(act_a[idx_a].sum())
            p2 = float(act_a_perm[idx_b].sum())
            p1_by_k[k] = p1
            p2_by_k[k] = p2
            r_by_k[k] = float(p1 / p2) if p2 > 0 else float("nan")
        null_log_ranges.append(_log_range(r_by_k))
    mean = float(np.mean(null_log_ranges)) if null_log_ranges else float("nan")
    std = float(np.std(null_log_ranges)) if null_log_ranges else float("nan")
    return NullResult("shape_perm", n_perm, null_log_ranges, mean, std,
                      float("nan"), seed)


def dirichlet_null(category_means: dict[str, np.ndarray], *,
                   cat_a: str = "code_python",
                   cat_b: str = "prose_fr",
                   k_grid: tuple[int, ...] = (1, 2, 4, 8, 16, 32, 64),
                   n_perm: int = 100,
                   seed: int = 1) -> NullResult:
    """Témoin nul Dirichlet(1) — vecteur sans structure (uniforme sur simplex).

    Pour chaque itération, on génère un vecteur ~Dirichlet(1) de
    dimension d_sae (= distribution « plate » sans aucune sparsity)
    et on calcule R(K) sur (cat_a, random_dirichlet). Le log_range
    null est la distribution sous H0 : « la variation R(K) est
    entièrement expliquée par l'asymétrie de concentration entre
    une distribution structurée et une distribution plate ».

    C'est un témoin *shape-asymmetric* : il borne la variabilité
    R(K) face à l'absence totale de structure. Si le log_range
    observé (cat_a vs cat_b) est dans la queue supérieure de ce
    témoin, alors la variation observée n'est pas juste l'effet
    d'une distribution structurée vs une distribution plate.
    """
    if cat_a not in category_means:
        return NullResult("dirichlet", n_perm, [], float("nan"),
                          float("nan"), float("nan"), seed)
    act_a = category_means[cat_a].astype(np.float64)
    d_sae = act_a.shape[0]
    kk_grid = [min(k, d_sae) for k in k_grid]
    rng = np.random.default_rng(seed)
    null_log_ranges: list[float] = []
    for _ in range(n_perm):
        random_vec = rng.dirichlet(np.ones(d_sae))
        p1_by_k = {}
        p2_by_k = {}
        r_by_k = {}
        for k, kk in zip(k_grid, kk_grid):
            idx_a = np.argsort(act_a)[::-1][:kk]
            idx_b = np.argsort(random_vec)[::-1][:kk]
            p1 = float(act_a[idx_a].sum())
            p2 = float(random_vec[idx_b].sum())
            p1_by_k[k] = p1
            p2_by_k[k] = p2
            r_by_k[k] = float(p1 / p2) if p2 > 0 else float("nan")
        null_log_ranges.append(_log_range(r_by_k))
    mean = float(np.mean(null_log_ranges)) if null_log_ranges else float("nan")
    std = float(np.std(null_log_ranges)) if null_log_ranges else float("nan")
    return NullResult("dirichlet", n_perm, null_log_ranges, mean, std,
                      float("nan"), seed)


def _p_value(null_log_ranges: list[float], observed: float) -> float:
    """p-value unilatérale : fraction de nulls >= observé.

    Convention : la queue supérieure (>=) est la zone d'« au moins
    aussi extrême que l'observé ». Pour le test F2, l'hypothèse
    alternative est « le log_range observé dépasse le bruit de fond »,
    donc on regarde la queue supérieure du témoin nul.
    """
    if not null_log_ranges or not math.isfinite(observed):
        return float("nan")
    extreme = sum(1 for x in null_log_ranges if x >= observed)
    return extreme / len(null_log_ranges)


def _verdict_with_null(log_range: float, *,
                       shape_perm: NullResult,
                       dirichlet: NullResult,
                       threshold: float = 0.30) -> tuple[str, list[str]]:
    """Verdict ajusté par les deux témoins nuls.

    Logique :
    - Si log_range < threshold : F2_FALSIFIED_PROXY (signature invariante).
    - Si log_range >= threshold ET (p_value_shape_perm < 0.05 ET
      p_value_dirichlet < 0.05) : F2_CONFIRMED_PROXY.
    - Sinon : F2_INCONCLUSIVE_PROXY (log_range élevé mais pas au-dessus
      du bruit de fond).
    """
    details: list[str] = []
    if not math.isfinite(log_range):
        return "INCONCLUSIF", [f"log_range non fini: {log_range}"]
    if log_range < threshold:
        details.append(
            f"log-range sur K∈{min(shape_perm.log_range_distribution) if shape_perm.log_range_distribution else '?'}..{max(shape_perm.log_range_distribution) if shape_perm.log_range_distribution else '?'}: "
            f"{log_range:.3f} < {threshold} (signature invariante à K)")
        return "F2_FALSIFIED_PROXY", details
    p_shape = _p_value(shape_perm.log_range_distribution, log_range)
    p_dir = _p_value(dirichlet.log_range_distribution, log_range)
    details.append(
        f"log-range observé: {log_range:.3f} (seuil {threshold})")
    details.append(
        f"témoin shape_perm (n={shape_perm.n_perm}): "
        f"mean={shape_perm.mean:.3f} std={shape_perm.std:.3f} "
        f"p_value(>=obs)={p_shape:.3f}")
    details.append(
        f"témoin dirichlet (n={dirichlet.n_perm}): "
        f"mean={dirichlet.mean:.3f} std={dirichlet.std:.3f} "
        f"p_value(>=obs)={p_dir:.3f}")
    if p_shape < 0.05 and p_dir < 0.05:
        details.append(
            "log-range au-dessus des deux témoins (p<0.05 des deux côtés)")
        return "F2_CONFIRMED_PROXY", details
    details.append(
        "log-range élevé mais pas au-dessus des deux témoins (p>=0.05 d'un côté) ; "
        "le proxy ne discrimine pas l'effet F2 d'un effet de forme"
    )
    return "F2_INCONCLUSIVE_PROXY", details


def dissociation_f2_proxy(category_means: dict[str, np.ndarray], *,
                          k_grid: tuple[int, ...] = (1, 2, 4, 8, 16, 32, 64),
                          cat_a: str = "code_python",
                          cat_b: str = "prose_fr") -> DissociationK:
    """Sweep K-features sur la discrimination inter-catégories (proxy F2).

    Si `R(K) = mean_act(cat_a, K) / mean_act(cat_b, K)` est constant à K
    variable (log-range petit), la discrimination est invariante à la
    résolution d'accès (proxy F2 falsifié). Si `R(K)` décroît avec K, F2
    est confirmé (la discrimination est une sortie du workspace).
    """
    if cat_a not in category_means or cat_b not in category_means:
        return DissociationK({}, {}, {}, float("inf"),
                             "INCONCLUSIF",
                             [f"catégorie {cat_a} ou {cat_b} absente"])
    act_a = category_means[cat_a]
    act_b = category_means[cat_b]
    p1_by_k: dict[int, float] = {}
    p2_by_k: dict[int, float] = {}
    r_by_k: dict[int, float] = {}
    d_sae = act_a.shape[0]
    for k in k_grid:
        kk = min(k, d_sae)
        # Prendre les top-K features par activation moyenne, puis
        # sommer leur activation sur le set.
        idx_a = np.argsort(act_a)[::-1][:kk]
        idx_b = np.argsort(act_b)[::-1][:kk]
        p1 = float(act_a[idx_a].sum())
        p2 = float(act_b[idx_b].sum())
        p1_by_k[k] = p1
        p2_by_k[k] = p2
        r_by_k[k] = float(p1 / p2) if p2 > 0 else float("nan")
    valid = [r for r in r_by_k.values() if math.isfinite(r) and r > 0]
    if not valid:
        return DissociationK(p1_by_k, p2_by_k, r_by_k, float("inf"),
                             "INCONCLUSIF",
                             ["toutes les catégories ont activation nulle"])
    log_range = _log_range(r_by_k)
    # Verdict provisoire : sera ajusté par les témoins nuls dans run().
    if log_range < 0.30:
        verdict = "F2_FALSIFIED_PROXY"
        details = [f"log-range sur K∈{min(k_grid)}..{max(k_grid)}: "
                   f"{log_range:.3f} < 0.30 (signature invariante à K)"]
    else:
        verdict = "F2_CONFIRMED_PROXY_PRELIMINARY"
        details = [f"log-range sur K∈{min(k_grid)}..{max(k_grid)}: "
                   f"{log_range:.3f} ≥ 0.30 (à valider contre témoins nuls)"]
    return DissociationK(p1_by_k, p2_by_k, r_by_k, log_range, verdict, details)


def load_ict21_means(trace_path: str | Path) -> dict[str, np.ndarray]:
    """Lit un .npz ICT-21 (format `counts_<cat>`, `l0_vals_<cat>`) et
    rend l'activation moyenne par catégorie."""
    data = np.load(Path(trace_path), allow_pickle=False)
    out: dict[str, np.ndarray] = {}
    for key in data.files:
        if key.startswith("counts_") and key != "counts_total":
            cat = key[len("counts_"):]
            counts = data[key].astype(np.float64)
            if counts.sum() > 0:
                out[cat] = counts / counts.sum()
    return out


def run(trace_path: str | Path,
        output_path: str | Path | None = None,
        cat_a: str = "code_python",
        cat_b: str = "prose_fr",
        n_perm: int = 100,
        seed: int = 0) -> dict:
    """Pipeline CLI : charge les traces ICT-21, lance le sweep, écrit JSON.

    Le verdict final est ajusté par deux témoins nuls :
    - shape_perm (permutation intra-catégorie, forme préservée)
    - dirichlet (vecteur sans structure)
    Si le log_range observé est ≥ 0.30 mais qu'un des deux témoins
    a une p_value unilatérale (fraction nulls ≥ observé) ≥ 0.05,
    le verdict devient F2_INCONCLUSIVE_PROXY.
    """
    means = load_ict21_means(trace_path)
    res = dissociation_f2_proxy(means, cat_a=cat_a, cat_b=cat_b)
    shape_perm = dissociation_f2_null(
        means, cat_a=cat_a, cat_b=cat_b, n_perm=n_perm, seed=seed)
    dirichlet_r = dirichlet_null(
        means, cat_a=cat_a, cat_b=cat_b, n_perm=n_perm, seed=seed + 1)
    # Ajustement verdict si on est dans la branche "F2_CONFIRMED_PROXY_PRELIMINARY"
    final_verdict = res.verdict
    final_details = list(res.kill_details)
    if res.verdict == "F2_CONFIRMED_PROXY_PRELIMINARY":
        final_verdict, extra_details = _verdict_with_null(
            res.log_r_range, shape_perm=shape_perm, dirichlet=dirichlet_r)
        final_details = res.kill_details + extra_details
    p_shape = _p_value(shape_perm.log_range_distribution, res.log_r_range)
    p_dir = _p_value(dirichlet_r.log_range_distribution, res.log_r_range)
    payload = {
        "case": "F2_dehaene_proxy",
        "substrate": Path(trace_path).name,
        "cat_a": cat_a,
        "cat_b": cat_b,
        "k_grid": [1, 2, 4, 8, 16, 32, 64],
        "p1_by_k": res.p1_by_k,
        "p2_by_k": res.p2_by_k,
        "r_by_k": res.r_by_k,
        "log_r_range": res.log_r_range,
        "verdict": final_verdict,
        "kill_details": final_details,
        "nulls": {
            "shape_perm": {
                "n_perm": shape_perm.n_perm,
                "seed": shape_perm.seed,
                "mean": shape_perm.mean,
                "std": shape_perm.std,
                "p_value": p_shape,
                "log_range_distribution": shape_perm.log_range_distribution,
            },
            "dirichlet": {
                "n_perm": dirichlet_r.n_perm,
                "seed": dirichlet_r.seed,
                "mean": dirichlet_r.mean,
                "std": dirichlet_r.std,
                "p_value": p_dir,
                "log_range_distribution": dirichlet_r.log_range_distribution,
            },
        },
        "limits": [
            "PROXY : discrimination inter-categories (code vs prose), pas self/other",
            "Test direct F2 (K-sweep sur case 4 self/other) = GPU-only",
            "Tell c.8236 RECOVERABLE-MACHINE (po-2023/po-2024 GPU 24+ Go)",
            "Témoins nuls (shape_perm, dirichlet) : n=100 permutations chacun, seed fixée pour reproductibilité",
        ],
    }
    if output_path is not None:
        Path(output_path).write_text(
            json.dumps(payload, ensure_ascii=False, indent=1),
            encoding="utf-8", newline="\n")
    return payload


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("traces", help="path to .npz ICT-21 calibration traces")
    ap.add_argument("--cat-a", default="code_python")
    ap.add_argument("--cat-b", default="prose_fr")
    ap.add_argument("--out", help="output JSON path")
    ap.add_argument("--n-perm", type=int, default=100,
                    help="nombre de permutations par témoin nul")
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    out = run(args.traces, args.out, args.cat_a, args.cat_b,
              n_perm=args.n_perm, seed=args.seed)
    summary = {k: v for k, v in out.items()
               if k not in ("p1_by_k", "p2_by_k", "r_by_k")}
    for null in summary.get("nulls", {}).values():
        null.pop("log_range_distribution", None)
    print(json.dumps(summary, ensure_ascii=False, indent=1))
    print(f"r_by_k = {out['r_by_k']}")
