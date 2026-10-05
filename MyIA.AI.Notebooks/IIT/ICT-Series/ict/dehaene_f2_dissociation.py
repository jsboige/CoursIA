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
    log_r = [math.log(r) for r in valid]
    log_range = max(log_r) - min(log_r)
    if log_range < 0.30:
        verdict = "F2_FALSIFIED_PROXY"
        details = [f"log-range sur K∈{min(k_grid)}..{max(k_grid)}: "
                   f"{log_range:.3f} < 0.30 (signature invariante à K)"]
    else:
        verdict = "F2_CONFIRMED_PROXY"
        details = [f"log-range sur K∈{min(k_grid)}..{max(k_grid)}: "
                   f"{log_range:.3f} ≥ 0.30 (signature dépend de K)"]
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
        cat_b: str = "prose_fr") -> dict:
    """Pipeline CLI : charge les traces ICT-21, lance le sweep, écrit JSON."""
    means = load_ict21_means(trace_path)
    res = dissociation_f2_proxy(means, cat_a=cat_a, cat_b=cat_b)
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
        "verdict": res.verdict,
        "kill_details": res.kill_details,
        "limits": [
            "PROXY : discrimination inter-categories (code vs prose), pas self/other",
            "Test direct F2 (K-sweep sur case 4 self/other) = GPU-only",
            "Tell c.8236 RECOVERABLE-MACHINE (po-2023/po-2024 GPU 24+ Go)",
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
    args = ap.parse_args()
    out = run(args.traces, args.out, args.cat_a, args.cat_b)
    print(json.dumps({k: v for k, v in out.items()
                      if k not in ("p1_by_k", "p2_by_k", "r_by_k")},
                     ensure_ascii=False, indent=1))
    print(f"r_by_k = {out['r_by_k']}")
