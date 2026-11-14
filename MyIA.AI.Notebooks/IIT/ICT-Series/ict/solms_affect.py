"""L'affect comme forme élémentaire de la conscience (Solms & Friston 2018, Epic #8182).

Source primaire (vue firsthand, copiée au gisement) :
    Solms M, Friston KJ (2018), « The Hard Problem of Consciousness and the Free
    Energy Principle », *Frontiers in Psychology* 9:2714, DOI 10.3389/fpsyg.2018.02714.

Ce qu'elle soutient et que ce module opérationnalise (grade C, traduction de la
lane -- cf ``docs/ict/solms-affect-pre-enregistrement.md`` §1) :
    1. la forme élémentaire de la conscience est l'**affect** ;
    2. son mécanisme physiologique est une forme étendue d'**homéostasie**,
       localisée dans le **tronc cérébral supérieur** (subcortical) ;
    3. formalisé en minimisation d'**énergie libre** : les **baisse** et
       **hausse** de l'incertitude attendue sont senties comme **plaisir** et
       déplaisir ;
    4. cela reconceptualise **level** (affectif, subcortical) vs **contents**
       (corticaux) de la conscience.

Le surrogate (pré-enregistrement §2) : un organisme tient ``d`` variables
homéostatiques ``x_t`` autour de consignes ``x*`` ; l'incertitude attendue
``U_t`` est l'EMA de l'erreur homéostatique. Deux architectures, même terrain :
    * **H1 (Solms)** -- l'affect ``a_t = -k_a * dU_t`` est généré par la
      **dynamique homéostatique** (subcortical) ; les contents ``c_t = W x_t``
      sont une lecture **corticale**.
    * **H0 (null)** -- l'affect est un **readout cortical des contents**
      ``a_t = w_a . c_t`` : retirer le cortex le supprime.

La prédiction signature (P1) : en H1 le **level** survit à l'ablation corticale
(conscience sans cortex) alors qu'en H0 il s'éteint. P2 porte sur le mécanisme
énergie-libre (``corr(a, -dU)``), P3 sur la spécificité subcorticale, P4 sur la
discrimination H1/H0, P5 sur la corticalité des contents.

Substrat
--------
Numpy uniquement, CPU-only, graine-fixe (deterministe).
"""

from __future__ import annotations

import json
from typing import Dict, List, Optional, Sequence, Tuple

import numpy as np


# --------------------------------------------------------------------------- #
#  Terrain homéostatique : x_t, U_t (incertitude attendue), dU_t              #
# --------------------------------------------------------------------------- #


def homeostatic_trajectory(
    d: int = 4,
    T: int = 300,
    alpha: float = 0.2,
    kappa: float = 0.6,
    sigma: float = 1.0,
    rng: Optional[np.random.Generator] = None,
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Tire une trajectoire homéostatique ``x_t`` et en dérive ``U_t`` / ``dU_t``.

    ``x_t = x* + z_t`` où ``z_t`` suit un processus d'Ornstein-Uhlenbeck
    (moyenne-réversion vers 0) : l'état errate autour des consignes sous une
    perturbation exogène, ce qui fait **fluctuer** l'erreur homéostatique
    ``||x_t - x*||^2`` -- ``dU_t`` prend donc les deux signes.

    ``U_t`` (proxie de l'« expected uncertainty ») est l'EMA de cette erreur au
    carré : ``U_t = alpha * err2_t + (1 - alpha) * U_{t-1}``.

    Renvoie ``(x, U, dU)`` : ``x`` de forme ``(T, d)``, ``U`` et ``dU`` de forme
    ``(T,)``.
    """
    if rng is None:
        rng = np.random.default_rng(0)
    x_star = rng.standard_normal(d)
    z = np.zeros(d)
    x = np.empty((T, d), dtype=float)
    for t in range(T):
        x[t] = x_star + z
        z = float(kappa) * z + float(sigma) * rng.standard_normal(d)
    err2 = ((x - x_star) ** 2).sum(axis=1)
    U = np.empty(T, dtype=float)
    U[0] = err2[0]
    for t in range(1, T):
        U[t] = float(alpha) * err2[t] + (1.0 - float(alpha)) * U[t - 1]
    dU = np.empty(T, dtype=float)
    dU[0] = 0.0
    dU[1:] = U[1:] - U[:-1]
    return x, U, dU


# --------------------------------------------------------------------------- #
#  Canaux : affect (subcortical / cortical) et contents (cortical)            #
# --------------------------------------------------------------------------- #


def affect_subcortical(dU: np.ndarray, k_a: float = 1.0) -> np.ndarray:
    """Affect **H1 (Solms)** : ``a_t = -k_a * dU_t``.

    Traduction directe de la citation 2 : une **baisse** de l'incertitude
    attendue (``dU < 0``) est sentie comme **plaisir** (``a > 0``), une **hausse**
    comme **déplaisir** (``a < 0``). Généré par la dynamique homéostatique,
    indépendamment du canal cortical.
    """
    return -float(k_a) * np.asarray(dU, dtype=float)


def content_readout(x: np.ndarray, W: np.ndarray) -> np.ndarray:
    """Contents **corticale** : ``c_t = x_t @ W`` (lecture riche de l'état)."""
    return np.asarray(x, dtype=float) @ np.asarray(W, dtype=float)


def affect_cortical(c: np.ndarray, w_a: np.ndarray) -> np.ndarray:
    """Affect **H0 (null)** : ``a_t = w_a . c_t`` -- un readout cortical des
    contents. Si le cortex est retiré (``c = 0``), l'affect s'éteint. C'est le
    régime adverse qui doit se distinguer de H1 (P4)."""
    return np.asarray(c, dtype=float) @ np.asarray(w_a, dtype=float)


def _measure(a: np.ndarray, scale: float, rng: np.random.Generator) -> np.ndarray:
    """Signal mesuré : ``a + eta * N(0,1)`` avec ``eta = scale * std(dU)``.

    Le bruit rend la corrélation mécanisme/bruit **non triviale** (P2 ~ 0,89,
    pas 1,0) tout en gardant le mécanisme dominant.
    """
    eta = float(scale) * float(np.std(a)) if a.size else 0.0
    return np.asarray(a, dtype=float) + eta * rng.standard_normal(a.size)


def _pearson(xs: np.ndarray, ys: np.ndarray) -> float:
    """Corrélation de Pearson (rend 0 si variance nulle)."""
    xs = np.asarray(xs, dtype=float)
    ys = np.asarray(ys, dtype=float)
    if xs.size < 2 or float(np.std(xs)) < 1e-12 or float(np.std(ys)) < 1e-12:
        return 0.0
    xs = xs - xs.mean()
    ys = ys - ys.mean()
    denom = float(np.sqrt((xs * xs).sum() * (ys * ys).sum()))
    return float((xs * ys).sum() / denom) if denom > 0 else 0.0


def _content_richness(c: np.ndarray) -> float:
    """Richesse des contents : variance échantillon de la trajectoire (somme des
    variances par coordonnée). 0 si le canal est absent."""
    c = np.asarray(c, dtype=float)
    if c.size == 0:
        return 0.0
    if c.ndim == 1:
        return float(np.var(c))
    return float(np.sum(np.var(c, axis=0)))


# --------------------------------------------------------------------------- #
#  Un bras : feel, content_rich, valence_tracks_dU                             #
# --------------------------------------------------------------------------- #


def run_arm(
    arch: str,
    ablation: str,
    x: np.ndarray,
    dU: np.ndarray,
    W: np.ndarray,
    w_a: np.ndarray,
    k_a: float = 1.0,
    noise_scale: float = 0.5,
    rng: Optional[np.random.Generator] = None,
) -> Dict[str, float]:
    """Évalue un bras (architecture x ablation) et rend ses métriques.

    ``arch`` ∈ {"h1", "h0"} ; ``ablation`` ∈ {"none", "no_cortex", "no_subcortex"}.
    En H1 l'affect est subcortical (``-k_a dU``) et les contents corticaux
    (``x @ W``) ; en H0 l'affect est un readout cortical (``w_a . c``).
    """
    if rng is None:
        rng = np.random.default_rng(0)
    # Contents corticales (supprimées si le cortex est ablé)
    c = content_readout(x, W) if ablation != "no_cortex" else np.zeros_like(content_readout(x, W))

    if arch == "h1":
        a = affect_subcortical(dU, k_a=k_a) if ablation != "no_subcortex" else np.zeros(dU.size)
    elif arch == "h0":
        a = affect_cortical(c, w_a)  # dépend des contents -> nul si cortex ablé
    else:
        raise ValueError(f"arch inconnue : {arch!r}")

    a_meas = _measure(a, scale=noise_scale, rng=rng)
    return {
        "feel": float(np.mean(np.abs(a_meas))),
        "content_rich": _content_richness(c),
        "valence_tracks_dU": _pearson(a_meas, -dU),
    }


# --------------------------------------------------------------------------- #
#  Verdict : les 5 prédictions pre-enregistrées (graine unique)               #
# --------------------------------------------------------------------------- #


def case_verdict(
    d: int = 4,
    T: int = 300,
    m: int = 8,
    alpha: float = 0.2,
    kappa: float = 0.6,
    sigma: float = 1.0,
    k_a: float = 1.0,
    noise_scale: float = 0.5,
    seed: int = 0,
) -> Dict[str, float]:
    """Verdict de la tranche Solms sur une **graine** (pré-enregistrement §3).

    Renvoie les ratios clés, les booléens P1-P5 (à l'échelle de la graine) et un
    verdict de convenance. L'agrégation multi-graine (chaque graine / médiane)
    est faite par :func:`verdict_robust_across_seeds`.
    """
    rng = np.random.default_rng(seed)
    x, U, dU = homeostatic_trajectory(d=d, T=T, alpha=alpha, kappa=kappa, sigma=sigma, rng=rng)
    W = rng.standard_normal((d, m))
    w_a = rng.standard_normal(m)

    intact = run_arm("h1", "none", x, dU, W, w_a, k_a=k_a, noise_scale=noise_scale, rng=rng)
    no_cortex = run_arm("h1", "no_cortex", x, dU, W, w_a, k_a=k_a, noise_scale=noise_scale, rng=rng)
    no_subcortex = run_arm("h1", "no_subcortex", x, dU, W, w_a, k_a=k_a, noise_scale=noise_scale, rng=rng)
    h0_intact = run_arm("h0", "none", x, dU, W, w_a, k_a=k_a, noise_scale=noise_scale, rng=rng)
    h0_no_cortex = run_arm("h0", "no_cortex", x, dU, W, w_a, k_a=k_a, noise_scale=noise_scale, rng=rng)

    def _ratio(num: float, den: float) -> float:
        return float(num / den) if den > 1e-12 else 0.0

    feel_ratio_nocortex = _ratio(no_cortex["feel"], intact["feel"])
    feel_ratio_nosubcortex = _ratio(no_subcortex["feel"], intact["feel"])
    content_ratio_nocortex = _ratio(no_cortex["content_rich"], intact["content_rich"])
    h0_feel_ratio_nocortex = _ratio(h0_no_cortex["feel"], h0_intact["feel"])
    dissociation_contrast = feel_ratio_nocortex - h0_feel_ratio_nocortex
    valence_tracks_dU = intact["valence_tracks_dU"]

    p1 = bool(feel_ratio_nocortex >= 0.5)
    p2 = bool(valence_tracks_dU >= 0.7)
    p3 = bool(feel_ratio_nosubcortex <= 0.2)
    p4 = bool(dissociation_contrast >= 0.3)
    p5 = bool(content_ratio_nocortex <= 0.3)

    return {
        "seed": int(seed),
        "feel_ratio_nocortex": feel_ratio_nocortex,
        "feel_ratio_nosubcortex": feel_ratio_nosubcortex,
        "content_ratio_nocortex": content_ratio_nocortex,
        "h0_feel_ratio_nocortex": h0_feel_ratio_nocortex,
        "dissociation_contrast": dissociation_contrast,
        "valence_tracks_dU": valence_tracks_dU,
        "p1": p1,
        "p2": p2,
        "p3": p3,
        "p4": p4,
        "p5": p5,
        "verdict": "PASS" if all([p1, p2, p3, p4, p5]) else "PARTIAL",
    }


# --------------------------------------------------------------------------- #
#  Agrégation multi-graine (pré-enregistrement §3 : chaque graine / médiane)  #
# --------------------------------------------------------------------------- #


def verdict_robust_across_seeds(
    seeds: Sequence[int] = (0, 1, 7, 42, 99),
    **kw,
) -> Dict[str, object]:
    """Verdict de la tranche sur les graines d'étude, selon les règles d'agrégation
    pre-enregistrées : P1/P3/P5 sur **chaque** graine, P2/P4 sur la **médiane**."""
    per_seed = [case_verdict(seed=int(s), **kw) for s in seeds]
    p1 = all(r["p1"] for r in per_seed)
    # P2 : médiane de valence_tracks_dU >= 0,7
    p2 = bool(np.median([r["valence_tracks_dU"] for r in per_seed]) >= 0.7)
    p3 = all(r["p3"] for r in per_seed)
    p4 = bool(np.median([r["dissociation_contrast"] for r in per_seed]) >= 0.3)
    p5 = all(r["p5"] for r in per_seed)

    n_ok = sum(1 for p in (p1, p2, p3, p4, p5) if p)
    if n_ok == 5:
        verdict = "SUPPORTED"
    elif p1 and p2 and sum(1 for p in (p3, p4, p5) if p) >= 2:
        verdict = "PARTIAL"
    else:
        verdict = "REFUTED"

    return {
        "seeds": [int(s) for s in seeds],
        "per_seed": per_seed,
        "p1_each_seed": p1,
        "p2_median": p2,
        "p3_each_seed": p3,
        "p4_median": p4,
        "p5_each_seed": p5,
        "verdict": verdict,
    }


# --------------------------------------------------------------------------- #
#  Étude : exécution + écriture du JSON de résultats                          #
# --------------------------------------------------------------------------- #


def run_study(seeds: Sequence[int] = (0, 1, 7, 42, 99), **kw) -> Dict[str, object]:
    """Exécute l'étude sur les graines et renvoie le dictionnaire de résultats."""
    return verdict_robust_across_seeds(seeds=seeds, **kw)


def main(out_path: Optional[str] = None, seeds: Sequence[int] = (0, 1, 7, 42, 99)) -> Dict[str, object]:
    """Point d'entrée : exécute l'étude et (si ``out_path``) écrit le JSON."""
    results = run_study(seeds=seeds)
    if out_path:
        with open(out_path, "w", encoding="utf-8") as fh:
            json.dump(results, fh, ensure_ascii=False, indent=2, sort_keys=True)
    return results


if __name__ == "__main__":
    import sys

    out = sys.argv[1] if len(sys.argv) > 1 else None
    res = main(out_path=out)
    print(json.dumps({"verdict": res["verdict"]}, ensure_ascii=False))
