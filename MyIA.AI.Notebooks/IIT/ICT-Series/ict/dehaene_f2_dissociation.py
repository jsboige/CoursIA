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

**Second volet — test direct A/B/C (issue #19343, reste ouvert après le
proxy).** Le proxy ci-dessus laisse la question F2 intacte : il mesure une
discrimination inter-catégories, pas la reconnaissance self-sur-self. Le
second volet construit un substrat **synthétique numpy-only** où la question
est directement falsifiable : deux agents appariés (même spectre, identité
distincte), un *store étendu* à cinq variables, un *self-model* ridge par
agent, et un score de reconnaissance symétrique. Trois régimes : A (store
plein), B (store vidé partout — lésion), C (self-model ablaté — contrôle de
non-dégénérescence). Verdict pré-enregistré : F2 falsifié si
``|score_A - score_B| < 2 * sigma(score_B)``. Mesuré sur les graines
{0, 1, 7, 42} : ``F2_CONFIRMED_EXTENDED_REQUIRED`` (delta = +0,289 ;
2·σ_B = 0,074) — avec la nuance que le régime B garde une reconnaissance
significative (p < 0,02), donc le self-model **persiste** sans le store, plus
faiblement. Carnet : ``ICT-Dissociation-DehaeneF2-SelfReport.ipynb`` ;
résultats : ``ict/results/dehaene_f2_abc_results.json``.

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


# ---------------------------------------------------------------------------
# Test direct F2 — régimes A/B/C (issue #19343, reste ouvert après le proxy
# #19345). Substrat synthétique numpy-only : l'agent porte un *store étendu*
# (les 5 variables de l'issue), et un *self-model* (prédicteur ridge à un pas
# entraîné sur sa propre trajectoire). La reconnaissance est le pouvoir de
# discrimination self/other du self-model, mesuré par l'AUC de ses erreurs.
#
# Pré-enregistrement (scellé AVANT la mesure, cf. carnet
# `ICT-Dissociation-DehaeneF2-SelfReport.ipynb` et docs §F2) :
#   - Régime A : store étendu plein (contenu dérivé de la dynamique PROPRE de
#     l'agent : workspace_state, ignition_flag, report_counter, attention_index,
#     basin_width), réinjecté dans la dynamique et lu par le self-model.
#   - Régime B : store vidé PARTOUT (`extended_mind_store = 0`) — lésion, pas
#     aveuglement : le canal étendu est coupé du monde ET du self-model, qui
#     reste calculé sur ses entrées minimales (proprio + bruit).
#   - Régime C : store plein, branche self-model ABLATÉE (prédicteur non
#     entraîné) — contrôle de non-dégénérescence : score_C ≈ 0.
#
# F2 (Dehaene) prédit score_A >> score_B (le self-model est une SORTIE du
# workspace étendu). Falsification : |score_A - score_B| < 2 * sigma(score_B)
# sur les graines {0, 1, 7, 42}.
# ---------------------------------------------------------------------------

STORE_VARS = ("workspace_state", "ignition_flag", "report_counter",
              "attention_index", "basin_width")

ABC_SEED_BASES = (0, 1, 7, 42)


@dataclass
class AgentParams:
    """Paramètres d'un agent : identité (A, G, C) + hyper-paramètres partagés."""

    seed: int
    A: np.ndarray  # (d, d) identité dynamique de l'agent
    G: np.ndarray  # (d, 5) couplage du store étendu vers la dynamique
    C: np.ndarray  # (d, 2) gain du drive proprioceptif
    ign_threshold: float
    sigma_dyn: float


@dataclass
class ABCResult:
    """Résultat d'une graine : scores A/B/C + témoins nuls de permutation."""

    seed_base: int
    score_A: float
    score_B: float
    score_C: float
    p_A: float
    p_B: float
    p_C: float
    store_share_A: float  # part de variance du terme G·h dans la dynamique A
    null_A: list[float] = field(default_factory=list)
    null_B: list[float] = field(default_factory=list)
    null_C: list[float] = field(default_factory=list)


def _agent_params(seed: int, d: int = 8,
                  scales: np.ndarray | None = None) -> AgentParams:
    """Tire les paramètres d'un agent : identité propre, hyper-paramètres partagés.

    ``scales`` (spectre de ``A``) est **partagé par la paire** d'agents appariés :
    mêmes valeurs propres, base propre tirée indépendamment. C'est la condition
    de « capacité égale » de l'issue — à défaut, deux agents tirés librement
    n'ont ni le même temps de mélange ni la même stationnarité, et l'écart
    mesuré signalerait la mémoire de l'un plutôt que la reconnaissance du
    self-model.
    """
    rng = np.random.default_rng(seed)
    q, _ = np.linalg.qr(rng.normal(size=(d, d)))
    if scales is None:
        scales = 0.65 + 0.25 * rng.random(d)
    A = q @ np.diag(np.asarray(scales, dtype=float)) @ q.T
    G = 0.60 * rng.normal(size=(d, len(STORE_VARS))) / np.sqrt(len(STORE_VARS))
    C = 0.30 * rng.normal(size=(d, 2)) / np.sqrt(2.0)
    return AgentParams(seed=seed, A=A, G=G, C=C,
                       ign_threshold=0.75, sigma_dyn=0.02)


def _simulate(params: AgentParams, T: int, rng: np.random.Generator,
              store_active: bool = True) -> tuple[np.ndarray, np.ndarray]:
    """Simule l'agent et son store étendu.

    Le store est un intégrateur lent des lectures de la dynamique PROPRE de
    l'agent (self-specific par construction) : concentration globale, événement
    d'ignition, compteur de reports fuyant, entropie d'attention, largeur de
    bassin (EMA de la vitesse). Avec ``store_active=False``, le store est vidé
    partout (lésion du régime B) : il ne pilote plus la dynamique.
    """
    d = params.A.shape[0]
    x = np.zeros((T, d))
    h = np.zeros((T, len(STORE_VARS)))
    x[0] = rng.normal(size=d) / np.sqrt(d)
    report_acc = 0.0
    basin_ema = 0.0
    conc_ema = 0.0
    for t in range(1, T):
        prev = x[t - 1]
        conc = float(np.linalg.norm(prev)) / np.sqrt(d)
        if t == 1:
            conc_ema = conc
        # seuil RELATIF : 1.10x la concentration courante -> excursions seules
        # Seuil RELATIF a la concentration courante : le cycle de service
        # d'ignition est stable par construction. Un seuil absolu rendait la
        # trajectoire multimodale (train et test dans deux regimes differents,
        # R2 test negatif mesure) et la mesure comparait des regimes, pas des
        # agents.
        ign = 1.0 if conc > 1.10 * conc_ema else 0.0
        conc_ema = 0.99 * conc_ema + 0.01 * conc
        report_acc = 0.95 * report_acc + ign
        absx = np.abs(prev)
        p = absx / (absx.sum() + 1e-12)
        att = float(-(p * np.log(p + 1e-12)).sum()) / math.log(d)
        if t > 1:
            basin_ema = 0.98 * basin_ema + 0.02 * float(np.linalg.norm(prev - x[t - 2]))
        h_t = np.array([math.tanh(conc), ign,
                        math.tanh(report_acc / 5.0), att,
                        math.tanh(basin_ema * 5.0)])
        if not store_active:
            h_t = np.zeros(len(STORE_VARS))
        h[t - 1] = h_t
        u = rng.normal(size=2)
        x[t] = np.tanh(params.A @ prev + params.G @ h_t + params.C @ u) \
            + params.sigma_dyn * rng.normal(size=d)
    h[T - 1] = h[T - 2]
    return x, h


def _ridge(Z: np.ndarray, Y: np.ndarray, lam: float = 1.0) -> np.ndarray:
    """Régression ridge fermée : W = (Z^T Z + lam I)^-1 Z^T Y."""
    k = Z.shape[1]
    return np.linalg.solve(Z.T @ Z + lam * np.eye(k), Z.T @ Y)


def _regime_score(x_self: np.ndarray, h_self: np.ndarray | None,
                  x_other: np.ndarray, h_other: np.ndarray | None,
                  rng: np.random.Generator, use_store: bool,
                  untrained: bool = False, n_shuffles: int = 50,
                  train_frac: float = 0.60, burn_in: float = 0.20,
                  lam: float = 1.0) -> tuple[float, list[float]]:
    """Score de reconnaissance self-sur-self, **symétrique et apparié**.

    Le self-model est un prédicteur ridge à un pas ``x_{t+1} = W f(x_t)``
    entraîné sur la première fraction de la trajectoire PROPRE de l'agent.
    Chaque agent reçoit SON prédicteur ; l'avantage de reconnaissance est la
    moyenne des deux sens ::

        adv = 1/2 [ (PE(other | W_self) - PE(self | W_self)) / PE(self | W_self)
                  + (PE(self | W_other) - PE(other | W_other)) / PE(other | W_other) ]

    ``adv > 0`` : chaque prédicteur prédit mieux sa propre trajectoire que
    celle de l'agent apparié. La forme symétrique est ce qui rend la mesure
    robuste : elle est une différence de différences, donc les biais de cadre
    (dérive, amplitude) s'annulent au lieu de s'ajouter — la forme
    asymétrique mesurait ces biais (PE_other jusqu'à 635, score toujours
    négatif sur 4/4 graines, contrôle C non nul).

    Les deux agents sont standardisés par l'échelle GLOBALE (scalaire) de leur
    train respectif : la dynamique est isotrope, donc une échelle par feature
    n'apporte rien et amplifie une coordonnée saturée. Le contrôle C
    (prédicteurs non entraînés) rend ≈ 0 par construction.

    Le témoin nul permute les étiquettes self/other des blocs de résidus
    (n_shuffles ≥ 50) ; il mesure ce que la même statistique donne sur des
    données où l'identité est effacée.
    """
    burn = int(x_self.shape[0] * burn_in)
    x_self, x_other = x_self[burn:], x_other[burn:]
    if h_self is None:
        h_self = np.zeros((x_self.shape[0], len(STORE_VARS)))
    else:
        h_self = h_self[burn:]
    if h_other is None:
        h_other = np.zeros((x_other.shape[0], len(STORE_VARS)))
    else:
        h_other = h_other[burn:]
    cut = int(x_self.shape[0] * train_frac)

    def prep(x, h):
        cols = [x]
        if use_store:
            cols.append(h)
        z = np.column_stack(cols)[:-1]
        y = x[1:]
        mu, ymu = z[:cut].mean(axis=0), y[:cut].mean(axis=0)
        sd = float(z[:cut].std(axis=0).mean()) + 1e-6
        ysd = float(y[:cut].std(axis=0).mean()) + 1e-6
        return (z - mu) / sd, (y - ymu) / ysd

    z_s, y_s = prep(x_self, h_self)
    z_o, y_o = prep(x_other, h_other)
    zero = np.zeros((z_s.shape[1], x_self.shape[1]))
    w_s = zero if untrained else _ridge(z_s[:cut], y_s[:cut], lam)
    w_o = zero if untrained else _ridge(z_o[:cut], y_o[:cut], lam)

    def mse(z, w, y):
        return ((z[cut:] @ w - y[cut:]) ** 2).mean(axis=1)

    pe_ss, pe_os = mse(z_s, w_s, y_s), mse(z_o, w_s, y_o)
    pe_oo, pe_so = mse(z_o, w_o, y_o), mse(z_s, w_o, y_s)

    # Erreur par bloc de temps, agregee par APPARIEMENT (predicteur sur sa
    # propre trajectoire vs predicteur sur l'autre) : c'est l'appariement qui
    # porte l'hypothese, pas la trajectoire. Chaque cote recoit les deux
    # predicteurs, donc la statistique est symetrique par construction.
    blocks = np.array_split(np.arange(pe_ss.size), 20)
    err_own = np.array([(pe_ss[b].mean() + pe_oo[b].mean()) / 2.0 for b in blocks])
    err_cross = np.array([(pe_os[b].mean() + pe_so[b].mean()) / 2.0 for b in blocks])

    def stat(a: np.ndarray, b: np.ndarray) -> float:
        return float((b.mean() - a.mean()) / (a.mean() + 1e-12))

    observed = stat(err_own, err_cross)
    pooled = np.concatenate([err_own, err_cross])
    n1 = err_own.size
    nulls = []
    for _ in range(n_shuffles):
        perm = rng.permutation(pooled.size)
        nulls.append(stat(pooled[perm[:n1]], pooled[perm[n1:]]))
    return float(observed), nulls


def _p_value(nulls: list[float], observed: float) -> float:
    """p unilatérale : fraction de nulls >= observé (n_shuffles ≥ 50 requis)."""
    if not nulls:
        return 1.0
    return sum(1 for v in nulls if v >= observed) / len(nulls)


def _abc_verdict(scores_a: list[float], scores_b: list[float]) -> tuple[str, list[str]]:
    """Applique la règle de verdict pré-enregistrée (issue #19343)."""
    mean_a = float(np.mean(scores_a))
    mean_b = float(np.mean(scores_b))
    sigma_b = float(np.std(scores_b))
    delta = mean_a - mean_b
    details = [
        f"score_A moyen = {mean_a:+.3f} (graines {['%+.3f' % v for v in scores_a]})",
        f"score_B moyen = {mean_b:+.3f} (graines {['%+.3f' % v for v in scores_b]})",
        f"delta = score_A - score_B = {delta:+.3f} ; 2*sigma_B = {2 * sigma_b:.3f}",
    ]
    if delta >= 2 * sigma_b:
        return "F2_CONFIRMED_EXTENDED_REQUIRED", details
    if abs(delta) < 2 * sigma_b:
        return "F2_FALSIFIED_SELF_PERSISTS", details
    return "F2_INVERTED_STORE_HURTS", details


def run_abc_regimes(seed_bases: tuple[int, ...] = ABC_SEED_BASES,
                    T: int = 8000, d: int = 8, n_shuffles: int = 50,
                    output_path: str | Path | None = None) -> dict:
    """Test direct F2 en régimes A/B/C sur les graines pré-enregistrées.

    Pour chaque graine : deux agents appariés (même architecture, identité
    ``A/G/C`` tirée indépendamment), trajectoires A (store plein), B (store
    vidé partout — mêmes paramètres d'agent, seule la lésion change) et C
    (mêmes trajectoires que A, branche self-model non entraînée).
    """
    results: list[ABCResult] = []
    for sb in seed_bases:
        pair_scales = 0.65 + 0.25 * np.random.default_rng(1000 * sb + 1).random(d)
        p_self = _agent_params(1000 * sb + 2, d, scales=pair_scales)
        p_other = _agent_params(1000 * sb + 3, d, scales=pair_scales)
        x_sA, h_sA = _simulate(p_self, T, np.random.default_rng(1000 * sb + 4))
        x_oA, h_oA = _simulate(p_other, T, np.random.default_rng(1000 * sb + 5))
        x_sB, h_sB = _simulate(p_self, T, np.random.default_rng(1000 * sb + 6),
                               store_active=False)
        x_oB, h_oB = _simulate(p_other, T, np.random.default_rng(1000 * sb + 7),
                               store_active=False)
        s_a, n_a = _regime_score(x_sA, h_sA, x_oA, h_oA,
                                 np.random.default_rng(1000 * sb + 8),
                                 use_store=True, n_shuffles=n_shuffles)
        s_b, n_b = _regime_score(x_sB, h_sB, x_oB, h_oB,
                                 np.random.default_rng(1000 * sb + 9),
                                 use_store=False, n_shuffles=n_shuffles)
        s_c, n_c = _regime_score(x_sA, h_sA, x_oA, h_oA,
                                 np.random.default_rng(1000 * sb + 10),
                                 use_store=True, untrained=True,
                                 n_shuffles=n_shuffles)
        gh = (p_self.G @ h_sA[1:].T).T
        share = float(gh.var() / (gh.var() + (p_self.A @ x_sA[:-1].T).T.var() + 1e-12))
        results.append(ABCResult(seed_base=sb, score_A=s_a, score_B=s_b, score_C=s_c,
                                 p_A=_p_value(n_a, s_a), p_B=_p_value(n_b, s_b),
                                 p_C=_p_value(n_c, s_c), store_share_A=share,
                                 null_A=n_a, null_B=n_b, null_C=n_c))

    scores_a = [r.score_A for r in results]
    scores_b = [r.score_B for r in results]
    scores_c = [r.score_C for r in results]
    verdict, details = _abc_verdict(scores_a, scores_b)
    mean_c, sigma_c = float(np.mean(scores_c)), float(np.std(scores_c))
    sanity_c = abs(mean_c) < 2 * sigma_c + 1e-9
    payload = {
        "case": "F2_dehaene_abc",
        "substrate": "agents synthétiques (store étendu 5 variables + self-model ridge)",
        "seed_bases": list(seed_bases),
        "T": T, "d": d, "n_shuffles": n_shuffles,
        "scores_by_seed": [
            {"seed": r.seed_base, "A": r.score_A, "B": r.score_B, "C": r.score_C,
             "p_A": r.p_A, "p_B": r.p_B, "p_C": r.p_C,
             "store_share_A": r.store_share_A} for r in results
        ],
        "mean_A": float(np.mean(scores_a)), "std_A": float(np.std(scores_a)),
        "mean_B": float(np.mean(scores_b)), "std_B": float(np.std(scores_b)),
        "mean_C": mean_c, "std_C": sigma_c,
        "delta": float(np.mean(scores_a) - np.mean(scores_b)),
        "seeds_positive_delta": int(sum(1 for a, b in zip(scores_a, scores_b) if a > b)),
        "verdict": verdict,
        "kill_details": details,
        "sanity_C_near_zero": sanity_c,
        "limits": [
            "Substrat SYNTHÉTIQUE : la conclusion porte sur ce modèle, pas sur un LLM",
            "Régime B est une LÉSION (store vidé partout), pas un aveuglement du self-model",
            "Régime C réutilise les trajectoires A : seule la branche self-model est ablatée",
            f"Témoins nuls par permutation d'étiquettes, n={n_shuffles} par régime et par graine",
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
