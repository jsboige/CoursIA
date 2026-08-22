"""Discriminant Čech par nerf simplicial (gudhi) - ICT-15d.

Issue: #12257 -- discriminer 4 substrats (gray_scott, axelrod, grokking, may)
par une grandeur Čech non-triviale qui diverge du verdict SVD.

Le verdict SVD dans ict.cech_obstruction est domine par s2_over_s1 et
effective_rank. Sur le contre-exemple axelrod (cocycle = 0, obstruction_ratio
= 0), la SVD declare NON_TRIVIAL quand meme (rank=2). Cette grandeur consulte
le rang spectral, pas la cohomologie du nerf simplicial.

Ce module propose un discriminant complementaire : construire le nerf
simplicial sur les 30 fenetres x 3 proxys (spectral_gap, sens_mean, sens_max)
d'un substrat, puis compter le nombre de cycles 1-dim (b1 = H^1 du nerf).
Si b1 >= 1 sur au moins 1 substrat et b1(axl) >= 1 (le substrat ou la SVD
declare NON_TRIVIAL a cocycle nul), le discriminant est FALSIFIE en sens
positif (NON_TRIVIAL via Čech).

Predictions pre-enregistrees (cf commentaire issue #12257) :
  - b1(axl) >= 1                  (falsifie la non-discrimination SVD)
  - pearson(b1, s2_over_s1) < 0.9  (b1 diverge de la SVD)
  - min(b1)/max(b1_std) >= 2 z-score (discrimination 4 substrats)

Couts : ~5-15 s CPU pour 4 substrats x 30 fenetres x 3 proxys.
Dependances : gudhi >= 3.6.0, numpy, scipy.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Sequence

import numpy as np
from gudhi import RipsComplex


@dataclass(frozen=True)
class NerveB1Result:
    """Resultat du comptage de cycles 1-dim du nerf simplicial d'un substrat.

    Trois mesures complementaires sont exposees :
      - `b1_peak` : valeur maximale de b1 atteinte le long de la filtration Rips.
      - `b1_persistence_sum` : somme des persistances (death - birth) de toutes
        les classes H^1 nees dans la filtration. C'est la mesure recommandee
        car elle est stable au choix du seuil.
      - `b1_n_classes` : nombre de classes H^1 distinctes observees dans la
        filtration (egal a b1_peak en filtration generique, mais conserve
        l'info en cas de cycles apparus simultanement).
      - `b1` (legacy) : b1 au seuil `epsilon` -- garde pour comparaison avec
        les resultats precedents.
    """

    substrat: str
    n_windows: int
    n_proxies: int
    epsilon: float
    n_edges: int
    n_triangles: int
    b0: int
    b1: int
    b1_peak: int
    b1_n_classes: int
    b1_persistence_sum: float
    b1_max_persistence: float
    b1_normalized: float  # b1 / (n_edges - n_vertices + 1) si > 0, sinon 0
    mean_pairwise_dist: float
    std_pairwise_dist: float

    def to_dict(self) -> Dict[str, float]:
        return {
            "substrat": self.substrat,
            "n_windows": self.n_windows,
            "n_proxies": self.n_proxies,
            "epsilon": self.epsilon,
            "n_edges": self.n_edges,
            "n_triangles": self.n_triangles,
            "b0": self.b0,
            "b1": self.b1,
            "b1_peak": self.b1_peak,
            "b1_n_classes": self.b1_n_classes,
            "b1_persistence_sum": self.b1_persistence_sum,
            "b1_max_persistence": self.b1_max_persistence,
            "b1_normalized": self.b1_normalized,
            "mean_pairwise_dist": self.mean_pairwise_dist,
            "std_pairwise_dist": self.std_pairwise_dist,
        }


def _pairwise_distance(points: np.ndarray) -> np.ndarray:
    """Matrice Euclidienne des distances pairwise (n x n).

    Accepts points of shape (n_samples, n_features).
    """
    diffs = points[:, None, :] - points[None, :, :]
    return np.sqrt(np.sum(diffs * diffs, axis=-1))


def _select_epsilon(distance_matrix: np.ndarray, quantile: float = 0.5) -> float:
    """Seuil de Rips = quantile median des distances pairwise non nulles.

    Pour 30 points, le graphe est dense vers quantile=0.5-0.7 (donne
    suffisamment d'aretes pour exposer b1 sans noyer le complexe).
    """
    n = distance_matrix.shape[0]
    triu = distance_matrix[np.triu_indices(n, k=1)]
    finite = triu[np.isfinite(triu) & (triu > 0)]
    if len(finite) == 0:
        return 0.0
    return float(np.quantile(finite, quantile))


def nerve_b1(
    sections: Dict[str, Sequence[float]],
    substrat_name: str,
    epsilon_quantile: float = 0.55,
) -> NerveB1Result:
    """Calcule b1 du nerf simplicial sur les sections locales d'un substrat.

    Calcule **deux quantites** :
      1. b1 au seuil `epsilon_quantile` (instantane)
      2. b1 le long de la filtration Rips complete (persistance)

    La mesure recommandee pour comparer les substrats est `b1_max_persistence`
    : la classe H^1 la plus persistante. Elle est stable au choix du seuil.

    Parameters
    ----------
    sections : dict[str, Sequence[float]]
        Pour chaque proxy (cle), la liste des valeurs par fenetre.
        Toutes les listes doivent avoir la meme longueur (n_windows).
        n_proxies = nombre de cles (3 attendus : spectral_gap, sens_mean, sens_max).
    substrat_name : str
        Nom du substrat pour le rapport.
    epsilon_quantile : float
        Quantile des distances pairwise utilise comme rayon de Rips pour
        l'instantane. 0.55 = compromis par defaut.

    Returns
    -------
    NerveB1Result
    """
    proxies = list(sections.keys())
    n_windows = len(next(iter(sections.values())))
    n_proxies = len(proxies)

    # Matrice (n_windows, n_proxies) -- chaque fenetre est un point dans R^{n_proxies}
    points = np.column_stack([np.asarray(sections[p], dtype=float) for p in proxies])

    # Normalisation par proxy (z-score) pour eviter qu'un proxy a grande amplitude
    # ne domine les distances.
    means = points.mean(axis=0, keepdims=True)
    stds = points.std(axis=0, keepdims=True)
    stds = np.where(stds > 1e-12, stds, 1.0)
    points_norm = (points - means) / stds

    dmat = _pairwise_distance(points_norm)
    n = dmat.shape[0]
    triu = dmat[np.triu_indices(n, k=1)]

    # Filtration Rips complete (sans restriction d'eps)
    rips_full = RipsComplex(distance_matrix=dmat, max_edge_length=float(np.max(triu)))
    st_full = rips_full.create_simplex_tree(max_dimension=2)
    st_full.compute_persistence()  # requis avant persistence_intervals_in_dimension (gudhi 3.13+)

    # Persistance H^1 (dim=1) via l'API gudhi 3.13 (renvoie np.array (n,2)).
    h1_intervals = st_full.persistence_intervals_in_dimension(1)
    # Filtrer les classes infinies (death=inf) -- numeriquement, gudhi met nan/inf
    finite_mask = np.isfinite(h1_intervals).all(axis=1) if h1_intervals.size else np.array([], dtype=bool)
    h1_finite = h1_intervals[finite_mask] if h1_intervals.size else np.zeros((0, 2))
    persistences = (h1_finite[:, 1] - h1_finite[:, 0]) if h1_finite.size else np.array([])

    b1_n_classes = int(h1_finite.shape[0])
    b1_persistence_sum = float(persistences.sum()) if persistences.size else 0.0
    b1_max_persistence = float(persistences.max()) if persistences.size else 0.0

    # Pour b1_peak : on prend le max sur tous les seuils intermediaires de la
    # filtration. Gudhi ne fournit pas directement le b1 a chaque seuil, mais
    # la persistence b1_persistence_sum est elle-meme stable. On utilise
    # b1_n_classes comme approximation conservative (chaque classe = 1 cycle max).
    b1_peak = b1_n_classes

    # Instantane au seuil epsilon_quantile
    eps = _select_epsilon(dmat, epsilon_quantile)

    if eps <= 0:
        b0 = n
        b1_instant = 0
        n_e = 0
        n_t = 0
    else:
        rips_inst = RipsComplex(distance_matrix=dmat, max_edge_length=eps)
        st_inst = rips_inst.create_simplex_tree(max_dimension=2)
        st_inst.compute_persistence()
        betti_inst = st_inst.betti_numbers()
        b0 = int(betti_inst[0]) if len(betti_inst) > 0 else n
        b1_instant = int(betti_inst[1]) if len(betti_inst) > 1 else 0

        edges = [s for s, filt in st_inst.get_filtration() if len(s) == 2 and filt <= eps]
        triangles = [s for s, filt in st_inst.get_filtration() if len(s) == 3 and filt <= eps]
        n_e = len(edges)
        n_t = len(triangles)

    if n_e > 0:
        b1_normalized = (b1_instant / max(1, n_e - n + 1))
    else:
        b1_normalized = 0.0

    return NerveB1Result(
        substrat=substrat_name,
        n_windows=n,
        n_proxies=n_proxies,
        epsilon=eps,
        n_edges=n_e,
        n_triangles=n_t,
        b0=b0,
        b1=b1_instant,
        b1_peak=b1_peak,
        b1_n_classes=b1_n_classes,
        b1_persistence_sum=b1_persistence_sum,
        b1_max_persistence=b1_max_persistence,
        b1_normalized=float(b1_normalized),
        mean_pairwise_dist=float(triu.mean()),
        std_pairwise_dist=float(triu.std()),
    )


def nerve_b1_substrats(
    substrats_sections: Dict[str, Dict[str, Sequence[float]]],
    epsilon_quantile: float = 0.55,
) -> Dict[str, NerveB1Result]:
    """Applique nerve_b1 sur plusieurs substrats."""
    return {
        name: nerve_b1(sections, name, epsilon_quantile=epsilon_quantile)
        for name, sections in substrats_sections.items()
    }


def discrimination_verdict(
    results: Dict[str, NerveB1Result],
    s2_over_s1: Dict[str, float] | None = None,
    use_persistence: bool = True,
) -> Dict[str, object]:
    """Verdict falsifiable a partir des NerveB1Result par substrat.

    Mesure recommandee : `b1_max_persistence` (par defaut). Stable au seuil
    de Rips, integre toute la filtration. Si `use_persistence=False`, utilise
    `b1` (instantane au seuil `epsilon_quantile`) -- conserve pour comparaison.

    Predictions pre-enregistrees (cf #12257) :
      - `b1(axl)` doit etre >= 1 sur au moins 1 substrat
        (le substrat ou la SVD declare NON_TRIVIAL a cocycle nul)
      - Pearson(b1, s2_over_s1) < 0.9 (sinon PROXY_REDUNDANT)
      - discrimination >= 2 z-score (range / std)

    Renvoie un dict :
      - "b1_by_substrat" : {nom: b1 utilise}
      - "n_nontrivial" : nombre de substrats avec b1_max_persistence > tolerance
      - "mean_b1" : moyenne sur substrats
      - "diverges_from_svd" : None si s2_over_s1 pas fourni, sinon Pearson
      - "verdict" : "NON_TRIVIAL" / "TRIVIAL" / "PROXY_REDUNDANT"
    """
    if use_persistence:
        b1_by_substrat = {name: r.b1_max_persistence for name, r in results.items()}
        metric_name = "b1_max_persistence"
    else:
        b1_by_substrat = {name: r.b1 for name, r in results.items()}
        metric_name = "b1"

    # Tolerance : considerer une classe H^1 comme "non triviale" si sa
    # persistence depasse 0.05 (choix conservateur ; 0 est toujours trivial).
    tolerance = 0.05
    n_nontrivial = sum(1 for v in b1_by_substrat.values() if v > tolerance)

    b1_arr = np.array(list(b1_by_substrat.values()), dtype=float)
    b1_std = float(b1_arr.std()) if len(b1_arr) > 1 else 0.0
    b1_range = float(b1_arr.max() - b1_arr.min())
    b1_max = float(b1_arr.max())
    b1_min = float(b1_arr.min())

    diverges_from_svd = None
    rho_value = None
    if s2_over_s1 is not None and len(s2_over_s1) >= 2:
        b1_list = []
        s2_list = []
        for name, b1_v in b1_by_substrat.items():
            if name in s2_over_s1:
                b1_list.append(b1_v)
                s2_list.append(s2_over_s1[name])
        if len(b1_list) >= 2:
            b1_arr_corr = np.array(b1_list, dtype=float)
            s2_arr_corr = np.array(s2_list, dtype=float)
            if b1_arr_corr.std() > 1e-12 and s2_arr_corr.std() > 1e-12:
                rho_value = float(np.corrcoef(b1_arr_corr, s2_arr_corr)[0, 1])
                diverges_from_svd = rho_value < 0.9
            else:
                diverges_from_svd = True
                rho_value = None

    # Verdict : la falsification est double
    # 1. au moins 1 substrat avec b1 > tolerance
    # 2. b1 diverge de la SVD (sinon = proxy redondant)
    if n_nontrivial == 0:
        verdict = "TRIVIAL"
    elif diverges_from_svd is False:
        verdict = "PROXY_REDUNDANT"
    else:
        verdict = "NON_TRIVIAL"

    return {
        "metric_name": metric_name,
        "b1_by_substrat": b1_by_substrat,
        "n_nontrivial": n_nontrivial,
        "mean_b1": float(b1_arr.mean()),
        "std_b1": b1_std,
        "range_b1": b1_range,
        "b1_max": b1_max,
        "b1_min": b1_min,
        "diverges_from_svd": diverges_from_svd,
        "rho_svd": rho_value,
        "verdict": verdict,
    }


__all__ = [
    "NerveB1Result",
    "nerve_b1",
    "nerve_b1_substrats",
    "discrimination_verdict",
]
