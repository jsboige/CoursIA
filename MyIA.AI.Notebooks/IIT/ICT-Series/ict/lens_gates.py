"""Gates qualite des lentilles avant intervention — metriques geometriques (issue #15480, tranche 2a).

Fonctions pures sur tableaux numpy. Aucune dependance au modele ni aux
endpoints : la pile transversale #15479 fournit le routage des canaux
(`lens_endpoints`) et le moteur d'intervention ; ces gates **mesurent** la
qualite de ce que les lentilles produisent, avant toute intervention.

Couvert ici — les metriques dont la semantique est non ambigue :

- :func:`heldout_linear_score` : gate F-Lens belief (R^2 / RMSE held-out
  d'un readout lineaire des representations vers les beliefs) ;
- :func:`principal_angles` / :func:`subspace_overlap` : angles et recouvrement
  spectral entre sous-espaces de facteurs (H4) ;
- :func:`additivity_residual` : residu relatif de la decomposition additive
  des representations par facteur ;
- :func:`separation_zscore` : separation geometrique d'une partition vraie
  confrontee a des partitions aleatoires appariees (H4 — « superieure a des
  partitions aleatoires » se mesure, elle ne se declare pas).

Explicitement differe : NC@95 — l'issue le nomme sans le definir ; une
semantique fabrique serait une metrique qui mesure autre chose que ce que
l'hypothese invoque. A definir dans la tranche qui l'exige.
"""

from __future__ import annotations

from typing import Dict

import numpy as np

Array = np.ndarray


class GateError(ValueError):
    """Parametrage ou formes incompatibles pour une gate."""


def _orthonormalize(basis: Array) -> Array:
    """Base orthonormalisee par QR ; erreur si la base est de rang deficient."""
    if basis.ndim != 2:
        raise GateError("attendu un tableau 2D (n_points, dim)")
    q, r = np.linalg.qr(basis)
    if not np.all(np.abs(np.diag(r)) > 1e-10):
        raise GateError("base de rang deficient : sous-espace mal defini")
    return q


def heldout_linear_score(
    features: Array,
    targets: Array,
    test_frac: float = 0.3,
    seed: int = 0,
) -> Dict[str, float]:
    """Gate F-Lens belief : R^2 et RMSE d'un readout lineaire (avec intercept), ajuste sur train, evalue sur held-out.

    Le decoupage est seede donc deterministe ; les lignes de ``features``
    sont les points, celles de ``targets`` les beliefs (une ou plusieurs
    colonnes).
    """
    if features.ndim != 2 or targets.ndim != 2:
        raise GateError("features et targets attendus en 2D (n, d)")
    if len(features) != len(targets):
        raise GateError("features et targets doivent avoir autant de lignes")
    if not 0.0 < test_frac < 1.0:
        raise GateError(f"test_frac doit etre dans (0,1), recu {test_frac}")
    if len(features) < 4:
        raise GateError("held-out exige au moins 4 points")

    rng = np.random.default_rng(seed)
    idx = rng.permutation(len(features))
    n_test = max(2, int(round(len(features) * test_frac)))
    test, train = idx[:n_test], idx[n_test:]

    x_tr = np.hstack([features[train], np.ones((len(train), 1))])
    x_te = np.hstack([features[test], np.ones((len(test), 1))])
    coef, *_ = np.linalg.lstsq(x_tr, targets[train], rcond=None)
    pred = x_te @ coef
    resid = targets[test] - pred

    rmse = float(np.sqrt((resid**2).mean()))
    t_centered = targets[test] - targets[test].mean(axis=0)
    tss = float((t_centered**2).sum())
    if tss <= 0.0:
        raise GateError("cible constante : R^2 indefini")
    return {"r2": float(1.0 - (resid**2).sum() / tss), "rmse": rmse}


def principal_angles(basis_u: Array, basis_v: Array) -> Array:
    """Angles principaux (radians, croissants) entre deux sous-espaces, par QR + SVD du produit des bases orthonormales."""
    q_u = _orthonormalize(basis_u)
    q_v = _orthonormalize(basis_v)
    if q_u.shape[1] > q_u.shape[0] or q_v.shape[1] > q_v.shape[0]:
        raise GateError("dimension de sous-espace superieure a l'ambiant")
    s = np.linalg.svd(q_u.T @ q_v, compute_uv=False)
    return np.arccos(np.clip(s, -1.0, 1.0))


def subspace_overlap(basis_u: Array, basis_v: Array) -> float:
    """Recouvrement spectral dans [0, 1] : somme des cos^2 des angles principaux, normalisee par la plus petite dimension.

    Le diviseur est le NOMBRE D'ANGLES MESURES (``len(theta)``), pas un rang
    recalcule sur les bases brutes : ``principal_angles`` orthonormalise par QR
    avec garde de rang (``_orthonormalize`` LEVE sur base deficiente), si bien
    que ses bases de sortie sont pleine-colonne par construction. Un
    ``matrix_rank`` mesure sur les bases brutes peut rendre MOINS que ce nombre
    de colonnes (base presque deficiente : tolerance au-dessus de la garde QR,
    en-dessous de celle de numpy) ; le diviseur serait alors trop petit, la
    somme porterait plus de termes qu'il n'en divise, et le recouvrement
    pourrait depasser 1 -- hors de l'intervalle annonce. Diviser par
    ``len(theta)`` aligne la normalisation sur ce qui est effectivement somme.
    """
    theta = principal_angles(basis_u, basis_v)
    k = int(theta.size)
    if k == 0:
        raise GateError("sous-espace de dimension nulle")
    return float((np.cos(theta) ** 2).sum() / k)


def additivity_residual(x: Array, x_a: Array, x_b: Array) -> float:
    """Residu relatif de la decomposition additive ``x ~ x_a + x_b`` : ||x - x_a - x_b||_F / ||x||_F."""
    for arr in (x, x_a, x_b):
        if arr.ndim != 2:
            raise GateError("attendu des tableaux 2D")
    if not (x.shape == x_a.shape == x_b.shape):
        raise GateError("formes identiques requises pour la decomposition additive")
    denom = np.linalg.norm(x)
    if denom <= 0.0:
        raise GateError("x nul : residu relatif indefini")
    return float(np.linalg.norm(x - x_a - x_b) / denom)


def _partition_separation(features: Array, labels: Array) -> float:
    """Separation d'une partition : trace(S_between) / trace(S_within) sur features centrees."""
    overall = features.mean(axis=0)
    s_w = np.zeros((features.shape[1], features.shape[1]))
    s_b = np.zeros_like(s_w)
    for lab in np.unique(labels):
        pts = features[labels == lab]
        center = pts.mean(axis=0)
        centered = pts - center
        s_w += centered.T @ centered
        diff = (center - overall)[None, :]
        s_b += len(pts) * (diff.T @ diff)
    tr_w = float(np.trace(s_w))
    if tr_w <= 1e-15:
        return float("inf")
    return float(np.trace(s_b) / tr_w)


def separation_zscore(
    features: Array,
    labels: Array,
    n_random: int = 200,
    seed: int = 0,
) -> Dict[str, float]:
    """H4 : z-score de la separation de la partition VRAIE confrontee a des relabelisations aleatoires appariees.

    La partition aleatoire preserve les effectifs de chaque classe (tirage
    multinomial des etiquettes, meme loi marginale) — le controle est apparie
    en taille, pas seulement en nombre.
    """
    if features.ndim != 2:
        raise GateError("features attendu en 2D")
    if labels.ndim != 1 or len(labels) != len(features):
        raise GateError("labels attendu en 1D, de meme longueur que features")
    if n_random < 2:
        raise GateError("z-score exige au moins 2 partitions aleatoires")

    rng = np.random.default_rng(seed)
    true_sep = _partition_separation(features, labels)
    counts = np.unique(labels, return_counts=True)[1]
    probs = counts / counts.sum()
    rand_seps = np.empty(n_random)
    for i in range(n_random):
        rand_labels = rng.choice(len(counts), size=len(labels), p=probs)
        rand_seps[i] = _partition_separation(features, rand_labels)
    std = float(rand_seps.std())
    if not np.isfinite(true_sep) or not np.all(np.isfinite(rand_seps)):
        raise GateError(
            "features degeneres (variance intra nulle) : separation et z-score indefinis"
        )
    if std <= 1e-15:
        raise GateError("separations aleatoires degeneratees (identiques) : z-score indefini")
    z = float((true_sep - rand_seps.mean()) / std)
    return {
        "z": z,
        "separation_vraie": true_sep,
        "separation_aleatoire_moyenne": float(rand_seps.mean()),
    }
