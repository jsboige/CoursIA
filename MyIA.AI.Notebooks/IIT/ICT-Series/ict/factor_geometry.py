"""Primitives numpy-only de geometrie factorisee (F-Lens), extraites d'ICT-36.

Origine : ``ICT-36-FLens-FactoredGeometry.ipynb`` (PR #15514, grain #15478),
cellules 5, 7 et 14. L'extraction vers le paquet ``ict/`` repond a la
remarque propriétaire du 2026-09-10 (« ça mérite surtout un module Python
qui viendra outiller d'autres composants ») formalisee par l'issue #15943 :
le notebook est la leçon, le paquet est l'outil. Les corps sont deplaces
**a l'identique** -- l'acceptance exige des resultats inchanges par
rapport a #15514 ; toute correction de comportement passerait par une PR
dediee, pas par ce module.

Les 7 primitives :

- :func:`weighted_pca` -- PCA ponderee centree (numpy-only).
- :func:`nc_at` -- nombre de composantes pour atteindre chaque seuil de
  variance cumulee (NC@p).
- :func:`basis_overlap` -- overlap normalise entre deux bases orthonormees.
- :func:`max_principal_angle` -- plus grand angle principal entre sous-espaces.
- :func:`make_factor_bases` -- construction de sous-espaces factoriels
  (regimes orthogonal / superpose).
- :func:`synthesize_activations` -- generation d'activations factorisees.
- :func:`null_overlap_distribution` -- hypothese nulle de l'overlap
  (voir l'avertissement dans sa docstring : artefact documente, conserve
  tel quel pour la lecon).

Note sur ``nc_at`` : dans le notebook, le defaut etait le global
``NC_THRESHOLDS = (80, 90, 95, 99)`` ; ici le defaut est materialise en
litteral identique, meme comportement par defaut.
"""

from __future__ import annotations

import numpy as np

__all__ = [
    "weighted_pca",
    "nc_at",
    "basis_overlap",
    "max_principal_angle",
    "make_factor_bases",
    "synthesize_activations",
    "null_overlap_distribution",
]


def weighted_pca(activations, weights=None):
    """PCA ponderee centree (numpy-only).

    activations : (N, D) ndarray
    weights     : (N,) ndarray ou None (egalitaire)
    Returns     : (mean, components, singular_values, explained_variance_ratio)
    """
    X = np.asarray(activations, dtype=np.float64)
    N, D = X.shape
    if weights is None:
        w = np.ones(N, dtype=np.float64) / N
    else:
        w = np.asarray(weights, dtype=np.float64)
        w = w / w.sum()
    # Centrage pondere
    mu = (w[:, None] * X).sum(axis=0)
    Xc = X - mu
    # Matrice de covariance ponderee (D, D)
    C = (Xc.T * w) @ Xc  # broadcast weights sur les lignes
    # Diagonalisation symetrique
    eigvals, eigvecs = np.linalg.eigh(C)
    # Tri descendant (np.linalg.eigh retourne ascendant)
    order = np.argsort(eigvals)[::-1]
    eigvals = eigvals[order]
    eigvecs = eigvecs[:, order]
    # Correction de signe : convention deterministe (premier element >= 0)
    for j in range(eigvecs.shape[1]):
        if eigvecs[0, j] < 0:
            eigvecs[:, j] = -eigvecs[:, j]
    # Valeurs singulieres et ratio de variance expliquee
    sv = np.sqrt(np.maximum(eigvals, 0.0)) * np.sqrt(N)  # facteur sqrt(N) pour coherence SVD
    total_var = eigvals.sum()
    if total_var > 0:
        evr = eigvals / total_var
    else:
        evr = np.zeros_like(eigvals)
    return mu, eigvecs, sv, evr


def nc_at(evr, thresholds=(80, 90, 95, 99)):
    """Renvoie le nombre de composantes necessaires pour atteindre chaque seuil de variance cumulee.

    Le defaut materialise ``NC_THRESHOLDS = (80, 90, 95, 99)`` du notebook
    ICT-36 (comportement identique a l'original ou le defaut lisait ce global).
    """
    cum = np.cumsum(evr)
    out = {}
    for k in thresholds:
        idx = int(np.searchsorted(cum, k / 100.0) + 1)
        idx = min(idx, len(cum))
        out[k] = idx
    return out


def basis_overlap(B1, B2):
    """Overlap normalise entre deux bases orthonormees (matrices (D, k1) et (D, k2)).

    Renvoie la matrice (k1, k2) des cosinus absolus : |cos(angle)| entre directions principales.
    """
    M = B1.T @ B2
    return np.abs(M)


def max_principal_angle(B1, B2):
    """Plus grand angle principal entre les sous-espaces (en degres).

    max_principal_angle = arcsin(max singulier de la projection orthogonale).
    Equivalent a : || B1 - B1 B2 B2^T ||_2 = sin(principal_angle_max).
    """
    # Projection orthogonale de B1 sur l'espace colonne de B2 : P = B2 B2^T
    P = B2 @ B2.T
    # Norme spectrale de la composante orthogonale
    Q = np.eye(B1.shape[0]) - P
    diff = Q @ B1
    sin_max = np.linalg.norm(diff, ord=2)
    sin_max = min(max(sin_max, 0.0), 1.0)  # clampage numerique
    return float(np.degrees(np.arcsin(sin_max)))


def make_factor_bases(n_factors, dim, mode="orthogonal", overlap=0.0, rng=None):
    """Construit n_factors sous-espaces dans R^dim, selon le mode.

    mode='orthogonal' : sous-espaces disjoints (Gram-Schnidt part d'une matrice aleatoire).
    mode='superposed' : sous-espaces partiellement superposes (overlap controle).
    Renvoie (bases, dim_per_factor) avec bases[i] de forme (dim, dim_per_factor).
    """
    if rng is None:
        rng = np.random.default_rng(0)
    dim_per_factor = dim // n_factors
    A = rng.standard_normal((dim, dim))
    Q, _ = np.linalg.qr(A)  # base orthonormee de R^dim
    bases = []
    for i in range(n_factors):
        start = i * dim_per_factor
        stop = start + dim_per_factor
        bases.append(Q[:, start:stop])
    if mode == "superposed":
        # Melange lineaire des bases pour introduire un overlap controle
        mix = rng.standard_normal((n_factors, n_factors)) * overlap
        np.fill_diagonal(mix, 1.0)
        # Normalisation colonne pour garder des bases a peu pres orthonormees
        new_bases = []
        for i in range(n_factors):
            B = sum(mix[i, j] * bases[j] for j in range(n_factors))
            # Re-orthonormalisation via QR
            Qi, _ = np.linalg.qr(B)
            new_bases.append(Qi[:, :dim_per_factor])
        bases = new_bases
    return bases, dim_per_factor


def synthesize_activations(bases, n_tokens, signal_var=1.0, noise_var=0.0, rng=None):
    """Genere des activations (n_tokens, dim) telles que chaque facteur contribue.

    Pour chaque token t et facteur i : x_t = sum_i B_i @ z_i,t avec z_i,t ~ N(0, signal_var),
    plus bruit gaussien N(0, noise_var) si noise_var > 0.
    """
    if rng is None:
        rng = np.random.default_rng(0)
    dim = bases[0].shape[0]
    n_factors = len(bases)
    X = np.zeros((n_tokens, dim), dtype=np.float64)
    for i, B in enumerate(bases):
        dim_i = B.shape[1]
        z = rng.standard_normal((n_tokens, dim_i)) * np.sqrt(signal_var)
        X += z @ B.T
    if noise_var > 0:
        X += rng.standard_normal(X.shape) * np.sqrt(noise_var)
    weights = np.ones(n_tokens, dtype=np.float64)
    return X, weights


def null_overlap_distribution(dim, dim_factor, n_nulls=100, seed=0):
    """Distribution de l'overlap max entre une base factorielle et des sous-espaces aleatoires apparies.

    Sert d'hypothese nulle : si l'overlap reel <= quantile 95 de la distribution nulle, la separation
    factorielle est compatible avec le hasard.

    Avertissement (comportement conserve tel quel, cf. note pedagogique de la
    cellule 14 d'ICT-36) : la mesure interne ``|Q.T @ Q|.max()`` sur une base
    orthonormee issue de QR vaut 1.0 systematiquement -- c'est l'artefact qui a
    motive le VRAI test H1 du notebook (paires de sous-espaces aleatoires
    APPARIES, ``null_pairs`` en cellule 14). Cette primitive est conservee
    a l'identique pour la lecon ICT-36 ; ne pas l'utiliser comme test de
    separation sans lire cette note.
    """
    rng = np.random.default_rng(seed)
    nulls = []
    for _ in range(n_nulls):
        # Base aleatoire de meme dimension que la base factorielle
        A = rng.standard_normal((dim, dim_factor))
        Q, _ = np.linalg.qr(A)
        nulls.append(float(np.abs(Q.T @ Q).max()))
    return np.array(nulls)
