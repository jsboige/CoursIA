"""Tests unitaires pour :mod:`ict.factor_geometry` (F-Lens, extraction #15943).

Le module porte les 7 primitives numpy-only de geometrie factorisee deplacees
a l'identique depuis ``ICT-36-FLens-FactoredGeometry.ipynb`` (PR #15514,
cellules 5, 7, 14). L'acceptance #15943 exige des **resultats inchanges** :
ces tests figent donc les contrats EXACTS du code deplace, y compris le
comportement artefactuel documente de :func:`null_overlap_distribution`
(contrat 11). Toute correction de comportement devra se voir ici en
echec -- c'est le garde anti-drift silencieux de l'extraction.

Contrats attestes :

    1.  (``__all__``) : le module expose exactement les 7 noms de
        l'acceptance #15943 (7 primitives, ni plus ni moins).
    2.  (evr exacte) : :func:`weighted_pca` sur des donnees 2D de variances
        connues (4 selon x, 1 selon y) rend evr = [0.8, 0.2] et des
        composantes alignees sur les axes (convention de signe : premier
        element >= 0).
    3.  (centrage pondere) : la moyenne rendue est la moyenne PONDEREE,
        pas la moyenne arithmetique -- un point lointain a fort poids tire
        mu vers lui (motivation n.2 de la md cellule 4 d'ICT-36).
    4.  (egalitaire par defaut) : ``weights=None`` equivaut au poids
        uniforme 1/N (mu identique a la moyenne arithmetique).
    5.  (nc_at bornes) : sur evr = [.5, .3, .15, .05] (cumul
        [.5, .8, .95, 1.0]), nc_at rend {80: 2, 90: 3, 95: 3, 99: 4}.
    6.  (nc_at defaut materialise) : le defaut ``thresholds`` du module
        vaut (80, 90, 95, 99) -- le litteral materialise le global
        ``NC_THRESHOLDS`` du notebook, meme comportement par defaut.
    7.  (basis_overlap identite) : une base contre elle-meme rend |cos| = 1
        sur la diagonale et 0 ailleurs (base orthonormee).
    8.  (basis_overlap orthogonal) : deux blocs disjoints d'identite rendent
        une matrice nulle.
    9.  (angle 0 et 90) : :func:`max_principal_angle` rend 0 deg pour un
        sous-espace contre lui-meme et 90 deg pour deux directions
        orthogonales de R^3.
    10. (bases orthogonales disjointes) : ``mode='orthogonal'`` rend des
        bases (dim, dim_per_factor) deux a deux orthogonales et
        deterministes sans rng (seed 0 implicite).
    11. (null artefact conserve) : :func:`null_overlap_distribution` rend
        1.0 systematiquement -- l'artefact |Q.T Q|.max() documente dans la
        docstring du module et la cellule 14 d'ICT-36. Le contrat est le
        comportement DEPLACE, pas le test qu'il pretend etre ; le VRAI
        test H1 (paires appariees) vit dans le notebook.
    12. (superpose > orthogonal) : ``mode='superposed'`` (overlap=0.4)
        produit un overlap moyen entre bases SUPERIEUR au regime
        orthogonal -- le regime discrimine, c'est sa raison d'etre.
    13. (synthese forme et determinisme) : :func:`synthesize_activations`
        rend X de forme (n_tokens, dim), weights uniformes ones(n_tokens),
        et est deterministe pour un meme rng ; ``noise_var > 0`` change X.
"""

from __future__ import annotations

import numpy as np

from ict import factor_geometry as fg


def test_all_exposes_exactement_les_7_primitives():
    assert fg.__all__ == [
        "weighted_pca",
        "nc_at",
        "basis_overlap",
        "max_principal_angle",
        "make_factor_bases",
        "synthesize_activations",
        "null_overlap_distribution",
    ]


def test_weighted_pca_evr_et_axes():
    rng = np.random.default_rng(0)
    n = 4000
    x = rng.normal(0.0, 2.0, size=n)  # var 4
    y = rng.normal(0.0, 1.0, size=n)  # var 1
    X = np.column_stack([x, y])
    mu, comps, sv, evr = fg.weighted_pca(X)
    assert abs(mu[0]) < 0.1 and abs(mu[1]) < 0.1
    # evr attendu : [4/5, 1/5] = [0.8, 0.2]
    np.testing.assert_allclose(evr, [0.8, 0.2], atol=0.02)
    # composante principale alignee sur l'axe x, convention de signe >= 0
    np.testing.assert_allclose(np.abs(comps[:, 0]), [1.0, 0.0], atol=1e-2)
    assert comps[0, 0] >= 0
    # valeurs singulieres coherentes SVD : sv[0] ~ sqrt(var*N)
    np.testing.assert_allclose(sv[0], 2.0 * np.sqrt(n), rtol=0.05)


def test_weighted_pca_centrage_pondere():
    X = np.array([[0.0, 0.0], [0.0, 0.0], [10.0, 10.0]])
    w = np.array([0.45, 0.45, 0.10])
    mu, _, _, _ = fg.weighted_pca(X, w)
    # moyenne ponderee = 0.1 * (10, 10) ; la moyenne arithmetique serait (10/3, 10/3)
    np.testing.assert_allclose(mu, [1.0, 1.0], atol=1e-12)


def test_weighted_pca_none_egalitaire():
    X = np.array([[0.0], [2.0], [4.0]])
    mu, _, _, _ = fg.weighted_pca(X, None)
    assert mu[0] == float(np.mean(X))


def test_nc_at_bornes():
    evr = np.array([0.5, 0.3, 0.15, 0.05])
    out = fg.nc_at(evr, (80, 90, 95, 99))
    assert out == {80: 2, 90: 3, 95: 3, 99: 4}


def test_nc_at_defaut_materialise():
    evr = np.array([0.5, 0.3, 0.15, 0.05])
    out = fg.nc_at(evr)  # defaut du module, sans seuils explicites
    assert out == {80: 2, 90: 3, 95: 3, 99: 4}


def test_basis_overlap_identite():
    B = np.eye(4)[:, :3]
    M = fg.basis_overlap(B, B)
    np.testing.assert_allclose(np.diag(M), 1.0, atol=1e-12)
    off = M - np.diag(np.diag(M))
    np.testing.assert_allclose(off, 0.0, atol=1e-12)


def test_basis_overlap_orthogonal():
    e1 = np.eye(3)[:, :1]  # direction x
    e2 = np.eye(3)[:, 1:2]  # direction y
    M = fg.basis_overlap(e1, e2)
    np.testing.assert_allclose(M, 0.0, atol=1e-12)


def test_max_principal_angle_0_et_90():
    B = np.eye(3)[:, :2]
    assert fg.max_principal_angle(B, B) == 0.0
    ex = np.eye(3)[:, :1]
    ey = np.eye(3)[:, 1:2]
    assert abs(fg.max_principal_angle(ex, ey) - 90.0) < 1e-9


def test_make_factor_bases_orthogonal_disjointes():
    bases, dim_per = fg.make_factor_bases(4, 32, mode="orthogonal")
    assert dim_per == 8
    assert len(bases) == 4
    for B in bases:
        assert B.shape == (32, 8)
    for i in range(4):
        for j in range(i + 1, 4):
            M = fg.basis_overlap(bases[i], bases[j])
            np.testing.assert_allclose(M, 0.0, atol=1e-10)
    # determinisme : deux appels sans rng (seed 0 implicite) rendent identique
    bases2, _ = fg.make_factor_bases(4, 32, mode="orthogonal")
    for B, B2 in zip(bases, bases2):
        np.testing.assert_allclose(B, B2)


def test_null_overlap_distribution_artefact_conserve():
    nulls = fg.null_overlap_distribution(dim=16, dim_factor=4, n_nulls=25, seed=3)
    assert nulls.shape == (25,)
    # |Q.T @ Q|.max() sur une base QR orthonormee = identite -> 1.0 systematique.
    # Comportement DEPLACE tel quel (avertissement module + cellule 14 ICT-36) :
    # ce test fige l'artefact, il ne le valide pas comme test statistique.
    np.testing.assert_allclose(nulls, 1.0, atol=1e-12)
    # determinisme par seed
    again = fg.null_overlap_distribution(dim=16, dim_factor=4, n_nulls=25, seed=3)
    np.testing.assert_array_equal(nulls, again)


def test_make_factor_bases_superposed_plus_doverlap():
    rng = np.random.default_rng(7)
    bases_o, _ = fg.make_factor_bases(4, 32, mode="orthogonal", rng=rng)
    rng_s = np.random.default_rng(7)
    bases_s, _ = fg.make_factor_bases(4, 32, mode="superposed", overlap=0.4, rng=rng_s)


    def mean_overlap(bases):
        vals = []
        for i in range(len(bases)):
            for j in range(i + 1, len(bases)):
                vals.append(float(fg.basis_overlap(bases[i], bases[j]).max()))
        return float(np.mean(vals))


    assert mean_overlap(bases_s) > mean_overlap(bases_o) + 0.05


def test_synthesize_activations_forme_determinisme_bruit():
    bases, dim_per = fg.make_factor_bases(3, 24, mode="orthogonal")
    X1, w1 = fg.synthesize_activations(bases, 200, signal_var=1.0, noise_var=0.0,
                                       rng=np.random.default_rng(5))
    X2, w2 = fg.synthesize_activations(bases, 200, signal_var=1.0, noise_var=0.0,
                                       rng=np.random.default_rng(5))
    assert X1.shape == (200, 24)
    np.testing.assert_array_equal(w1, np.ones(200))
    np.testing.assert_array_equal(w1, w2)
    np.testing.assert_array_equal(X1, X2)  # determinisme meme rng
    Xn, _ = fg.synthesize_activations(bases, 200, signal_var=1.0, noise_var=0.5,
                                      rng=np.random.default_rng(5))
    assert not np.allclose(X1, Xn)  # le bruit change les activations
