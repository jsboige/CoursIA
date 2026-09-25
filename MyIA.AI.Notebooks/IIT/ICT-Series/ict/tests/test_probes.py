"""Tests des sondes lineaires factorisees (``ict.probes``, #13564).

Chaque sonde est pinnee par une **propriete falsifiable** plutot que par une
valeur numerique figee : direction retrouvee sur donnees a direction plantee,
degenerescence attendue sous covariance isotrope, alignement PCA...

  1. (Mass-mean) la direction rendue est exactement ``mu_+ - mu_-``.

  2. (MM-IID isotrope) sous covariance isotrope, ``Sigma^{-1} delta`` est
     proportionnelle a ``delta`` : la sonde doit degenerer vers MM (cosinus
     > 0.95).

  3. (MM-IID anisotrope) sous covariance fortement anisotrope **orthogonale**
     au signal, MM est biaisee ; MM-IID doit retrouver la direction plantee et
     battre MM, en cosinus comme en exactitude. C'est la raison d'etre de la
     sonde -- le controle qui falsifie « MM suffit ».

  4. (Logistique separable) a 5 sigma de separation, la sonde LR classe au
     moins 98 % des points.

  5. (Logistique isotrope) sous covariance isotrope, LR converge vers la meme
     direction que MM (cosinus > 0.90) : deux estimateurs coherents du meme
     signal.

  6. (Determinisme) deux appels identiques rendent des sorties identiques au
     bit pres -- aucun tirage dans l'organe.

  7. (Exactitude au hasard) sur labels melanges, les trois sondes sont a la
     chance (|acc - 0.5| < 0.10) : la sonde ne fabrique pas de signal.

  8. (Insensibilite a l'echelle) l'exactitude est invariante a la norme de
     ``theta`` -- c'est la convention ``mu_train`` qui le garantit.

  9. (PCA : invariants) ``align >= 0.5`` toujours, et ``align`` est invariante
     au retournement des labels (la statistique est ``max(a, 1 - a)``).

 10. (PCA : corpus separable) sur un corpus isotrope a separation 1 sigma,
     ``align ~ 0.69`` (mesure) et PC1 pointe vers la direction plantee
     (cosinus > 0.8).

 11. (PCA n'est pas la verite) sur le corpus anisotrope ou le signal est dans
     une direction a **faible** variance, PC1 suit la variance et non le label
     (cosinus < 0.5) alors que MM-IID suit le label (> 0.95) : l'alignement
     PCA ne detecte pas la direction vraie.

 12. (PC1 ancre) la projection moyenne des ``y == 1`` est positive, et
     retourner les labels retourne exactement le vecteur.

 13. (API) ``train_probes`` rend les trois cles ``MM`` / ``LR`` / ``MMIID`` et
     l'origine ``X.mean(0)``.

 14. (d = 1) ``mm_iid_probe`` reste definie en dimension 1 et vaut
     ``delta / var`` (variance ``ddof=1`` des points classe-centres).

 15. (Frontiere) ``ValueError`` sur ``X`` non 2D, ``y`` de mauvaise longueur,
     labels non binaires, et classe unique (qui rendrait un ``NaN`` muet).

Implementation : un seul import numpy + import du package ``ict`` ; toutes les
donnees sont tirees avec ``default_rng(seed)`` -- aucune dependance a l'ordre
des tests ni a l'etat global.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.probes import (
    anchored_pc1,
    logistic_probe,
    mass_mean_probe,
    mm_iid_probe,
    pca_stats,
    probe_accuracy,
    train_probes,
)


def _cos(a: "np.ndarray", b: "np.ndarray") -> float:
    return float(a @ b / (np.linalg.norm(a) * np.linalg.norm(b)))


def _gaussians(
    n: int, d: int, delta: "np.ndarray", cov: "np.ndarray", seed: int
):
    """Deux classes gaussiennes ``+-delta/2`` de covariance ``cov``."""
    rng = np.random.default_rng(seed)
    A = np.linalg.cholesky(cov)
    Xp = delta / 2.0 + rng.standard_normal((n, d)) @ A.T
    Xm = -delta / 2.0 + rng.standard_normal((n, d)) @ A.T
    X = np.concatenate([Xp, Xm], axis=0)
    y = np.concatenate([np.ones(n, dtype=int), np.zeros(n, dtype=int)])
    return X, y


def _unit_direction(d: int, seed: int) -> "np.ndarray":
    rng = np.random.default_rng(seed)
    v = rng.standard_normal(d)
    return v / np.linalg.norm(v)


def _anisotropic_cov(delta: "np.ndarray", lam_signal: float, lam_noise: float):
    """Covariance a variances ``lam_signal`` (sur delta) / ``lam_noise`` (ailleurs)."""
    d = delta.shape[0]
    rng = np.random.default_rng(3)
    Q = np.linalg.qr(rng.standard_normal((d, d)))[0]
    Q[:, 0] = delta
    Q = np.linalg.qr(Q)[0]
    lam = np.array([lam_signal] + [lam_noise] * (d - 1))
    return Q @ np.diag(lam) @ Q.T


# ---------------------------------------------------------------------------
# 1. mass-mean
# ---------------------------------------------------------------------------


def test_mass_mean_probe_is_class_mean_difference():
    """La direction MM est exactement ``mu_+ - mu_-`` (sonde sans parametre)."""
    X, y = _gaussians(40, 3, _unit_direction(3, 0), np.eye(3), seed=0)
    theta = mass_mean_probe(X, y)
    attendu = X[y == 1].mean(axis=0) - X[y == 0].mean(axis=0)
    assert np.allclose(theta, attendu)


# ---------------------------------------------------------------------------
# 2-3. mass-mean IID : degenerescence isotrope, superiorite anisotrope
# ---------------------------------------------------------------------------


def test_mm_iid_degenerates_to_mass_mean_under_isotropic_covariance():
    """Sous covariance isotrope, ``Sigma^{-1} delta`` reste alignee sur MM."""
    d = 8
    delta = _unit_direction(d, 7)
    X, y = _gaussians(400, d, delta, np.eye(d), seed=0)
    assert _cos(mm_iid_probe(X, y), mass_mean_probe(X, y)) > 0.95


def test_mm_iid_beats_mass_mean_under_anisotropic_covariance():
    """Signal dans une direction a faible variance : MM est biaisee, MM-IID non.

    Mesure sur ce corpus (seed fixe) : cos(MM, delta) ~ 0.56 contre
    cos(MM-IID, delta) ~ 0.9996 -- et l'exactitude suit (0.57 -> 0.68).
    """
    d = 8
    delta = _unit_direction(d, 7)
    cov = _anisotropic_cov(delta, lam_signal=1.0, lam_noise=40.0)
    X, y = _gaussians(400, d, delta, cov, seed=1)

    theta_mm = mass_mean_probe(X, y)
    theta_iid = mm_iid_probe(X, y)

    assert _cos(theta_iid, delta) > 0.95, "MM-IID doit retrouver la direction plantee"
    assert _cos(theta_mm, delta) < 0.80, "MM est biaisee par l'anisotropie"
    assert _cos(theta_iid, delta) > _cos(theta_mm, delta) + 0.20

    mu = X.mean(axis=0)
    assert probe_accuracy(theta_iid, mu, X, y) > probe_accuracy(theta_mm, mu, X, y)


# ---------------------------------------------------------------------------
# 4-6. logistique
# ---------------------------------------------------------------------------


def test_logistic_probe_separates_well_separated_data():
    """A 5 sigma de separation, LR classe au moins 98 % des points."""
    d = 8
    delta = _unit_direction(d, 7)
    X, y = _gaussians(200, d, 5.0 * delta, np.eye(d), seed=2)
    theta = logistic_probe(X, y)
    assert probe_accuracy(theta, X.mean(axis=0), X, y) >= 0.98


def test_logistic_probe_agrees_with_mass_mean_under_isotropic_covariance():
    """Sous covariance isotrope, LR et MM estiment la meme direction."""
    d = 8
    delta = _unit_direction(d, 7)
    X, y = _gaussians(400, d, delta, np.eye(d), seed=0)
    assert _cos(logistic_probe(X, y), mass_mean_probe(X, y)) > 0.90


def test_logistic_probe_is_deterministic():
    """Deux appels identiques rendent des sorties identiques au bit pres."""
    X, y = _gaussians(100, 4, _unit_direction(4, 1), np.eye(4), seed=4)
    assert np.array_equal(logistic_probe(X, y), logistic_probe(X, y))


# ---------------------------------------------------------------------------
# 7-8. exactitude
# ---------------------------------------------------------------------------


def test_probe_accuracy_is_chance_on_shuffled_labels():
    """Sur labels melanges, les trois sondes sont a la chance (pas de signal fabrique)."""
    rng = np.random.default_rng(11)
    X = rng.standard_normal((600, 8))
    y = rng.integers(0, 2, 600)
    probes, mu = train_probes(X, y)
    for nom, theta in probes.items():
        acc = probe_accuracy(theta, mu, X, y)
        assert abs(acc - 0.5) < 0.10, f"{nom} : acc={acc} loin de la chance"


def test_probe_accuracy_is_invariant_to_theta_scale():
    """L'exactitude ne depend pas de la norme de ``theta`` (convention ``mu_train``).

    Les facteurs sont des puissances de deux : la multiplication est exacte en
    binaire, donc le seuillage ``score > 0`` est bit-identique -- l'egalite des
    exactitudes est rigoureuse, pas approximative.
    """
    X, y = _gaussians(60, 5, _unit_direction(5, 2), np.eye(5), seed=5)
    theta = mass_mean_probe(X, y)
    mu = X.mean(axis=0)
    acc = probe_accuracy(theta, mu, X, y)
    assert probe_accuracy(2.0 * theta, mu, X, y) == acc
    assert probe_accuracy(0.25 * theta, mu, X, y) == acc


# ---------------------------------------------------------------------------
# 9-12. PCA
# ---------------------------------------------------------------------------


def test_pca_stats_alignment_is_bounded_and_label_swap_symmetric():
    """``align >= 0.5`` toujours, et invariante au retournement des labels."""
    d = 8
    delta = _unit_direction(d, 7)
    X, y = _gaussians(200, d, delta, np.eye(d), seed=6)
    align, Z, comps = pca_stats(X, y)
    assert align >= 0.5
    assert Z.shape == (X.shape[0], 2)
    assert comps.shape == (2, d)
    align_inverse, _, _ = pca_stats(X, 1 - y)
    assert np.isclose(align_inverse, align)


def test_pca_stats_alignment_follows_planted_direction_when_signal_dominates():
    """Corpus isotrope a 1 sigma : ``align`` suit la separabilite (~0.69 mesure)."""
    d = 8
    delta = _unit_direction(d, 7)
    X, y = _gaussians(300, d, delta, np.eye(d), seed=0)
    align, _, comps = pca_stats(X, y)
    assert align > 0.60
    assert _cos(comps[0], delta) > 0.80


def test_pca_pc1_follows_variance_not_truth_under_anisotropy():
    """PC1 suit la variance, pas le label : l'alignement PCA ne detecte pas la verite.

    Meme corpus que ``test_mm_iid_beats_mass_mean_under_anisotropic_covariance``
    (variance 40x hors du signal) : PC1 pointe ailleurs (< 0.5) alors que
    MM-IID pointe juste (> 0.95). C'est le controle que l'organe ``probes``
    existe pour rendre visible -- une PCA bien alignee n'est pas une preuve.
    """
    d = 8
    delta = _unit_direction(d, 7)
    cov = _anisotropic_cov(delta, lam_signal=1.0, lam_noise=40.0)
    X, y = _gaussians(300, d, delta, cov, seed=4)
    _, _, comps = pca_stats(X, y)
    assert _cos(comps[0], delta) < 0.50
    assert _cos(mm_iid_probe(X, y), delta) > 0.95


def test_anchored_pc1_orients_toward_class_one_and_flips_with_labels():
    """PC1 ancre : projection moyenne des ``y == 1`` positive, et negation exacte."""
    d = 8
    delta = _unit_direction(d, 7)
    X, y = _gaussians(200, d, delta, np.eye(d), seed=6)
    Xc = X - X.mean(axis=0)
    v = anchored_pc1(X, y)
    assert float(np.mean(Xc[y == 1] @ v)) > 0.0
    assert float(np.mean(Xc[y == 1] @ v)) > float(np.mean(Xc[y == 0] @ v))
    assert np.allclose(anchored_pc1(X, 1 - y), -v)


# ---------------------------------------------------------------------------
# 13-15. API, dimension 1, frontiere
# ---------------------------------------------------------------------------


def test_train_probes_returns_the_three_probes_and_origin():
    """``train_probes`` rend les cles ``MM`` / ``LR`` / ``MMIID`` et ``X.mean(0)``."""
    X, y = _gaussians(30, 4, _unit_direction(4, 3), np.eye(4), seed=7)
    probes, mu = train_probes(X, y)
    assert set(probes) == {"MM", "LR", "MMIID"}
    assert all(probes[k].shape == (4,) for k in probes)
    assert np.allclose(mu, X.mean(axis=0))


def test_mm_iid_is_defined_in_dimension_one_and_equals_delta_over_var():
    """En dimension 1, ``mm_iid_probe`` vaut ``delta / var`` (points classe-centres)."""
    X = np.array([[0.0], [1.0], [2.0], [3.0]])
    y = np.array([0, 0, 1, 1])
    mu_p, mu_m = X[y == 1].mean(axis=0), X[y == 0].mean(axis=0)
    Xc = np.concatenate([X[y == 1] - mu_p, X[y == 0] - mu_m], axis=0)
    var = float(np.var(Xc, ddof=1))
    attendu = float(mu_p[0] - mu_m[0]) / (var + 1e-3)
    assert np.isclose(mm_iid_probe(X, y)[0], attendu)
    assert np.isclose(mass_mean_probe(X, y)[0], 2.0)


def test_input_validation_rejects_degenerate_inputs():
    """``ValueError`` sur X non 2D, y mal dimensionne, labels non binaires, classe unique."""
    bons_X = np.zeros((4, 2))
    with pytest.raises(ValueError):
        mass_mean_probe(np.zeros(3), np.array([0, 1, 0]))
    with pytest.raises(ValueError):
        mass_mean_probe(bons_X, np.array([0, 1]))
    with pytest.raises(ValueError):
        mass_mean_probe(bons_X, np.array([0, 1, 2, 0]))
    with pytest.raises(ValueError):
        mass_mean_probe(bons_X, np.array([0, 0, 0, 0]))
    with pytest.raises(ValueError):
        mass_mean_probe(bons_X, np.array([1, 1, 1, 1]))