"""Tests des metriques de fidelite SAE de ``ict.sae_calibration`` (#8236, Livrable 1 Phase 0).

Les mesures doivent etre exactes sur des cas synthetiques ou la verite est
connue par construction -- un FVU mal calcule sur un ratio de grandes norms
(bf16 -> float64) fausserait le tableau cross-echelle du notebook de
calibration avant meme la premiere experience.
"""

import numpy as np
import pytest

from ict import sae_calibration as sc


def test_mse_perfect_and_worst_case():
    h = np.array([[1.0, 2.0], [3.0, 4.0], [5.0, 6.0]])
    assert sc.reconstruction_mse(h, h.copy()) == 0.0
    r = np.zeros_like(h)
    assert sc.reconstruction_mse(h, r) == pytest.approx(np.mean(h**2))


def test_fvu_bounds():
    rng = np.random.default_rng(0)
    h = rng.normal(size=(200, 16)) * 10.0
    # reconstruction parfaite
    assert sc.fraction_variance_unexplained(h, h.copy()) == pytest.approx(0.0, abs=1e-12)
    # predire la moyenne du corpus -> FVU = 1 par construction
    mean = np.tile(h.mean(axis=0), (h.shape[0], 1))
    assert sc.fraction_variance_unexplained(h, mean) == pytest.approx(1.0, abs=1e-9)
    # predire zero avec corpus centree -> meme norme residuelle que la moyenne
    centered = h - h.mean(axis=0)
    assert sc.fraction_variance_unexplained(centered, np.zeros_like(centered)) == pytest.approx(1.0, abs=1e-9)


def test_fvu_rejects_degenerate_corpus():
    single = np.array([[1.0, 2.0]])
    with pytest.raises(ValueError, match="variance nulle"):
        sc.fraction_variance_unexplained(single, single.copy())


def test_fvu_stable_on_large_norm_bf16_scale():
    # residual bf16 typique : norms ~1e2 ; le ratio doit rester precis en f64
    rng = np.random.default_rng(1)
    h = rng.normal(size=(500, 32)) * 150.0
    recon = h + rng.normal(size=h.shape) * 0.5
    fvu = sc.fraction_variance_unexplained(h, recon)
    assert 0.0 < fvu < 1.0
    # coherence : FVU ~ sigma_bruit^2 / variance_corpus
    expected = 0.25 / np.var(h)
    assert fvu == pytest.approx(expected, rel=0.15)


def test_l0_measured_counts_nonzero_only():
    # top-4 stocke dont 1 valeur annulee par relu -> L0 = 3
    vals = np.array([[1.0, 0.0, 2.0, 3.0], [0.5, 1.5, 0.0, 2.5]])
    assert sc.l0_measured(vals) == 3.0
    assert sc.l0_measured(np.ones((5, 50))) == 50.0


def test_assert_l0_release_consistent():
    sc.assert_l0_release_consistent(49.2, k_release=50)
    sc.assert_l0_release_consistent(50.0, k_release=50)
    with pytest.raises(AssertionError, match="incoherent"):
        sc.assert_l0_release_consistent(80.0, k_release=50)


def test_dead_features_threshold():
    counts = np.array([100, 50, 1, 0])
    # seuil 5 % : actives sur < 5 tokens -> features 2 (1 token) et 3 (0 token)
    dead = sc.dead_features(counts, n_tokens=100, activation_threshold=0.05)
    assert dead.tolist() == [2, 3]
    # seuil 1 % : seule la feature jamais active passe sous la barre
    assert sc.dead_features(counts, n_tokens=100, activation_threshold=0.01).tolist() == [3]
    # une feature active 50 % du temps reste vive a tous les seuils utiles
    alive_only = [i for i in range(4) if i not in dead.tolist()]
    assert alive_only == [0, 1]


def test_fidelity_report_aggregates_and_guards():
    rng = np.random.default_rng(2)
    t, d, k = 300, 8, 50
    h = rng.normal(size=(t, d))
    # reconstruction credible : projection bruitee
    recon = h + rng.normal(size=(t, d)) * 0.1
    vals = rng.uniform(0.1, 2.0, size=(t, k))
    vals[:10, 3] = 0.0  # 10 tokens ou la feature 3 est selectionnee mais annulee
    counts = np.full(k, t, dtype=np.int64)
    counts[3] = t - 10
    counts[7] = 0  # feature morte sur tout le corpus
    report = sc.fidelity_report(h, recon, vals, counts, k_release=50, label="test / W32K")
    assert report["label"] == "test / W32K"
    assert report["n_tokens"] == t and report["d_model"] == d
    # 10 tokens perdent leur feature 3 annulee par relu : L0 = 49.97, pas k
    assert 49.0 < report["l0_measured"] < 50.0
    assert report["l0_measured"] == pytest.approx(2999.0 / 60.0, abs=0.02)
    assert 0.0 < report["fvu"] < 1.0
    assert report["n_dead_features"] == 1
    assert report["dead_fraction"] == pytest.approx(1 / k)
    # la garde release bloque un rapport incoherent
    vals_f32 = np.ones((t, 32))
    counts_f32 = np.full(32, t, dtype=np.int64)
    with pytest.raises(AssertionError, match="incoherent"):
        sc.fidelity_report(h, recon, vals_f32, counts_f32, k_release=50, label="x")


def test_shape_mismatches_rejected():
    h = np.zeros((10, 4))
    with pytest.raises(ValueError, match="formes incompatibles"):
        sc.reconstruction_mse(h, np.zeros((10, 5)))
    with pytest.raises(ValueError, match="formes incompatibles"):
        sc.fraction_variance_unexplained(h, np.zeros((11, 4)))
    with pytest.raises(ValueError, match="attendu"):
        sc.l0_measured(np.zeros(5))
    with pytest.raises(ValueError, match="attendu"):
        sc.dead_features(np.zeros((2, 2)), n_tokens=5)
