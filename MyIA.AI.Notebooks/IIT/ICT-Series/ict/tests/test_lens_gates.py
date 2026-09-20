"""Tests CPU deterministes des gates geometriques (issue #15480, tranche 2a)."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import numpy as np
import pytest

from ict.lens_gates import (
    GateError,
    additivity_residual,
    heldout_linear_score,
    principal_angles,
    separation_zscore,
    subspace_overlap,
)


# ---------------------------------------------------------------------------
# heldout_linear_score : gate F-Lens belief
# ---------------------------------------------------------------------------


def _readout_data(n: int, noise: float, seed: int):
    rng = np.random.default_rng(seed)
    feats = rng.normal(size=(n, 6))
    true_w = rng.normal(size=(6, 3))
    targets = feats @ true_w + noise * rng.normal(size=(n, 3))
    return feats, targets


def test_readout_lineaire_sans_bruit_r2_proche_de_1():
    feats, targets = _readout_data(400, noise=0.0, seed=1)
    out = heldout_linear_score(feats, targets, test_frac=0.3, seed=2)
    assert out["r2"] > 0.999
    assert out["rmse"] < 1e-6


def test_readout_bruite_r2_descend_et_restre_reproductible():
    feats, targets = _readout_data(600, noise=0.5, seed=3)
    a = heldout_linear_score(feats, targets, seed=4)
    b = heldout_linear_score(feats, targets, seed=4)
    assert a == b
    # features desappariees (melangees) : le readout perd l'information -> R2 effondre
    rng = np.random.default_rng(99)
    shuffled = feats[rng.permutation(len(feats))]
    c = heldout_linear_score(shuffled, targets, seed=4)
    assert c["r2"] < 0.2 < a["r2"] < 1.0
    assert a["rmse"] > 0.0


def test_readout_rejette_formes_et_cible_constante():
    with pytest.raises(GateError):
        heldout_linear_score(np.zeros((10, 2)), np.zeros(10))
    feats = np.ones((10, 2))
    cible_constante = np.full((10, 1), 5.0)
    with pytest.raises(GateError):
        heldout_linear_score(feats, cible_constante, seed=0)


# ---------------------------------------------------------------------------
# angles principaux et recouvrement de sous-espaces
# ---------------------------------------------------------------------------


def test_sous_espaces_orthogonaux_angles_droits_recouvrement_nul():
    rng = np.random.default_rng(5)
    u = rng.normal(size=(30, 3))
    v = rng.normal(size=(30, 3))
    # orthogonalise v par rapport a u
    q_u, _ = np.linalg.qr(u)
    v_proj = v - q_u @ (q_u.T @ v)
    theta = principal_angles(u, v_proj)
    assert np.allclose(theta, np.pi / 2, atol=1e-8)
    assert subspace_overlap(u, v_proj) == pytest.approx(0.0, abs=1e-8)


def test_sous_espaces_identiques_angles_nuls_recouvrement_un():
    rng = np.random.default_rng(6)
    u = rng.normal(size=(20, 2))
    # meme sous-espace, base differente (melange lineaire inversible)
    mix = u @ np.array([[1.0, 0.3], [-0.2, 0.9]])
    theta = principal_angles(u, mix)
    # atol=1e-6, PAS 1e-8 : principal_angles rend arccos(clip(s)) et s vaut 1 a
    # 1 ulp pres pour deux bases du meme sous-espace ; arccos AMPLIFIE cet ULP
    # en sqrt(2*eps) ~ 1.49e-8, au-dessus de 1e-8 selon la LAPACK employee
    # (mesure : numpy 1.26.4 -> serie 1.0 exacte, numpy 2.5.3 -> 0.9999999999999999).
    # Meme tolerance que le test frere recouvrement_partiel (abs=1e-6), qui
    # mesure la meme metrique.
    assert np.allclose(theta, 0.0, atol=1e-6)
    assert subspace_overlap(u, mix) == pytest.approx(1.0, abs=1e-8)


def test_recouvrement_partiel_2_dimensions_partagees_sur_3():
    rng = np.random.default_rng(7)
    u = rng.normal(size=(40, 3))
    w = rng.normal(size=(40, 2))
    q_u, _ = np.linalg.qr(u)
    w_orth = w - q_u @ (q_u.T @ w)
    # v partage les 2 premieres directions de u + une direction hors de u
    v = np.hstack([u[:, :2], w_orth[:, :1]])
    theta = principal_angles(u, v)
    assert theta[0] == pytest.approx(0.0, abs=1e-6)
    assert theta[1] == pytest.approx(0.0, abs=1e-6)
    assert theta[2] == pytest.approx(np.pi / 2, abs=1e-6)
    ov = subspace_overlap(u, v)
    # 2 angles nuls + 1 droit : cos^2 = 2, normalise par min(3,3)=3
    assert ov == pytest.approx(2.0 / 3.0, abs=1e-6)


def test_base_de_rang_deficient_rejetee():
    u = np.array([[1.0, 2.0], [2.0, 4.0], [0.0, 0.0]])  # colonnaire
    with pytest.raises(GateError):
        principal_angles(u, np.eye(3)[:, :2])


# ---------------------------------------------------------------------------
# additivite
# ---------------------------------------------------------------------------


def test_additivite_exacte_residu_nul_et_perturbe_croissant():
    rng = np.random.default_rng(8)
    xa = rng.normal(size=(25, 4))
    xb = rng.normal(size=(25, 4))
    x = xa + xb
    assert additivity_residual(x, xa, xb) == pytest.approx(0.0, abs=1e-12)
    r_small = additivity_residual(x + 0.01 * rng.normal(size=(25, 4)), xa, xb)
    r_big = additivity_residual(x + 1.0 * rng.normal(size=(25, 4)), xa, xb)
    assert 0.0 < r_small < r_big
    with pytest.raises(GateError):
        additivity_residual(np.zeros((3, 2)), np.zeros((3, 2)), np.zeros((3, 2)))


# ---------------------------------------------------------------------------
# separation vs partitions aleatoires (H4)
# ---------------------------------------------------------------------------


def _blobs(n_per: int, gap: float, seed: int):
    rng = np.random.default_rng(seed)
    centers = np.array([[0.0, 0.0], [gap, 0.0], [0.0, gap]])
    feats = np.vstack([c + 0.1 * rng.normal(size=(n_per, 2)) for c in centers])
    labels = np.repeat(np.arange(3), n_per)
    return feats, labels


def test_blobs_bien_separes_z_eleve_blobs_confondus_z_faible():
    feats_far, labels = _blobs(120, gap=6.0, seed=9)
    out_far = separation_zscore(feats_far, labels, n_random=100, seed=10)
    assert out_far["z"] > 20.0
    assert out_far["separation_vraie"] > out_far["separation_aleatoire_moyenne"]

    feats_near, _ = _blobs(120, gap=0.05, seed=9)  # memes etiquettes, classes confondues
    out_near = separation_zscore(feats_near, labels, n_random=100, seed=10)
    assert out_near["z"] < out_far["z"]


def test_relabelisation_aleatoire_pure_z_proche_de_zero():
    rng = np.random.default_rng(11)
    feats = rng.normal(size=(300, 4))  # aucune structure de classe
    labels = rng.integers(0, 3, size=300)
    out = separation_zscore(feats, labels, n_random=200, seed=12)
    assert abs(out["z"]) < 3.0


def test_separation_rejette_entrees_invalides():
    # np.errstate : la premiere entree est VOLONTAIREMENT degeneree (zeros), et
    # numpy emet un RuntimeWarning "invalid value encountered in subtract" depuis
    # le calcul de separation AVANT que la garde ne rejette. On le declare ici
    # (scoped a l'appel fautif) plutot que de laisser le warning polluer la
    # sortie de suite ; on ne masque rien du contrat teste, qui reste le rejet.
    with np.errstate(invalid="ignore"), pytest.raises(GateError):
        separation_zscore(np.zeros((10, 2)), np.zeros(10), n_random=5)
    # n_random < 2 est valide AVANT tout calcul : aucune valeur degeneree evaluee.
    with pytest.raises(GateError):
        separation_zscore(np.zeros((10, 2)), np.zeros(10), n_random=1)
