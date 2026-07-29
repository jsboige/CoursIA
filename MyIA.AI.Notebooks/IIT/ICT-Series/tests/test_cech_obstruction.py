"""Tests du module #7744 : cochaîne de Čech pondérée, obstruction entre proxys.

Couvrent :
1. Les **structures relationnelles** (sections, normalisation, transport,
   holonomie, dimensionnalité effective) -- propriétés mécaniques.
2. Le **verdict falsifiable** : 1D affine -> TRIVIAL ; >=2D -> NON_TRIVIAL ;
   <3 proxys -> INCONCLUSIVE. Le banc ``cech_obstruction_test`` doit passer.
3. L'**intégration réelle** : proxys issus de ``ict.spectral`` (le vrai
   moteur) via ``proxy_sections`` -> pipeline complet.

numpy + pytest, CPU uniquement.
"""

import numpy as np
import pytest

from ict.cech_obstruction import (
    cech_obstruction_class,
    cech_obstruction_test,
    cech_obstruction_verdict,
    effective_dimensionality,
    holonomy,
    normalize_sections,
    proxy_sections,
    transport_residual,
)


# --- Proprietes mecaniques : sections ---


def test_proxy_sections_windowing():
    """proxy_sections découpe en fenêtres contiguës et évalue chaque proxy."""
    states = list(range(20))  # 20 états -> window_size=4 -> (20-4)/4 = 4 fenêtres.
    proxies = {
        "sum": lambda s, n: float(np.sum(s)),
        "mean": lambda s, n: float(np.mean(s)),
    }
    secs = proxy_sections(states, n_symbols=20, window_size=4, proxies=proxies)
    assert set(secs.keys()) == {"sum", "mean"}
    assert len(secs["sum"]) == 4  # 4 fenêtres de 4 transitions.
    # Fenêtre 0 = états [0,1,2,3,4], somme = 10.
    np.testing.assert_allclose(secs["sum"][0], 10.0)


def test_proxy_sections_guards():
    with pytest.raises(ValueError):
        proxy_sections([0, 1, 2], n_symbols=1, window_size=2, proxies={"a": lambda s, n: 0.0})
    with pytest.raises(ValueError):
        proxy_sections([0, 1, 2], n_symbols=3, window_size=0, proxies={"a": lambda s, n: 0.0})
    with pytest.raises(ValueError):
        proxy_sections([0, 1, 2], n_symbols=3, window_size=2, proxies={"only_one": lambda s, n: 0.0})
    with pytest.raises(ValueError):
        proxy_sections([0, 1], n_symbols=3, window_size=5, proxies={"a": lambda s, n: 0.0, "b": lambda s, n: 1.0})


def test_normalize_sections_removes_level_and_scale():
    """Centrer-réduire : moyenne ~0, std ~1 ; section constante -> vecteur 0."""
    secs = {"a": np.array([1.0, 2.0, 3.0, 4.0]), "const": np.array([5.0, 5.0, 5.0, 5.0])}
    out = normalize_sections(secs)
    assert abs(out["a"].mean()) < 1e-12
    assert abs(out["a"].std() - 1.0) < 1e-9
    np.testing.assert_allclose(out["const"], np.zeros(4))  # constante -> 0.


# --- Transport residual (cobord, recouvrement double) ---


def test_transport_residual_affine_is_zero():
    """Deux sections affinement liées -> résidu ~0 (le cobord absorbe)."""
    x = np.linspace(0, 10, 50)
    s_i = 3.0 * x + 7.0       # affine en x.
    s_j = -2.0 * x + 1.0      # aussi affine en x (donc affine en s_i).
    res = transport_residual(s_i, s_j)
    assert res["norm"] < 1e-9  # le résidu est absorbé par la relation affine.
    assert abs(res["cosine"]) > 0.999 or abs(res["cosine"]) < -0.999  # |cos|~1.


def test_transport_residual_orthogonal_is_large():
    """Deux sections indépendantes -> résidu non-nul."""
    rng = np.random.default_rng(0)
    s_i = rng.standard_normal(50)
    s_j = rng.standard_normal(50)
    res = transport_residual(s_i, s_j)
    assert res["norm"] > 0.5
    assert abs(res["cosine"]) < 0.5  # structures indépendantes.


def test_transport_residual_shape_guard():
    with pytest.raises(ValueError):
        transport_residual(np.zeros(5), np.zeros(6))
    with pytest.raises(ValueError):
        transport_residual(np.zeros(1), np.zeros(1))


# --- Effective dimensionality (mesure d'obstruction primaire) ---


def test_effective_dimensionality_1d_affine():
    """3 proxys affinement liés -> dim effective 1 (s2/s1 ~0)."""
    rng = np.random.default_rng(0)
    latent = rng.standard_normal(60)
    secs = {"A": 2.5 * latent + 10, "B": -0.8 * latent - 3, "C": 1.3 * latent + 7}
    dim = effective_dimensionality(secs)
    assert dim["s2_over_s1"] < 0.05
    assert dim["effective_rank"] == 1


def test_effective_dimensionality_2d():
    """3 proxys sur 2 latents indépendants -> dim effective 2."""
    rng = np.random.default_rng(0)
    x = rng.standard_normal(60)
    y = rng.standard_normal(60)
    secs = {"A": x, "B": y, "C": x + y}
    dim = effective_dimensionality(secs)
    assert dim["s2_over_s1"] > 0.5
    assert dim["effective_rank"] >= 2


# --- Holonomie (cocycle, recouvrement triple) ---


def test_holonomy_zero_residuals_is_zero():
    z = np.zeros(40)
    h = holonomy(z, z, z)
    assert h["holonomy"] < 1e-12
    assert h["max_abs"] < 1e-12


def test_holonomy_nonzero_residuals():
    r = np.ones(40)
    h = holonomy(r, r, r)  # 1+1+1 = 3 partout.
    np.testing.assert_allclose(h["holonomy"], 3.0)
    assert h["sign_consistency"] > 0.9  # tout positif -> signe cohérent.


# --- Le verdict falsifiable #7744 ---


def test_cech_obstruction_test_passes():
    """Banc falsifiable : aff=TRIVIAL ET multi=NON_TRIVIAL, multi-seed."""
    for seed in range(6):
        report = cech_obstruction_test(n_windows=60, seed=seed)
        assert report["affine_verdict"] == "TRIVIAL", f"seed={seed}: affine should be TRIVIAL"
        assert report["multi_verdict"] == "NON_TRIVIAL", f"seed={seed}: multi should be NON_TRIVIAL"
        assert report["passes"] == 1.0


def test_verdict_affine_trivial():
    rng = np.random.default_rng(2)
    latent = rng.standard_normal(50)
    secs = {"A": 2.0 * latent, "B": -1.0 * latent + 5, "C": 0.5 * latent - 2}
    assert cech_obstruction_verdict(cech_obstruction_class(secs)) == "TRIVIAL"


def test_verdict_multidim_non_trivial():
    rng = np.random.default_rng(3)
    secs = {"A": rng.standard_normal(50), "B": rng.standard_normal(50), "C": rng.standard_normal(50)}
    assert cech_obstruction_verdict(cech_obstruction_class(secs)) == "NON_TRIVIAL"


def test_verdict_less_than_three_proxies_inconclusive():
    """<3 proxys : pas de cocycle triple -> INCONCLUSIVE."""
    rng = np.random.default_rng(4)
    secs = {"A": rng.standard_normal(50), "B": rng.standard_normal(50)}
    assert cech_obstruction_verdict(cech_obstruction_class(secs)) == "INCONCLUSIVE"


def test_cech_obstruction_class_report_fields():
    rng = np.random.default_rng(5)
    secs = {"A": rng.standard_normal(40), "B": rng.standard_normal(40), "C": rng.standard_normal(40)}
    rep = cech_obstruction_class(secs)
    for key in (
        "n_proxies", "n_windows", "pairwise_residuals", "mean_coboundary",
        "triple_holonomies", "mean_cocycle", "obstruction_ratio",
        "effective_rank", "s2_over_s1",
    ):
        assert key in rep, f"champ manquant : {key}"
    assert rep["n_proxies"] == 3
    assert len(rep["pairwise_residuals"]) == 3  # 3 paires.
    assert len(rep["triple_holonomies"]) == 1   # 1 triplet.


# --- Intégration réelle : proxys issus de ict.spectral ---


def test_integration_real_spectral_proxies():
    """proxy_sections + vraies métriques spectral -> pipeline complet valide."""
    from ict import spectral

    rng = np.random.default_rng(7)
    # Trajectoire réaliste (mdp à 6 états, transitions markoviennes).
    P = rng.random((6, 6))
    P /= P.sum(axis=1, keepdims=True)
    states = [0]
    for _ in range(800):
        states.append(int(rng.choice(6, p=P[states[-1]])))

    proxies = {
        "spectral_gap": lambda s, n: float(spectral.spectral_summary(s, n)["spectral_gap"]),
        "density": lambda s, n: float(spectral.spectral_summary(s, n)["density"]),
        "mean_degree": lambda s, n: float(spectral.spectral_summary(s, n)["mean_degree"]),
    }
    secs = proxy_sections(states, n_symbols=6, window_size=40, proxies=proxies)
    assert len(secs["spectral_gap"]) > 5
    rep = cech_obstruction_class(secs)
    verdict = cech_obstruction_verdict(rep)
    # On n'asserte pas la valeur du verdict (dépend du substrat réel) --
    # on vérifie seulement que le pipeline bout-en-bout avec les vrais proxys
    # produit un verdict valide (l'objet expérimental est bien défini).
    assert verdict in ("TRIVIAL", "NON_TRIVIAL", "INCONCLUSIVE")
    assert rep["n_windows"] == len(secs["spectral_gap"])
