"""Tests pour scripts/notebook_tools/sota_bridge_tests/vector_compare.py

Couvre :
- distance L∞/L2 : identity / mismatch / empty / NaN / dimensions !=
- vector_close : 3 modes (absolute, relative, both) x 2 metriques (linf, l2)
- compare_bridge : 4 statuts, bridge_verdict dataclass, summary lisible

Reference : #11058 (Ponts SOTA : comparer les vecteurs from-scratch <-> oracle).
"""
from __future__ import annotations

import math
import pytest

from scripts.notebook_tools.sota_bridge_tests.vector_compare import (
    vector_linf,
    vector_l2,
    vector_close,
    compare_bridge,
    BridgeVerdict,
)


# ---- vector_linf ---------------------------------------------------------

def test_vector_linf_identique_zero():
    assert vector_linf([0.0, 0.0, 0.0], [0.0, 0.0, 0.0]) == 0.0


def test_vector_linf_identique_non_zero():
    assert vector_linf([0.5, 0.25, 0.75], [0.5, 0.25, 0.75]) == 0.0


def test_vector_linf_un_seul_écart():
    assert vector_linf([1.0, 2.0, 3.0], [1.0, 2.0, 3.5]) == pytest.approx(0.5)


def test_vector_linf_vide_zero():
    assert vector_linf([], []) == 0.0


def test_vector_linf_dimensions_differentes():
    with pytest.raises(ValueError, match="dimensions differentes"):
        vector_linf([1.0, 2.0], [1.0, 2.0, 3.0])


def test_vector_linf_rejette_nan():
    with pytest.raises(ValueError, match="NaN/Inf interdite"):
        vector_linf([1.0, float("nan")], [1.0, 2.0])


def test_vector_linf_rejette_non_numerique():
    with pytest.raises(TypeError, match="non numerique"):
        vector_linf([1.0, "x"], [1.0, 2.0])


# ---- vector_l2 -----------------------------------------------------------

def test_vector_l2_identique_zero():
    assert vector_l2([1.0, 2.0, 3.0], [1.0, 2.0, 3.0]) == 0.0


def test_vector_l2_orthogonal_3_4_5():
    # (3,4) vs (0,0) => sqrt(9+16) = 5.0
    assert vector_l2([3.0, 4.0], [0.0, 0.0]) == pytest.approx(5.0)


def test_vector_l2_vide_zero():
    assert vector_l2([], []) == 0.0


def test_vector_l2_dimensions_differentes():
    with pytest.raises(ValueError, match="dimensions differentes"):
        vector_l2([1.0], [1.0, 2.0])


# ---- vector_close : absolute --------------------------------------------

def test_vector_close_absolute_pass():
    # distance 1e-3, tolerance 1e-2 => ok
    assert vector_close([0.0, 1.0], [1e-3, 1.0], tol=1e-2)


def test_vector_close_absolute_fail():
    # distance 1e-3, tolerance 1e-4 => ko
    assert not vector_close([0.0, 1.0], [1e-3, 1.0], tol=1e-4)


def test_vector_close_absolute_dim_diff_false_pas_crash():
    assert not vector_close([1.0, 2.0], [1.0, 2.0, 3.0], tol=1e-6)


def test_vector_close_absolute_vide_true():
    # Vecteurs vides : distance 0 <= tol => True
    assert vector_close([], [], tol=1e-6)


def test_vector_close_absolute_metric_inconnue():
    with pytest.raises(ValueError, match="metric inconnue"):
        vector_close([1.0], [1.0], tol=1e-6, metric="chebyshev")


def test_vector_close_absolute_mode_inconnu():
    with pytest.raises(ValueError, match="mode inconnu"):
        vector_close([1.0], [1.0], tol=1e-6, mode="hybrid")


# ---- vector_close : relative --------------------------------------------

def test_vector_close_relative_pass():
    # vecteur a = [100.0], b = [100.001], distance 0.001
    # scale = 100.0 -> tol_relative = 1e-3 * 100 = 0.1 ; 0.001 <= 0.1 => ok
    assert vector_close([100.0], [100.001], tol=1e-3, mode="relative")


def test_vector_close_relative_fail_si_petit_vecteur():
    # a = [1.0], b = [1.1], distance 0.1, scale 1.0, tol_relative 1e-3,
    # tol_relative effectif = 1e-3 * 1.0 = 1e-3 ; 0.1 > 1e-3 => KO
    assert not vector_close([1.0], [1.1], tol=1e-3, mode="relative")


def test_vector_close_relative_pass_si_grand_vecteur():
    # a = [100.0], b = [100.1], distance 0.1, scale 100.0, tol_rel_effectif = 0.1
    # 0.1 <= 0.1 -> True
    assert vector_close([100.0], [100.1], tol=1e-3, mode="relative")


def test_vector_close_relative_zero_scale_passe_tol():
    # a = b = [0], distance 0, scale 0, tol=0 => dist <= tol -> True
    assert vector_close([0.0], [0.0], tol=0.0, mode="relative")


def test_vector_close_relative_zero_scale_hors_tol():
    # a = [0], b = [0.5], distance 0.5, scale 0, dist <= 1e-6? non
    assert not vector_close([0.0], [0.5], tol=1e-6, mode="relative")


def test_vector_close_relative_scale_explicite():
    # scale force a 1.0 : dist 1e-3 <= 1e-3 * 1.0 = 1e-3 -> ok
    assert vector_close([1.0], [1.001], tol=1e-3, mode="relative", scale=1.0)


# ---- vector_close : both -------------------------------------------------

def test_vector_close_both_absolute_pass():
    assert vector_close([0.0, 1.0], [1e-3, 1.0], tol=1e-2, mode="both")


def test_vector_close_both_relative_pass_sauf_absolute():
    # dist 1e-3 > abs 1e-6 mais relative pass si scale grand
    assert vector_close(
        [100.0], [100.001], tol=1e-4, mode="both",
    )


def test_vector_close_both_deux_echouent():
    # dist 1e-2, tol 1e-3 abs & relative (scale=1) -> KO sur les deux
    assert not vector_close([1.0], [1.01], tol=1e-3, mode="both")


# ---- vector_close : l2 vs linf ------------------------------------------

def test_vector_close_l2_mismatch_linf_miss():
    # dist L∞ = 0.5 ; dist L2 = 0.5 (vecteur 1D). Tol 0.1.
    # Les deux devraient fail.
    assert not vector_close([0.0], [0.5], tol=0.1, metric="linf")
    assert not vector_close([0.0], [0.5], tol=0.1, metric="l2")


def test_vector_close_linf_vs_l2_sur_vecteur_uniforme():
    # vecteur 1D identite => dist=0 sur les deux
    assert vector_close([1.0], [1.0], tol=0.0, metric="linf")
    assert vector_close([1.0], [1.0], tol=0.0, metric="l2")


# ---- compare_bridge : status, summary, dataclass ------------------------

def test_compare_bridge_concordant():
    v = compare_bridge(
        [1.0, 2.0, 3.0], [1.0, 2.0, 3.0001],
        tol=1e-3, mode="absolute", metric="linf",
    )
    assert isinstance(v, BridgeVerdict)
    assert v.status == "CONCORDANT"
    assert v.distance == pytest.approx(1e-4)
    assert v.max_index == 2
    assert v.max_pair == (3.0, 3.0001)
    assert v.tolerance == 1e-3
    assert v.metric == "linf"
    assert "CONCORDANT" in v.summary
    assert "idx=2" in v.summary
    # as_dict round-trip
    d = v.as_dict()
    assert d["status"] == "CONCORDANT"
    assert d["max_index"] == 2


def test_compare_bridge_divergent():
    v = compare_bridge(
        [1.0, 2.0, 3.0], [1.0, 2.0, 3.5],
        tol=1e-3, mode="absolute", metric="linf",
    )
    assert v.status == "DIVERGENT"
    assert v.distance == pytest.approx(0.5)
    assert v.max_index == 2
    assert v.max_pair == (3.0, 3.5)


def test_compare_bridge_shape_mismatch():
    v = compare_bridge([1.0, 2.0], [1.0, 2.0, 3.0], tol=1e-6)
    assert v.status == "SHAPE_MISMATCH"
    assert math.isinf(v.distance)
    assert v.max_index is None
    assert "dimensions incompatibles" in v.summary


def test_compare_bridge_empty():
    v = compare_bridge([], [])
    assert v.status == "EMPTY"
    assert v.distance == 0.0
    assert v.max_index is None
    assert "vecteurs vides" in v.summary


def test_compare_bridge_label_in_summary():
    v = compare_bridge([1.0], [1.0], tol=1e-6, label="from-scratch vs nashpy")
    assert "from-scratch vs nashpy" in v.summary


def test_compare_bridge_no_label_summary_sans_brackets_vides():
    v = compare_bridge([1.0], [1.0], tol=1e-6)
    # pas de "[...]" vide en tete
    assert not v.summary.startswith(" [")


def test_compare_bridge_relative_mode_label_summary():
    v = compare_bridge(
        [100.0], [100.001],
        tol=1e-3, mode="relative", metric="linf",
        label="MLP",
    )
    assert v.status == "CONCORDANT"
    assert "mode=relative" in v.summary
    assert "MLP" in v.summary


def test_compare_bridge_l2_metric():
    v = compare_bridge(
        [3.0, 4.0], [0.0, 0.0],
        tol=5.0, mode="absolute", metric="l2",
    )
    assert v.status == "CONCORDANT"
    assert v.distance == pytest.approx(5.0)
    assert v.metric == "l2"


def test_compare_bridge_metric_inconnue():
    with pytest.raises(ValueError, match="metric inconnue"):
        compare_bridge([1.0], [1.0], metric="chebyshev")


# ---- Cas-pattern : GT-14 DifferentialGames (PR #11074) ----------------

def test_pattern_gt_14_l_inf_concordant_pythonnet():
    # Reproduction du pattern PR #11074 : 11 vecteurs integrees du meme RK4
    # from-scratch BCL vs MathNet.Numerics RungeKutta.FourthOrder
    from_scratch = [
        0.0, 9.99966667e-04, 1.99986667e-03, 2.99970000e-03,
        3.99946667e-03, 4.99916667e-03, 5.99880001e-03,
        6.99836670e-03, 7.99786668e-03, 8.99730002e-03,
        1.02790000e-05,
    ]
    mathnet = list(from_scratch)  # byte-equal dans le pattern valide
    v = compare_bridge(from_scratch, mathnet, tol=1e-6)
    assert v.status == "CONCORDANT"
    assert v.distance == 0.0


def test_pattern_gt_14_l_inf_divergent_si_pas_meme_pas():
    # Reproduit le bug note dans PR #11074 : si N != N-1 pas, drift de 1.8e-3
    from_scratch_h_correct = [0.0, 0.05, 0.1, 0.15, 0.2]
    mathnet_h_drift = [0.0, 0.04975, 0.0995, 0.14925, 0.199]  # pas 0.04975
    v = compare_bridge(from_scratch_h_correct, mathnet_h_drift, tol=1e-3)
    assert v.status == "DIVERGENT"
    assert v.distance > 1e-3


# ---- Sanity natif : 4 jeux PD/BoS/MP/RPS -------------------------------

def test_pattern_pd_nashpy_vs_from_scratch():
    # PD equilibre pur (Defect, Defect) -> (1, 0) x (1, 0) = [1,0,1,0]
    nashpy_pd = [1.0, 0.0, 1.0, 0.0]
    from_scratch_pd = [1.0, 0.0, 1.0, 0.0]
    v = compare_bridge(nashpy_pd, from_scratch_pd, tol=1e-6)
    assert v.status == "CONCORDANT"
    assert v.distance == 0.0


def test_pattern_bos_mixte_formule_close():
    # BoS mixte (q, 1-q) x (p, 1-p) avec q = 2/3, p = 1/3
    # En notation par paire de strategies : [q, 1-q, p, 1-p] = [2/3, 1/3, 1/3, 2/3]
    nashpy_bos = [2 / 3, 1 / 3, 1 / 3, 2 / 3]
    from_scratch_bos = [2 / 3, 1 / 3, 1 / 3, 2 / 3]
    v = compare_bridge(nashpy_bos, from_scratch_bos, tol=1e-9)
    assert v.status == "CONCORDANT"


def test_pattern_rps_uniforme():
    # RPS equilibre uniforme = [1/3, 1/3, 1/3] x [1/3, 1/3, 1/3]
    # Aplati : [1/3, 1/3, 1/3, 1/3, 1/3, 1/3]
    unif = [1 / 3] * 6
    v = compare_bridge(unif, unif, tol=1e-9)
    assert v.status == "CONCORDANT"
    assert v.distance == 0.0


def test_pattern_non_formule_close_aleatoire():
    # Jeu non formule close : matrice aleatoire 2x2 ; on teste que le helper
    # accepte n'importe quel vecteur raisonnable.
    import random
    random.seed(42)
    a = [random.random() for _ in range(8)]
    b = list(a)  # identique
    v = compare_bridge(a, b, tol=1e-12)
    assert v.status == "CONCORDANT"
    assert v.distance == 0.0


# ---- Re-export ----------------------------------------------------------

def test_vector_compare_public_api():
    # Verifie que les 4 symboles publics sont exposes (le notebook peut les
    # importer directement).
    from scripts.notebook_tools.sota_bridge_tests import vector_compare as vc
    assert callable(vc.vector_linf)
    assert callable(vc.vector_l2)
    assert callable(vc.vector_close)
    assert callable(vc.compare_bridge)
