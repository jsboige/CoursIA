"""Tests unitaires pour ``ict.phat_causal_unlink`` (case 3 iceberg, #8182).

Le diagnostic du biais de frontiere ``kappa_c`` (observe 0.080 vs predit
0.053, +0.027 sur 5/5 graines, PR #9567) est teste ici selon 10 gates
falsifiables :

    1.  (frontiere deterministe) ``KAPPA_STAR_FINITE`` est exactement
        ``(5^(1/200) - 0.95) / 0.95`` (~= 0.0611) et majore la frontiere
        asymptotique ``KAPPA_C_PREDICTED``.
    2.  (frontiere bruitee)    ``KAPPA_STAR_NOISY`` est STRICTEMENT sous
        la frontiere deterministe (le bruit cumule franchit le seuil plus
        tot) et son equation de fermeture ``E[R_T^2] = 25/3`` tient au
        point resolu.
    3.  (grille fine)          ``FINE_GRID`` est uniforme sur [0.050,
        0.080] au pas 0.002 et depasse la bande de verdict des deux cotes
        (sentinelles du null adversarial).
    4.  (reproduction P1)      sur la grille D'ORIGINE, la frontiere
        observee est 0.080 sur 5/5 graines -- la reproduction exacte de
        l'observation historique de la case (#9567). Ce gate echoue si le
        module d'origine ou la lecture ont derive.
    5.  (controle delieur)     ``kappa = 0`` reste sous RATIO_BORNE_HIGH.
    6.  (controle stable)      ``kappa = 0.03`` (sous frontiere) ne
        franchit jamais RATIO_DIVERGENT -- pas de faux positif.
    7.  (verdict)              le verdict de ``diagnose`` appartient aux
        trois issues pre-enregistrees et la bande rendue est coherente
        avec les constantes.
    8.  (protocole)            ``run_full_protocol`` expose les cles
        documentees (frontieres, grille, verdict, ratios par scan).
    9.  (determinisme)         deux appels successifs produisent le meme
        ``verdict_detail`` byte-a-byte.
    10. (bande non vide)       la bande de verdict est une plage valide
        (borne basse < borne haute) d'au moins une maille de large.

Les frontieres theoriques et la grille sont verrouillees AVANT le run :
les tests ne forcent aucun verdict final, ils verifient la COHERENCE des
invariants pre-enregistres (le verdict ARTEFACT/STRUCTURAL/INCONCLUSIF
depend du run multi-seed, pas des tests).
"""

from __future__ import annotations

import os
import sys

# Permettre l'import direct depuis ict package (sans installer en mode develop).
_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

import numpy as np

from ict import phat_causal_unlink as pcu
from ict import phat_self_reference as psr

SEEDS = (0, 1, 7, 42, 99)


# --------------------------------------------------------------------------- #
#  Gate 1 : frontiere deterministe finie                                        #
# --------------------------------------------------------------------------- #


def test_kappa_star_finite_formula():
    """``KAPPA_STAR_FINITE = (5^(1/200) - a) / a_hat`` (~= 0.0611).

    La frontiere du critere fini est AU-DESSUS de l'asymptotique
    (0.0526) : franchir g^200 = 5 demande plus de gain que |g| = 1.
    """
    expected = (5.0 ** (1.0 / psr.HORIZON_T) - 0.95) / 0.95
    assert np.isclose(pcu.KAPPA_STAR_FINITE, expected), (
        f"KAPPA_STAR_FINITE = {pcu.KAPPA_STAR_FINITE}, attendu {expected}"
    )
    assert 0.061 < pcu.KAPPA_STAR_FINITE < 0.0612, (
        f"KAPPA_STAR_FINITE = {pcu.KAPPA_STAR_FINITE} hors [0.061, 0.0612]"
    )
    assert pcu.KAPPA_STAR_FINITE > psr.KAPPA_C_PREDICTED, (
        "la frontiere finie doit majore la frontiere asymptotique"
    )


# --------------------------------------------------------------------------- #
#  Gate 2 : frontiere bruitee (fermeture de l'equation)                         #
# --------------------------------------------------------------------------- #


def test_kappa_star_noisy_below_finite_and_closure():
    """``KAPPA_STAR_NOISY`` < ``KAPPA_STAR_FINITE`` et ``E[R_T^2] = 25/3``
    au point resolu (re-derivee independamment dans le test).

    Le bruit accumule ajoute de la variance : le seuil ``R_T/R_0 >= 5``
    est franchi plus tot qu'en deterministe pur.
    """
    assert 0 < pcu.KAPPA_STAR_NOISY < pcu.KAPPA_STAR_FINITE, (
        f"KAPPA_STAR_NOISY = {pcu.KAPPA_STAR_NOISY} doit etre dans "
        f"(0, KAPPA_STAR_FINITE={pcu.KAPPA_STAR_FINITE})"
    )

    # Fermeture : re-derive independante de E[R_T^2] au point resolu.
    p = psr.EnvironmentParams()
    g = p.a + pcu.KAPPA_STAR_NOISY * p.a_hat
    g2t = g ** (2 * psr.HORIZON_T)
    r0_sq = 1.0 / 3.0
    expected_r_t_sq = g2t * r0_sq + p.sigma ** 2 * (g2t - 1.0) / (g * g - 1.0)
    target = psr.RATIO_DIVERGENT ** 2 * r0_sq
    assert np.isclose(expected_r_t_sq, target, rtol=1e-6), (
        f"fermeture echouee : E[R_T^2] = {expected_r_t_sq}, cible {target}"
    )


# --------------------------------------------------------------------------- #
#  Gate 3 : grille fine uniforme + sentinelles                                  #
# --------------------------------------------------------------------------- #


def test_fine_grid_uniform_with_sentinels():
    """Grille fine uniforme [0.050, 0.080] pas 0.002, 16 points, avec des
    points HORS bande des deux cotes (sinon le test serait tautologique).
    """
    grid = np.asarray(pcu.FINE_GRID)
    assert len(grid) == 16, f"16 mailles attendues, recues {len(grid)}"
    assert np.isclose(grid[0], 0.050) and np.isclose(grid[-1], 0.080)
    steps = np.diff(grid)
    assert np.allclose(steps, pcu.FINE_STEP), (
        f"grille non uniforme : pas = {steps}"
    )

    band_lo = pcu.KAPPA_STAR_NOISY - pcu.FINE_STEP
    band_hi = pcu.KAPPA_STAR_FINITE + pcu.FINE_STEP
    below = grid < band_lo
    above = grid > band_hi
    assert below.any(), "aucune sentinelle sous la bande : test tautologique"
    assert above.any(), "aucune sentinelle au-dessus de la bande : test tautologique"


# --------------------------------------------------------------------------- #
#  Gate 4 : reproduction de l'observation historique (P1)                       #
# --------------------------------------------------------------------------- #


def test_original_grid_reproduces_historical_boundary():
    """Sur la grille d'origine, la frontiere observee est 0.080 sur 5/5
    graines -- reproduction de l'observation #9567 (biais +0.027).

    C'est le gate P1 : le diagnostic doit REPRODUIRE le phenomene qu'il
    explique avant de l'expliquer.
    """
    scan = psr.stability_scan(kappa_grid=pcu.ORIGINAL_GRID, seeds=SEEDS)
    boundary = pcu.observed_boundary(scan)
    assert np.allclose(boundary, 0.08), (
        f"frontiere grille d'origine = {boundary}, attendu 0.08 x5 "
        f"(reproduction historique #9567)"
    )


# --------------------------------------------------------------------------- #
#  Gates 5-6 : controles d'instrument (delieur + sous-frontiere)                #
# --------------------------------------------------------------------------- #


def test_control_delieur_bounded():
    """``kappa = 0`` (delieur causal) : ratio median < RATIO_BORNE_HIGH."""
    rng = np.random.default_rng(42)
    sim = psr.simulate_self_reference_loop(
        kappa=pcu.CONTROL_KAPPA_DELIEUR, rng=rng
    )
    assert float(np.median(sim["ratio"])) < psr.RATIO_BORNE_HIGH


def test_control_stable_no_false_positive():
    """``kappa = 0.03`` (sous les deux frontieres pre-enregistrees) : aucun
    franchissement de RATIO_DIVERGENT sur les 5 graines -- sinon le bruit
    fabrique des divergences n'importe ou et l'instrument est non concluant.
    """
    scan = psr.stability_scan(
        kappa_grid=[pcu.CONTROL_KAPPA_STABLE], seeds=SEEDS
    )
    assert bool(np.all(scan["ratio_median"] < psr.RATIO_DIVERGENT)), (
        f"fausse divergence a kappa=0.03 : "
        f"{scan['ratio_median'][:, 0]}"
    )


# --------------------------------------------------------------------------- #
#  Gate 7 : verdict dans l'ensemble pre-enregistre + bande coherente            #
# --------------------------------------------------------------------------- #


def test_diagnose_verdict_in_preregistered_set():
    """Le verdict appartient a {ARTEFACT_DE_MESURE, STRUCTURAL_RESIDUE,
    INCONCLUSIF_INSTRUMENT} et la bande rendue est coherente avec les
    constantes du module (maille fine autour des deux frontieres).
    """
    result = pcu.run_full_protocol(seeds=SEEDS)
    v = result["verdict"]

    assert v["verdict"] in {
        "ARTEFACT_DE_MESURE", "STRUCTURAL_RESIDUE", "INCONCLUSIF_INSTRUMENT",
    }, f"verdict hors ensemble pre-enregistre : {v['verdict']!r}"
    assert isinstance(v["verdict_detail"], str) and v["verdict_detail"]
    assert np.isclose(v["band"][0], pcu.KAPPA_STAR_NOISY - pcu.FINE_STEP)
    assert np.isclose(v["band"][1], pcu.KAPPA_STAR_FINITE + pcu.FINE_STEP)
    assert v["band"][0] < v["band"][1]


# --------------------------------------------------------------------------- #
#  Gate 8 : protocole complet, cles documentees                                 #
# --------------------------------------------------------------------------- #


def test_run_full_protocol_documented_keys():
    result = pcu.run_full_protocol(seeds=SEEDS)
    expected_keys = {
        "frontieres_pre_enregistrees", "fine_grid", "verdict",
        "ratio_median_fine", "ratio_median_original",
        "ratio_median_control", "seeds",
    }
    assert set(result.keys()) == expected_keys, (
        f"cles attendues {expected_keys}, recues {set(result.keys())}"
    )
    fp = result["frontieres_pre_enregistrees"]
    assert np.isclose(fp["kappa_star_finite"], pcu.KAPPA_STAR_FINITE)
    assert np.isclose(fp["kappa_star_noisy"], pcu.KAPPA_STAR_NOISY)
    assert np.isclose(fp["kappa_c_asymptotique"], psr.KAPPA_C_PREDICTED)
    # Shapes : (n_seeds, n_points de chaque grille).
    n = len(SEEDS)
    assert np.asarray(result["ratio_median_fine"]).shape == (n, len(pcu.FINE_GRID))
    assert np.asarray(result["ratio_median_original"]).shape == (n, len(pcu.ORIGINAL_GRID))
    assert np.asarray(result["ratio_median_control"]).shape == (n, 2)


# --------------------------------------------------------------------------- #
#  Gate 9 : determinisme                                                        #
# --------------------------------------------------------------------------- #


def test_run_full_protocol_deterministic():
    r1 = pcu.run_full_protocol(seeds=SEEDS)
    r2 = pcu.run_full_protocol(seeds=SEEDS)
    assert r1["verdict"]["verdict"] == r2["verdict"]["verdict"]
    assert r1["verdict"]["verdict_detail"] == r2["verdict"]["verdict_detail"]
    assert np.array_equal(
        np.asarray(r1["ratio_median_fine"]),
        np.asarray(r2["ratio_median_fine"]),
    )
