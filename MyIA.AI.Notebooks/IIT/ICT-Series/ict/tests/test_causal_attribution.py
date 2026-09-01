"""Tests du module :mod:`ict.causal_attribution` (ICT-Greffe 5, issue #13903).

Chaque test valide une propriete falsifiable de l'attribution causale
d'intervention, numerotee par *gate*. Pattern herite de ``test_argumentation.py``
/ ``test_voi.py`` : bootstrap ``sys.path`` module-level, sans fixtures,
tolerances commentees.

Substance verifiee (mesure first-hand c.292) :

- Gate 1 : estimateur naif retourne la difference brute.
- Gate 2 : backdoor adjustment debiaise quand Z bloque le confondant.
- Gate 3 : backdoor adjustment NON_IDENTIFIABLE quand Z ne bloque pas.
- Gate 4 : variable instrumentale debiaise avec instrument pertinent.
- Gate 5 : variable instrumentale NON_IDENTIFIABLE quand instrument non pertinent.
- Gate 6 : controle negatif -- intervention sans effet, ATE ground truth = 0.
- Gate 7 : verdict tri-etat AGREEMENT sous tolerance, DESACCORD au-dela.
- Gate 8 : validation squelette CausalGraph (refuse graphes invalides).
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import causal_attribution as ca  # noqa: E402


# --------------------------------------------------------------------------- #
#  Gate 1 : estimateur naif retourne la difference brute                      #
# --------------------------------------------------------------------------- #
def test_naive_difference_returns_raw_gap():
    """``E[Y | X=1] - E[Y | X=0]`` rend la difference brute, meme biaisee."""
    outcome_by_treatment = {0: [1.0, 2.0, 3.0], 1: [4.0, 5.0, 6.0]}
    gap = ca.naive_difference(outcome_by_treatment)
    # E[Y|X=1] = 5.0, E[Y|X=0] = 2.0 -> gap = 3.0
    assert abs(gap - 3.0) < 1e-9, f"gap attendu 3.0, recu {gap}"


def test_naive_difference_rejects_missing_modality():
    """``naive_difference`` leve si l'une des modalites manque."""
    with pytest.raises(ValueError, match="modalites 0 et 1"):
        ca.naive_difference({1: [1.0, 2.0]})


# --------------------------------------------------------------------------- #
#  Gate 2 : backdoor adjustment debiaise quand Z bloque le confondant        #
# --------------------------------------------------------------------------- #
def test_backdoor_adjustment_unbiases_when_z_blocks():
    """Simpson : vrai ATE = 5 ; sans ajustement biaise ; avec ajustement OK.

    On genere 200 obs par modalite de Z (2 modalites : ``low`` / ``high``).
    Sous chaque Z, ``E[Y | X=x, Z=z] = 10 + 5 * x + 2 * z`` ; la moyenne
    non ponderee sur Z donne 5 (VRAI) si Z est independant de X. Si on
    force une dependance ``P(X=1 | Z=high) > P(X=1 | Z=low)`` (effet
    selection), l'estimateur naif biaise ; le backdoor adjustment debiaise.
    """
    rng = np.random.default_rng(seed=42)
    n = 1000
    # Z independant, X dependant de Z via confoundant simule
    z = rng.choice(["low", "high"], size=n, p=[0.5, 0.5])
    # P(X=1 | Z=high) = 0.9, P(X=1 | Z=low) = 0.1 -> effet selection
    p_x1 = np.where(z == "high", 0.9, 0.1)
    x = (rng.uniform(size=n) < p_x1).astype(int)
    # Y = 10 + 5*X + 2*Z + bruit
    y = 10.0 + 5.0 * x + 2.0 * np.where(z == "high", 1, 0) + rng.normal(scale=0.5, size=n)

    naive_gap = ca.naive_difference({0: y[x == 0].tolist(), 1: y[x == 1].tolist()})
    ate = ca.backdoor_adjustment(y, x, z, tol_zero=1e-9)

    # Vrai ATE = 5. Le naif doit biaiser (vers le haut, parce que Z=high -> X=1
    # plus probable ET Y plus eleve par Z). Le backdoor doit etre proche de 5.
    assert abs(naive_gap - 5.0) > 0.5, (
        f"naif attendu BIAISE (>0.5 de 5), recu {naive_gap:.3f}"
    )
    assert abs(ate - 5.0) < 0.5, (
        f"backdoor ajuste attendu proche de 5.0, recu {ate:.3f}"
    )


# --------------------------------------------------------------------------- #
#  Gate 3 : backdoor adjustment NON_IDENTIFIABLE quand Z ne bloque pas       #
# --------------------------------------------------------------------------- #
def test_backdoor_adjustment_raises_when_modality_missing():
    """Si une modalite X manque pour une modalite Z, estimand non identifiable.

    Z="a" a X=0 et X=1 (OK), Z="b" n'a QUE X=1 (estimand NON_IDENTIFIABLE pour Z=b).
    """
    y = np.array([10.0, 11.0, 12.0, 13.0])
    x = np.array([0, 1, 1, 1])  # Z="a" a les deux, Z="b" n'a que X=1
    z = np.array(["a", "a", "b", "b"])
    with pytest.raises(ValueError, match="modalite X manquante"):
        ca.backdoor_adjustment(y, x, z)


# --------------------------------------------------------------------------- #
#  Gate 4 : variable instrumentale debiaise avec instrument pertinent        #
# --------------------------------------------------------------------------- #
def test_iv_estimate_unbiased_with_valid_instrument():
    """Z pertinent (Cov(X,Z) > 0) + exogene -> ATE instrumental proche du vrai."""
    rng = np.random.default_rng(seed=7)
    n = 2000
    # Instrument Z, exogene, influence X
    z = rng.normal(size=n)
    # X endogene : Z + confondant U non observe
    u = rng.normal(size=n)
    x = 0.5 * z + 0.7 * u + rng.normal(scale=0.2, size=n)
    # Y = vrai ATE * X + U + bruit ; vrai ATE = 3.0
    y = 3.0 * x + 2.0 * u + rng.normal(scale=0.2, size=n)

    ate_iv = ca.iv_estimate(y.tolist(), x.tolist(), z.tolist())
    # IV doit recuperer 3.0 ; OLS (naif) biaise vers le haut a cause de U
    assert abs(ate_iv - 3.0) < 0.5, (
        f"ATE instrumental attendu proche de 3.0, recu {ate_iv:.3f}"
    )


# --------------------------------------------------------------------------- #
#  Gate 5 : variable instrumentale NON_IDENTIFIABLE si instrument non pertinent #
# --------------------------------------------------------------------------- #
def test_iv_estimate_raises_when_instrument_irrelevant():
    """Z independant de X (Cov(X, Z) ~ 0) -> instrument NON PERTINENT.

    Avec n=1e6 observations i.i.d. N(0,1) independantes, le module leve
    ``NON PERTINENT`` parce que |Cov(X, Z)| ~ 1e-3 reste sous le seuil
    5/sqrt(n) ~ 5e-3 (5-sigma, signal clairement insuffisant).
    """
    rng = np.random.default_rng(seed=11)
    n = 1_000_000
    x = rng.normal(size=n)
    z = rng.normal(size=n)  # independant de X
    y = rng.normal(size=n)
    with pytest.raises(ValueError, match="NON PERTINENT"):
        ca.iv_estimate(y.tolist(), x.tolist(), z.tolist())


# --------------------------------------------------------------------------- #
#  Gate 6 : controle negatif -- intervention sans effet                      #
# --------------------------------------------------------------------------- #
def test_control_intervention_without_effect_returns_zero_ate():
    """Vrai ATE = 0 ; backdoor adjustment doit retourner ~0 ; naive peut biaiser.

    Ce controle est la **negation du pattern ICT-12e** (le EVSI non-informatif
    doit valoir 0). Si l'attribution causale ne sait pas dire 'cette
    intervention n'a pas cause ce changement', elle ne sait rien dire.
    """
    rng = np.random.default_rng(seed=99)
    n = 1000
    z = rng.choice(["a", "b"], size=n)
    x = rng.binomial(1, 0.5, size=n)
    # Vrai ATE = 0 : Y = 5 + 0*X + 0.5*Z + bruit
    y = 5.0 + 0.0 * x + 0.5 * np.where(z == "b", 1, 0) + rng.normal(scale=0.3, size=n)
    ate = ca.backdoor_adjustment(y, x, z)
    assert abs(ate) < 0.2, (
        f"controle negatif : ATE ground truth = 0, attendu |ATE| < 0.2, recu {ate:.3f}"
    )


# --------------------------------------------------------------------------- #
#  Gate 7 : verdict tri-etat (protocole ICT-12e)                            #
# --------------------------------------------------------------------------- #
def test_compare_estimators_agreement_within_tolerance():
    """Deux estimateurs dans la fenetre de tolerance -> AGREEMENT."""
    verdict = ca.compare_estimators(
        {"a": 253000.0, "b": 252796.0},
        tolerance=500.0,
    )
    assert verdict == ca.AttributionVerdict.AGREEMENT, (
        f"verdict attendu AGREEMENT sous tol=500, recu {verdict}"
    )


def test_compare_estimators_disagreement_beyond_tolerance():
    """Deux estimateurs au-dela de la tolerance -> DESACCORD (pas moyenne)."""
    verdict = ca.compare_estimators(
        {"a": 253000.0, "b": 200000.0},
        tolerance=500.0,
    )
    assert verdict == ca.AttributionVerdict.DESACCORD, (
        f"verdict attendu DESACCORD au-dela de tol=500, recu {verdict}"
    )


def test_compare_estimators_requires_at_least_two():
    """Lever si moins de deux estimateurs -- on ne peut pas comparer seul."""
    with pytest.raises(ValueError, match=">= 2 estimateurs"):
        ca.compare_estimators({"a": 1.0}, tolerance=0.1)


# --------------------------------------------------------------------------- #
#  Gate 8 : validation squelette CausalGraph                                  #
# --------------------------------------------------------------------------- #
def test_causal_graph_rejects_self_loop():
    """``treatment == outcome`` est incoherent -- intervention ne peut pas
    etre sa propre reponse."""
    with pytest.raises(ValueError, match="treatment == outcome"):
        ca.CausalGraph(treatment="X", outcome="X")


def test_causal_graph_rejects_confounder_equals_treatment():
    """Un confounder ne peut pas etre X ou Y."""
    with pytest.raises(ValueError, match="ne peut pas etre treatment"):
        ca.CausalGraph(treatment="X", outcome="Y", confounders=("X",))


def test_causal_graph_accepts_valid_skeleton():
    """Un squelette valide (X, Y, Z confondant, Z2 instrument) est accepte."""
    g = ca.CausalGraph(
        treatment="X",
        outcome="Y",
        confounders=("Z1",),
        instrument="Z2",
    )
    assert g.treatment == "X"
    assert g.outcome == "Y"
    assert g.confounders == ("Z1",)
    assert g.instrument == "Z2"
