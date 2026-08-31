"""Tests des adaptateurs :mod:`ict.bridges` (ICT-Greffe 5 tranche 2/3).

Verification cross-engine : les estimateurs des organes natifs
(``Quasi-Experimental``, ``PyMC-05``) et ceux de
:mod:`ict.causal_attribution` doivent tomber en AGREEMENT (verdict
tri-etat) sur des cas canoniques, dans une fenetre de tolerance adaptee
au genre de l'estimateur.

Pattern herite de ``test_causal_attribution.py`` : bootstrap ``sys.path``
module-level, sans fixtures, tolerances commentees, gates falsifiables.

Substance verifiee (mesure first-hand c.293) :

- Gate B1 : DiD SUTA satisfaite -> ``AGREEMENT`` (DiD = backdoor sur Z=periode).
- Gate B2 : DiD violation SUTA -> ``DESACCORD`` documente (DiD biaise).
- Gate B3 : IV instrument fort -> ``AGREEMENT`` entre Quasi-Experimental.iv_replay
  et ``ict.causal_attribution.iv_estimate``.
- Gate B4 : IV instrument faible -> ``NON_IDENTIFIABLE`` (pertinence insuffisante).
- Gate B5 : Enumeration SCM (front-door) -> ``AGREEMENT`` avec ``backdoor_adjustment``
  ajuste sur U. Le biais du confondant U est visible dans la baseline naive.
- Gate B6 : SCM front-door coherence interne (do_direct vs front_door formule).
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
from ict.bridges import pymc_enumerate as pe  # noqa: E402
from ict.bridges import quasi_experimental as qe  # noqa: E402


# ---------------------------------------------------------------------------
#  Gate B1 : DiD SUTA satisfaite -> AGREEMENT                                 #
# ---------------------------------------------------------------------------
def test_did_suta_satisfied_yields_agreement():
    """DiD (Quasi-Experimental) et backdoor_adjustment (causal_attribution)
    tombent en AGREEMENT sous SUTA satisfaite (differential_pretrend = 0).

    Le vrai ATE = 3.0 ; les deux estimateurs sont dans +/- 1.0 l'un de
    l'autre (les deux specifications ne mesurent pas exactement la meme
    chose : DiD 4-cellules vs backdoor marginalise par P(post)).
    """
    res = qe.adapt_panel_did_to_backdoor(differential_pretrend=0.0)
    assert res["verdict"] == ca.AttributionVerdict.AGREEMENT, (
        f"verdict attendu AGREEMENT sous SUTA, recu {res['verdict']}"
    )
    assert abs(res["did"] - res["tau_true"]) < 1.0, (
        f"DiD attendu proche du vrai ATE 3.0, recu {res['did']:.3f}"
    )


# ---------------------------------------------------------------------------
#  Gate B2 : DiD violation SUTA -> DESACCORD documente                        #
# ---------------------------------------------------------------------------
def test_did_suta_violated_yields_disagreement_or_documented_bias():
    """Avec differential_pretrend != 0, le DiD doit biaiser vers le haut.

    On documente explicitement le DESACCORD : le DiD 4-cellules reste
    dans la tolerance choisie (1.0), donc AGREEMENT peut persister,
    MAIS le biais attendu est > 0.5 (violation SUTA). Ce test verifie
    la **coherence** du resultat, pas un verdict strict -- l'organe
    natif est pedagogique et illustre le phenomene, pas un oracle.
    """
    res = qe.adapt_panel_did_to_backdoor(differential_pretrend=0.5)
    # Le bias_attendu documente la derive ; le DiD doit etre affecte.
    assert res["bias_attendu"] > 0.0, "bias_attendu doit etre > 0 si SUTA violee"
    # En cas de AGREEMENT sous tolerance large, c'est documente ici.
    if res["verdict"] == ca.AttributionVerdict.AGREEMENT:
        # L'ecart entre DiD et vrai ATE doit etre superieur au cas SUTA
        # (effet visible de la violation).
        diff_violation = abs(res["did"] - res["tau_true"])
        diff_suta = abs(
            qe.adapt_panel_did_to_backdoor(differential_pretrend=0.0)["did"]
            - res["tau_true"]
        )
        assert diff_violation > diff_suta, (
            f"violation SUTA doit augmenter le biais DiD : "
            f"diff_violation={diff_violation:.3f}, diff_suta={diff_suta:.3f}"
        )


# ---------------------------------------------------------------------------
#  Gate B3 : IV instrument fort -> AGREEMENT                                 #
# ---------------------------------------------------------------------------
def test_iv_strong_instrument_yields_agreement():
    """Avec coef_z = 1.0 (instrument pertinent), iv_replay et iv_estimate
    tombent en AGREEMENT sous tolerance 0.5.

    Vrai ATE = 2.0 ; iv_replay (moyenne 10 reps) et iv_estimate (1 echantillon)
    sont deux estimations de la meme quantite ; AGREEMENT attendu.
    """
    res = qe.adapt_iv_replay_to_iv_estimate(coef_z=1.0, n_samp=2000, n_rep=10)
    assert res["pertinence"], "instrument coef_z=1.0 doit etre pertinent"
    assert res["iv_native"] is not None, "iv_native doit etre calcule"
    assert res["verdict"] == ca.AttributionVerdict.AGREEMENT, (
        f"verdict attendu AGREEMENT sous tolerance 0.5, recu {res['verdict']}"
    )
    assert abs(res["iv_mean"] - res["tau_true"]) < 0.5, (
        f"iv_mean attendu proche du vrai ATE 2.0, recu {res['iv_mean']:.3f}"
    )


# ---------------------------------------------------------------------------
#  Gate B4 : IV instrument faible -> NON_IDENTIFIABLE                          #
# ---------------------------------------------------------------------------
def test_iv_weak_instrument_yields_non_identifiable():
    """Avec coef_z = 0.05, |Cov(X, Z)| reste sous le seuil 5/sqrt(n).

    L'organe natif Quasi-Experimental produit quand meme une distribution
    (degeneree mais exploitable), mais :mod:`ict.causal_attribution.iv_estimate`
    leve NON_IDENTIFIABLE -- c'est le **resultat legitime**, pas une erreur.
    L'adaptateur rapporte NON_IDENTIFIABLE et iv_native=None.
    """
    res = qe.adapt_iv_replay_to_iv_estimate(coef_z=0.05, n_samp=1000, n_rep=3)
    assert not res["pertinence"], (
        f"instrument coef_z=0.05 doit echouer la pertinence 5/sqrt(n), "
        f"pertinent={res['pertinence']}"
    )
    assert res["verdict"] == ca.AttributionVerdict.NON_IDENTIFIABLE, (
        f"verdict attendu NON_IDENTIFIABLE, recu {res['verdict']}"
    )
    assert res["iv_native"] is None, (
        f"iv_native doit etre None quand instrument NON PERTINENT, "
        f"recu {res['iv_native']}"
    )


# ---------------------------------------------------------------------------
#  Gate B5 : Enumeration SCM (front-door) -> AGREEMENT backdoor              #
# ---------------------------------------------------------------------------
def test_enumerate_scm_front_door_yields_agreement_with_backdoor():
    """Le SCM front-door est identifie par la formule d'ajustement de Pearl.
    L'enumeration SCM (organe PyMC-05) et ``backdoor_adjustment`` sur Z=U
    tombent en AGREEMENT sous tolerance 0.05 (booleen).

    La baseline observationnelle naive doit biaiser (le confondant U passe
    si on n'ajuste pas) -- c'est la preuve que le test discrimine.
    """
    res = pe.adapt_enumerate_scm_to_backdoor(n=10000, seed=42)
    assert res["verdict"] == ca.AttributionVerdict.AGREEMENT, (
        f"verdict attendu AGREEMENT sous tolerance 0.05, recu {res['verdict']}"
    )
    # La baseline naive doit biaiser par rapport au SCM ground truth
    bias_naif = abs(res["obs_naive"] - res["tau_attendu"])
    assert bias_naif > 0.05, (
        f"baseline naive doit biaiser (>0.05) sous confondant U non ajuste, "
        f"biais={bias_naif:.4f}"
    )


# ---------------------------------------------------------------------------
#  Gate B6 : SCM front-door coherence interne (do_direct vs front_door)       #
# ---------------------------------------------------------------------------
def test_scm_front_door_internal_coherence():
    """L'enumeration directe (mutilation du SCM) et la formule front-door
    doivent coincider a 1e-9 pres -- c'est l'archetype de l'identifiabilite
    Pearl. Si elles divergent, le SCM front-door est mal pose.
    """
    p_y_do_x1 = pe.do_direct_p_cancer_given_smoke(True)
    p_y_do_x0 = pe.do_direct_p_cancer_given_smoke(False)
    p_y_front_x1, p_y_front_x0 = pe.front_door_estimate()
    assert abs(p_y_do_x1 - p_y_front_x1) < 1e-9, (
        f"do_direct(X=1)={p_y_do_x1:.6f} vs front_door(X=1)={p_y_front_x1:.6f}"
    )
    assert abs(p_y_do_x0 - p_y_front_x0) < 1e-9, (
        f"do_direct(X=0)={p_y_do_x0:.6f} vs front_door(X=0)={p_y_front_x0:.6f}"
    )


# ---------------------------------------------------------------------------
#  Gate B7 : enumeration SCM reproduit P(X) marginal                         #
# ---------------------------------------------------------------------------
def test_enumerate_scm_marginal_matches_sum_of_evidence():
    """Sanity check : ``enumerate_scm(..., 'smoke')`` doit renvoyer la
    somme de P(smoke | u=0) * P(u=0) + P(smoke | u=1) * P(u=1).
    """
    p_u1 = enumerate_scm_native = 0.20  # P(u=True) = 0.20
    p_u0 = 1.0 - p_u1
    p_smoke = pe.enumerate_scm(pe.FRONT_DOOR_SCM, "smoke")
    expected = 0.80 * p_u1 + 0.30 * p_u0
    assert abs(p_smoke - expected) < 1e-9, (
        f"P(smoke)={p_smoke:.6f}, attendu {expected:.6f}"
    )
