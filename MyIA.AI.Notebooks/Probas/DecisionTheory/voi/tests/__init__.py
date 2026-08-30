"""Tests du module :mod:`Probas.DecisionTheory.voi` (issue #13569, tranche 3/3).

Pattern : bootstrap ``sys.path`` module-level, sans fixtures pytest,
tolerances commentees. Chaque test valide une propriete falsifiable du
contrat, de l'adaptateur PyMC et du comparateur cross-engine.
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(os.path.dirname(_HERE))
_DECISION = os.path.join(_ROOT, "Probas", "DecisionTheory")
for _p in (_DECISION,):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from Probas.DecisionTheory import voi  # noqa: E402
from Probas.DecisionTheory.voi import contract as contract_mod  # noqa: E402
from Probas.DecisionTheory.voi import compare as compare_mod  # noqa: E402


# --------------------------------------------------------------------------- #
#  Helpers                                                                   #
# --------------------------------------------------------------------------- #


def _parapluie() -> contract_mod.VoiContract:
    """Scenario parapluie (DecPyMC-5 section 2) : 2 etats, 2 actions."""
    return contract_mod.VoiContract(
        states=("pluie", "soleil"),
        prior=(0.3, 0.7),
        actions=("parapluie", "pas_parapluie"),
        utility=((0.0, -50.0), (-5.0, 0.0)),
        likelihood=((0.8, 0.2), (0.1, 0.9)),
        test_outcomes=("annonce_pluie", "annonce_soleil"),
        cost=1.0,
    )


def _forage() -> contract_mod.VoiContract:
    """Scenario forage petrolier (DecInfer-6 + DecPyMC-5 section 3)."""
    return contract_mod.VoiContract(
        states=("petrole", "pas_petrole"),
        prior=(0.3, 0.7),
        actions=("forer", "vendre"),
        utility=(
            (1_500_000.0, 200_000.0),
            (-500_000.0, 200_000.0),
        ),
        likelihood=((0.9, 0.1), (0.2, 0.8)),
        test_outcomes=("sismique_positif", "sismique_negatif"),
        cost=50_000.0,
    )


# --------------------------------------------------------------------------- #
#  Gate 1 : validations du contrat                                            #
# --------------------------------------------------------------------------- #


def test_contract_rejects_non_normalized_prior():
    """Le contrat refuse un prior qui ne somme pas a 1."""
    with pytest.raises(ValueError, match="sommer a 1"):
        contract_mod.VoiContract(
            states=("a", "b"),
            prior=(0.5, 0.4),
            actions=("x",),
            utility=((1.0,), (0.0,)),
            likelihood=((1.0,), (1.0,)),
            cost=0.0,
        )


def test_contract_rejects_row_sum_likelihood():
    """Le contrat refuse une vraisemblance dont les lignes ne somment pas a 1."""
    with pytest.raises(ValueError, match="ligne de likelihood"):
        contract_mod.VoiContract(
            states=("a", "b"),
            prior=(0.5, 0.5),
            actions=("x",),
            utility=((1.0,), (0.0,)),
            likelihood=((0.6, 0.6), (0.5, 0.5)),
            cost=0.0,
        )


def test_contract_rejects_negative_cost():
    """Le contrat refuse un cout strictement negatif."""
    with pytest.raises(ValueError, match="cost doit etre"):
        contract_mod.VoiContract(
            states=("a", "b"),
            prior=(0.5, 0.5),
            actions=("x",),
            utility=((1.0,), (0.0,)),
            likelihood=((1.0,), (1.0,)),
            cost=-1.0,
        )


def test_contract_roundtrip_json():
    """``to_dict`` / ``from_dict`` preserve les champs."""
    c = _parapluie()
    c2 = contract_mod.VoiContract.from_dict(c.to_dict())
    assert c == c2


# --------------------------------------------------------------------------- #
#  Gate 2 : reference analytique close-form                                  #
# --------------------------------------------------------------------------- #


def test_analytical_parapluie_evpi_matches_decpymc5_section2():
    """Calcul a la main : EVPI parapluie = 3.5 (cf DecPyMC-5 section 2)."""
    res = contract_mod.animat_decision_summary_contract(_parapluie())
    assert res.evpi == pytest.approx(3.5, abs=1e-9)
    assert res.best_no_info == "parapluie"


def test_analytical_forage_evpi_matches_decinfer6_section3():
    """Calcul a la main : EVPI forage = 90000 EUR (cf DecInfer-6 section 3).

    Avec P(petrole)=0.3, U(forer|petrole)=1.5M, U(forer|pas_petrole)=-0.5M,
    U(vendre)=0.2M partout : max EU par etat = 1.5M (forer) ou 0.2M (vendre).
    EU oracle = 0.3 * 1.5M + 0.7 * 0.2M = 450k + 140k = 590k.
    EU sans info constante optimale : max(0.3*1.5M+0.7*(-0.5M), 200k)
                                     = max(100k, 200k) = 200k.
    EVPI = 590k - 200k = 390k.
    """
    res = contract_mod.animat_decision_summary_contract(_forage())
    assert res.evpi == pytest.approx(390_000.0, abs=1e-6)
    assert res.best_no_info == "vendre"


def test_analytical_evsi_zero_for_perfect_observation_cost():
    """Controle negatif : cout >= EVPI => observe=False, EVSI nette <= 0."""
    # L'EVPI forage est 390k ; on met le cout exactement a 390k.
    c = contract_mod.VoiContract(
        states=("petrole", "pas_petrole"),
        prior=(0.3, 0.7),
        actions=("forer", "vendre"),
        utility=(
            (1_500_000.0, 200_000.0),
            (-500_000.0, 200_000.0),
        ),
        likelihood=((0.9, 0.1), (0.2, 0.8)),
        cost=390_000.0,
    )
    res = contract_mod.animat_decision_summary_contract(c)
    assert res.evsi_net == pytest.approx(res.evpi - 390_000.0, abs=1e-6)
    assert res.observe is False


# --------------------------------------------------------------------------- #
#  Gate 3 : comparateur cross-engine (PyMC + reference analytique)            #
# --------------------------------------------------------------------------- #


def test_compare_pymc_matches_analytical_parapluie_within_tolerance():
    """PyMC MCMC doit s'approcher de la reference analytique a 1e-1 pres.

    Tolerance elargie pour MCMC (2000 draws). Cf. docstring adapter_pymc.
    """
    report = compare_mod.compare(
        _parapluie(),
        include_pymc=True,
        include_infernet=False,
        tolerance=1e-1,
    )
    if report.pymc is None:
        pytest.skip("PyMC non disponible dans l'env (RECOVERABLE-LOCAL).")
    assert report.pymc.evpi == pytest.approx(report.analytical.evpi, abs=1e-1)
    assert report.pymc.evsi == pytest.approx(report.analytical.evsi, abs=1e-1)
    assert report.pymc.best_no_info == report.analytical.best_no_info


def test_compare_decision_agreement_parapluie():
    """PyMC + analytique doivent tomber d'accord sur observe=True/False."""
    report = compare_mod.compare(
        _parapluie(),
        include_pymc=True,
        include_infernet=False,
        tolerance=1e-1,
    )
    if report.pymc is None:
        pytest.skip("PyMC non disponible.")
    assert report.pymc.observe == report.analytical.observe


def test_compare_report_serializable_json():
    """Le rapport est serialisable en JSON (pour le runner multi-wakeup)."""
    report = compare_mod.compare(
        _parapluie(),
        include_pymc=False,
        include_infernet=False,
    )
    d = report.to_dict()
    import json as _json
    s = _json.dumps(d)
    _json.loads(s)
