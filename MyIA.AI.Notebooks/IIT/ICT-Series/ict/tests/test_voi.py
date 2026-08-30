"""Tests du module :mod:`ict.voi` (ICT-12e, Epic #4588, issue #13569).

Pattern herite de ``test_argumentation.py`` : bootstrap ``sys.path``
module-level, sans fixtures, tolerances commentees. Chaque test valide une
propriete falsifiable de l'interface EVPI/EVSI, numerote par *gate*.
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

from ict import voi as voi_mod  # noqa: E402


# --------------------------------------------------------------------------- #
#  Helpers                                                                   #
# --------------------------------------------------------------------------- #


def _parapluie() -> voi_mod.DecisionProblem:
    """Scenario parapluie (DecPyMC-5 section 2) : 2 etats, 2 actions.

    Pluie (P=0.3), Soleil (P=0.7). Utilites :

    - (parapluie, pluie) = 0
    - (parapluie, soleil) = -5
    - (pas_parapluie, pluie) = -50
    - (pas_parapluie, soleil) = 0

    Meilleure action sans info : parapluie (EU=-3.5 vs EU=-15 pour pas_parapluie).
    EVPI = 0 - (-3.5) = 3.5.
    """
    return voi_mod.DecisionProblem(
        states=("pluie", "soleil"),
        prior=(0.3, 0.7),
        actions=("parapluie", "pas_parapluie"),
        utility=[
            [0.0, -50.0],
            [-5.0, 0.0],
        ],
    )


def _forage() -> voi_mod.DecisionProblem:
    """Scenario forage petrolier (DecInfer-6 + DecPyMC-5 section 3).

    P(petrole) = 0.3, P(pas_petrole) = 0.7.

    Utilites :
    - (forer, petrole) = 1.5M (gain - cout forage)
    - (forer, pas_petrole) = -0.5M (-cout_forage)
    - (vendre, *) = 0.2M (prix_vente)
    """
    return voi_mod.DecisionProblem(
        states=("petrole", "pas_petrole"),
        prior=(0.3, 0.7),
        actions=("forer", "vendre"),
        utility=[
            [1_500_000.0, 200_000.0],
            [-500_000.0, 200_000.0],
        ],
    )


# --------------------------------------------------------------------------- #
#  Gate 1 : validation DecisionProblem (constructeur dataclass frozen)        #
# --------------------------------------------------------------------------- #


def test_decision_problem_validates_shape():
    """``DecisionProblem`` rejette un prior 2D ou une utility 1D."""
    with pytest.raises(ValueError, match="prior doit etre 1D"):
        voi_mod.DecisionProblem(
            states=("a", "b"),
            prior=[[0.5, 0.5]],
            actions=("x",),
            utility=[[1.0], [2.0]],
        )
    with pytest.raises(ValueError, match="utility doit etre 2D"):
        voi_mod.DecisionProblem(
            states=("a", "b"),
            prior=(0.5, 0.5),
            actions=("x",),
            utility=[1.0, 2.0],
        )


def test_decision_problem_rejects_non_normalised_prior():
    """Un prior qui ne somme pas a 1 est rejete (Bayes demande p sum = 1)."""
    with pytest.raises(ValueError, match="prior doit sommer a 1"):
        voi_mod.DecisionProblem(
            states=("a", "b"),
            prior=(0.5, 0.4),
            actions=("x",),
            utility=[[1.0], [2.0]],
        )


def test_decision_problem_rejects_negative_prior():
    """Probabilites negatives : rejete (sinon posteriors fantaisistes)."""
    with pytest.raises(ValueError, match="prior doit etre >= 0"):
        voi_mod.DecisionProblem(
            states=("a", "b"),
            prior=(-0.1, 1.1),
            actions=("x",),
            utility=[[1.0], [2.0]],
        )


# --------------------------------------------------------------------------- #
#  Gate 2 : EVPI analytique — scenario parapluie (clos-form canonique)         #
# --------------------------------------------------------------------------- #


def test_evpi_parapluie_canonical():
    """EVPI parapluie = 3.5 (cf DecPyMC-5 section 2 verbatim).

    Plafond theorique : si on observait parfaitement la meteo avant de
    decider, on gagnerait 3.5 utils en moyenne (la perte moyenne du
    choix constant parapluie).
    """
    pb = _parapluie()
    e = voi_mod.evpi(pb)
    assert np.isclose(e, 3.5, atol=1e-9), f"EVPI parapluie attendu 3.5, recu {e}"


def test_evpi_is_zero_when_const_policy_dominates():
    """Si la politique constante est optimale sur tous les etats, EVPI=0.

    Exemple : U[pluie, parapluie]=U[soleil, parapluie]=10, et l'autre
    action toujours inferieure. Aucune observation ne peut ameliorer.
    """
    pb = voi_mod.DecisionProblem(
        states=("a", "b"),
        prior=(0.5, 0.5),
        actions=("x", "y"),
        utility=[
            [10.0, 0.0],
            [10.0, 0.0],
        ],
    )
    assert voi_mod.evpi(pb) == 0.0


def test_optimal_action_parapluie():
    """Sans info, l'animat prend le parapluie (EU=-3.5 vs EU=-15).

    Verification verbatim DecPyMC-5 section 2.
    """
    pb = _parapluie()
    eu, action = voi_mod.optimal_action_without_info(pb)
    assert action == "parapluie"
    assert np.isclose(eu, -3.5, atol=1e-9)


# --------------------------------------------------------------------------- #
#  Gate 3 : EVSI — senseur informatif (vs EVPI, EVSI <= EVPI)                #
# --------------------------------------------------------------------------- #


def test_evsi_perfect_sensor_equals_evpi():
    """Un senseur parfait (likelihood = identite) donne EVSI = EVPI.

    Un oracle exact equivaut a l'info parfaite : EVSI = EVPI.
    """
    pb = _parapluie()
    L_perfect = np.eye(2)  # outcome j == etat j
    e_perfect = voi_mod.evsi(pb, L_perfect)
    e_evpi = voi_mod.evpi(pb)
    assert np.isclose(e_perfect, e_evpi, atol=1e-9), (
        f"EVSI senseur parfait doit valoir EVPI ({e_evpi}), recu {e_perfect}"
    )


def test_evsi_uninformative_sensor_is_zero():
    """Un senseur uniforme (likelihood = 1/n_outcomes) a une EVSI nulle.

    Le test n'apprend rien sur l'etat : posteriors = prior, donc la
    politique optimale conditionnelle = politique constante.
    """
    pb = _parapluie()
    L_uniform = np.ones((2, 2)) * 0.5
    e = voi_mod.evsi(pb, L_uniform)
    assert np.isclose(e, 0.0, atol=1e-12), (
        f"EVSI senseur uniforme doit etre 0, recu {e}"
    )


def test_evsi_le_evpi_inequality():
    """EVSI <= EVPI toujours (l'imparfait ne peut pas exceder le parfait).

    Senseur sismique : sensibilite 0.90, specificite 0.80, scenario forage.
    """
    pb = _forage()
    L_seismic = np.array([
        [0.90, 0.10],  # petrole -> [test+, test-]
        [0.20, 0.80],  # pas_petrole -> [test+, test-]
    ])
    e = voi_mod.evpi(pb)
    s = voi_mod.evsi(pb, L_seismic)
    assert s <= e + 1e-9, f"EVSI ({s}) doit etre <= EVPI ({e})"
    assert s >= 0.0, f"EVSI doit etre >= 0, recu {s}"


def test_evsi_observation_decision_forage():
    """EVSI sismique > cout d'observation de 50k : l'animat fore apres test.

    Scenario forage DecInfer-6 : EVSI = environ 250k (test informatif), cout
    50k : rentable. Verification semantique du verdict observation_is_worthwhile.
    """
    pb = _forage()
    L_seismic = np.array([
        [0.90, 0.10],
        [0.20, 0.80],
    ])
    summary = voi_mod.animat_decision_summary(pb, L_seismic, cost=50_000.0)
    assert summary["evsi_net"] > 0, (
        f"EVSI net doit etre > 0 (rentable), recu {summary['evsi_net']:.0f}"
    )
    assert summary["observe"] is True


def test_evsi_net_observation_decision_expensive_test():
    """Test trop cher : EVSI < cout, l'animat n'observe pas.

    Senseur parfait mais cout 100M : aucune observation ne vaut ce prix.
    L'animat decide sans observer.
    """
    pb = _forage()
    L_perfect = np.eye(2)
    summary = voi_mod.animat_decision_summary(pb, L_perfect, cost=100_000_000.0)
    assert summary["evsi_net"] < 0, (
        f"EVSI net doit etre < 0 (test trop cher), recu {summary['evsi_net']:.0f}"
    )
    assert summary["observe"] is False


# --------------------------------------------------------------------------- #
#  Gate 4 : cas limite — senseur = bruit pur, EVSI = 0                       #
# --------------------------------------------------------------------------- #


def test_evsi_zero_likelihood_column_ignored():
    """Une colonne de likelihood marginale < 1e-12 est ignoree (no division by 0).

    Si la colonne ne contribue pas numeriquement, on ne divise pas par
    ``P(outcome) ≈ 0`` dans le posterior de Bayes. Ici, l'outcome 1 est
    le seul informatif (senseur quasi-parfait) : EVSI ≈ EVPI.
    L'outcome 2 est negligeable : il est ignore, pas de NaN.
    """
    pb = _parapluie()
    L = np.array([
        [0.99, 1e-15],  # pluie -> [out1 informatif, out2 negligeable]
        [0.01, 1e-15],  # soleil -> [out1 informatif, out2 negligeable]
    ])
    e = voi_mod.evsi(pb, L)
    # Pas de NaN (outcome negligeable ignore correctement)
    assert np.isfinite(e), f"EVSI doit etre fini, recu {e}"
    # Outcome 1 = senseur quasi-parfait → EVSI ≈ EVPI (perte ~1%)
    e_evpi = voi_mod.evpi(pb)
    assert e <= e_evpi + 1e-9, f"EVSI ({e}) doit etre <= EVPI ({e_evpi})"
    assert e >= e_evpi * 0.95, (
        f"EVSI senseur 99% doit etre >= 95% EVPI, recu {e:.4f} vs EVPI={e_evpi:.4f}"
    )


def test_evsi_likelihood_validation():
    """Likelihood avec valeurs negatives : rejete."""
    pb = _parapluie()
    L_bad = np.array([[0.5, 0.5], [-0.1, 1.1]])  # negatives
    with pytest.raises(ValueError, match="likelihood doit etre >= 0"):
        voi_mod.evsi(pb, L_bad)


# --------------------------------------------------------------------------- #
#  Gate 5 : interface canonique animat_decision_summary                        #
# --------------------------------------------------------------------------- #


def test_animat_decision_summary_keys():
    """Le résumé expose les 6 clés attendues par le notebook ICT-12e."""
    pb = _forage()
    L = np.eye(2)
    summary = voi_mod.animat_decision_summary(pb, L, cost=50_000.0)
    expected_keys = {"eu_no_info", "best_no_info", "evpi", "evsi", "evsi_net", "observe"}
    assert set(summary.keys()) == expected_keys, (
        f"Clés attendues {expected_keys}, recues {set(summary.keys())}"
    )


def test_evsi_net_rejects_negative_cost():
    """Un cout d'observation negatif n'a pas de sens : on le rejette."""
    pb = _parapluie()
    L = np.eye(2)
    with pytest.raises(ValueError, match="cout doit etre >= 0"):
        voi_mod.evsi_net(pb, L, cost=-1.0)
