"""Tests unitaires pour ``ict.phat_self_reference`` (Case 2, Epic #9533).

La boucle auto-referentielle ``p_hat -> action -> p_hat`` (ICT-2, case 2 du
canevas pre-enregistre ``docs/ict/dissociations-matrix.md``) est testee ici
selon 13 gates falsifiables, chacun attestant un contrat precis du module :

    1.  (dataclass) ``EnvironmentParams`` est frozen et porte les valeurs
        par defaut attendues.
    2.  (f_obs)      la prediction observationnelle ``f_obs`` est exactement
        ``a_hat * x + b_hat`` (scalaire et vecteur).
    3.  (simulation) ``simulate_self_reference_loop`` renvoie un dict avec
        les cles/shapes documentees (``R_0``, ``R_T``, ``ratio``,
        ``trajectories_x``, ``trajectories_phat``).
    4.  (delieur)    pour ``kappa = 0`` (delieur causal), le ratio
        ``R_T / R_0`` reste borne (< 2) -- la prediction n'influence pas
        l'environnement.
    5.  (divergence) pour ``kappa = 1.0`` (couplage fort), le ratio
        ``R_T / R_0`` franchit ``RATIO_DIVERGENT = 5`` -- la boucle
        auto-referentielle suremodifie le regime.
    6.  (constante)  ``KAPPA_C_PREDICTED`` est exactement ``(1 - a) / a_hat``
        avec ``a = a_hat = 0.95`` (-> environ 0.0526).
    7.  (scan shapes) ``stability_scan`` produit les bonnes formes
        ``(n_seeds, len(kappa_grid))`` et la frontiere est reproductible :
        memes seeds -> memes ratios bit-a-bit.
    8.  (scan coherence) dans le scan, ``divergent_mask`` est True pour
        les grands kappa et False pour ``kappa = 0`` (coherence semantique
        de la grille).
    9.  (estimate)   ``estimate_stability_boundary`` retourne ``n_seeds``
        valeurs ``kappa_critical_per_seed``, toutes positives.
    10. (delieur)    ``delieur_verdict`` declare ``delieur_stable = True``
        sur la configuration par defaut : la dissociation bouclee/delieur
        tient structurellement.
    11. (verdict)    ``predict_and_dissociate`` retourne un verdict parmi
        ``{"CONFIRMED", "PARTIAL", "FALSIFIED"}`` avec toutes les
        sous-cles attendues.
    12. (protocol)   ``run_full_protocol`` compose ``stability_scan`` +
        ``predict_and_dissociate`` de maniere coherente.
    13. (determinism) ``run_full_protocol`` est deterministe : deux appels
        successifs avec memes seeds produisent le meme verdict_detail
        byte-a-byte.

Implementation : aucune dependance externe ; un seul import numpy + import
du package ``ict``. Les seuils (KAPPA_C_PREDICTED, RATIO_DIVERGENT,
RATIO_BORNE_HIGH) sont pre-enregistres (cf PR #9546 SHA 3f6590fa4) et
verrouilles avant le test : les tests ne FORCENT aucun verdict, ils
verifient la COHERENCE des invariants.
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
import pytest

from ict import phat_self_reference as psr


def _rng_for(seed: int) -> np.random.Generator:
    return np.random.default_rng(seed)


# --------------------------------------------------------------------------- #
#  Gate 1 : EnvironmentParams : dataclass frozen + valeurs par defaut         #
# --------------------------------------------------------------------------- #


def test_environment_params_frozen_default_values():
    """``EnvironmentParams`` est frozen et porte les valeurs par defaut
    documentees (``a = a_hat = 0.95``, ``b = b_hat = 0.0``, ``sigma = 0.05``).
    """
    params = psr.EnvironmentParams()
    assert params.a == 0.95, f"a attendu = 0.95, recu {params.a}"
    assert params.a_hat == 0.95, f"a_hat attendu = 0.95, recu {params.a_hat}"
    assert params.b == 0.0, f"b attendu = 0.0, recu {params.b}"
    assert params.b_hat == 0.0, f"b_hat attendu = 0.0, recu {params.b_hat}"
    assert params.sigma == 0.05, f"sigma attendu = 0.05, recu {params.sigma}"

    # frozen -> mutation leve FrozenInstanceError (dataclass).
    with pytest.raises(Exception):
        params.a = 1.0  # type: ignore[misc]


# --------------------------------------------------------------------------- #
#  Gate 2 : f_obs : prediction observationnelle = a_hat * x + b_hat            #
# --------------------------------------------------------------------------- #


def test_f_obs_scalar_and_vector():
    """``f_obs(x, params) = a_hat * x + b_hat`` (scalaire et vecteur).

    On verifie la formule sur un scalaire et sur un vecteur numpy, avec
    des params non triviaux pour exclure tout court-circuit.
    """
    params = psr.EnvironmentParams(a=0.7, b=0.1, a_hat=0.8, b_hat=-0.2)
    x_scalar = np.array(0.5)
    out_scalar = psr.f_obs(x_scalar, params)
    assert np.allclose(out_scalar, 0.8 * 0.5 + (-0.2)), (
        f"f_obs scalaire : attendu {0.8 * 0.5 - 0.2}, recu {out_scalar}"
    )

    x_vec = np.array([-1.0, 0.0, 0.5, 1.0])
    out_vec = psr.f_obs(x_vec, params)
    expected = 0.8 * x_vec + (-0.2)
    assert np.allclose(out_vec, expected), (
        f"f_obs vecteur : attendu {expected}, recu {out_vec}"
    )


# --------------------------------------------------------------------------- #
#  Gate 3 : simulate_self_reference_loop : dict structure + shapes             #
# --------------------------------------------------------------------------- #


def test_simulate_loop_returns_documented_keys_and_shapes():
    """Le dict de retour contient exactement les 5 cles documentees
    avec les shapes ``(n_init,)`` et ``(n_init, horizon + 1)``.
    """
    n_init = 25
    horizon = 50
    rng = _rng_for(0)
    result = psr.simulate_self_reference_loop(
        kappa=0.05, n_init=n_init, horizon=horizon, rng=rng
    )

    expected_keys = {"R_0", "R_T", "ratio", "trajectories_x", "trajectories_phat"}
    assert set(result.keys()) == expected_keys, (
        f"cles attendues {expected_keys}, recues {set(result.keys())}"
    )

    assert result["R_0"].shape == (n_init,)
    assert result["R_T"].shape == (n_init,)
    assert result["ratio"].shape == (n_init,)
    assert result["trajectories_x"].shape == (n_init, horizon + 1)
    assert result["trajectories_phat"].shape == (n_init, horizon + 1)

    # Toutes les conditions initiales partagent le meme R_0 et R_T (def.
    # de la doc : rms agrege sur l'ensemble des conditions initiales).
    assert np.all(result["R_0"] == result["R_0"][0])
    assert np.all(result["R_T"] == result["R_T"][0])

    # Et ratio = R_T / R_0 (pour R_0 > 0).
    expected_ratio = result["R_T"] / np.maximum(result["R_0"], 1e-12)
    assert np.allclose(result["ratio"], expected_ratio), (
        f"ratio incoherent : ratio={result['ratio']}, expected={expected_ratio}"
    )


# --------------------------------------------------------------------------- #
#  Gate 4 : delieur causal (kappa = 0) -> ratio borne (< 2)                   #
# --------------------------------------------------------------------------- #


def test_simulate_kappa_zero_is_bounded():
    """Pour ``kappa = 0`` (delieur causal), la prediction n'influence pas
    l'environnement : ``R_T / R_0`` reste sous ``RATIO_BORNE_HIGH = 2.0``.

    Note : sans couplage, la dynamique reduit a ``x_{t+1} = a x_t + b +
    epsilon_t`` avec ``|a| = 0.95 < 1`` -> regime lineaire stable, |<R_T>|
    ~ |<R_0>| * 0.95^T + bruit cumule borne. Avec T = 200, l'amplification
    par bruit cumule reste faible face au facteur d'attenuation ``0.95^200``.
    """
    rng = _rng_for(42)
    result = psr.simulate_self_reference_loop(
        kappa=0.0, n_init=psr.N_INIT, horizon=psr.HORIZON_T, rng=rng
    )
    median_ratio = float(np.median(result["ratio"]))
    assert median_ratio < psr.RATIO_BORNE_HIGH, (
        f"delieur (kappa=0) devrait rester borne, "
        f"median ratio = {median_ratio:.3f} >= {psr.RATIO_BORNE_HIGH}"
    )


# --------------------------------------------------------------------------- #
#  Gate 5 : kappa grand -> divergence (> RATIO_DIVERGENT = 5)                 #
# --------------------------------------------------------------------------- #


def test_simulate_kappa_large_diverges():
    """Pour ``kappa = 1.0`` (couplage fort), la prediction est injectee
    en pleine puissance dans la dynamique : ``R_T / R_0`` franchit
    ``RATIO_DIVERGENT = 5``.

    Theorie lineaire : ``a_eff = a + kappa * a_hat = 0.95 + 1.0 * 0.95
    = 1.90``, ``|a_eff| >> 1`` -> la trajectoire explose.
    """
    rng = _rng_for(7)
    result = psr.simulate_self_reference_loop(
        kappa=1.0, n_init=psr.N_INIT, horizon=psr.HORIZON_T, rng=rng
    )
    median_ratio = float(np.median(result["ratio"]))
    assert median_ratio > psr.RATIO_DIVERGENT, (
        f"kappa=1.0 devrait diverger, "
        f"median ratio = {median_ratio:.3f} <= {psr.RATIO_DIVERGENT}"
    )


# --------------------------------------------------------------------------- #
#  Gate 6 : KAPPA_C_PREDICTED = (1 - a) / a_hat ~= 0.0526                       #
# --------------------------------------------------------------------------- #


def test_kappa_c_predicted_constant_value():
    """``KAPPA_C_PREDICTED`` est exactement ``(1 - a) / a_hat`` avec
    ``a = a_hat = 0.95`` -> environ 0.0526.
    """
    expected = (1.0 - 0.95) / 0.95
    assert np.isclose(psr.KAPPA_C_PREDICTED, expected), (
        f"KAPPA_C_PREDICTED = {psr.KAPPA_C_PREDICTED}, "
        f"attendu = {expected}"
    )
    # Verification absolue : >= 0.05 (la doc annonce "arrondi a la resolution
    # de la grille 0.1", demi-maille 0.05).
    assert 0.05 <= psr.KAPPA_C_PREDICTED < 0.06, (
        f"KAPPA_C_PREDICTED = {psr.KAPPA_C_PREDICTED} hors tolérance [0.05, 0.06)"
    )


# --------------------------------------------------------------------------- #
#  Gate 7 : stability_scan : shapes + reproductibilite seed                    #
# --------------------------------------------------------------------------- #


def test_stability_scan_shapes_and_reproducibility():
    """``stability_scan`` produit les 5 sorties documentees et est
    deterministe : memes seeds -> memes ratios bit-a-bit.
    """
    seeds = (0, 1, 7, 42, 99)
    scan1 = psr.stability_scan(seeds=seeds)
    scan2 = psr.stability_scan(seeds=seeds)

    expected_keys = {
        "kappa_grid", "ratio_mean", "ratio_median",
        "stable_mask", "divergent_mask", "seeds",
    }
    assert set(scan1.keys()) == expected_keys, (
        f"cles scan attendues {expected_keys}, recues {set(scan1.keys())}"
    )

    n_seeds = len(seeds)
    n_kappa = len(psr.KAPPA_GRID)
    assert scan1["ratio_mean"].shape == (n_seeds, n_kappa)
    assert scan1["ratio_median"].shape == (n_seeds, n_kappa)
    assert scan1["stable_mask"].shape == (n_seeds, n_kappa)
    assert scan1["divergent_mask"].shape == (n_seeds, n_kappa)
    assert np.array_equal(scan1["seeds"], np.asarray(seeds))

    # Determinism bit-a-bit : memes seeds -> memes arrays.
    assert np.array_equal(scan1["ratio_mean"], scan2["ratio_mean"])
    assert np.array_equal(scan1["ratio_median"], scan2["ratio_median"])
    assert np.array_equal(scan1["stable_mask"], scan2["stable_mask"])
    assert np.array_equal(scan1["divergent_mask"], scan2["divergent_mask"])


# --------------------------------------------------------------------------- #
#  Gate 8 : stability_scan : divergent_mask coherent (petit vs grand kappa)   #
# --------------------------------------------------------------------------- #


def test_stability_scan_divergent_mask_is_coherent():
    """Dans le scan, ``divergent_mask`` est False pour les petits kappa
    (dont kappa = 0, delieur) et True pour les grands kappa (couplage
    fort). Le seuil de bascule se situe en un kappa >= KAPPA_C_PREDICTED.
    """
    scan = psr.stability_scan(seeds=(0, 1, 7, 42, 99))
    kappa_grid = scan["kappa_grid"]
    divergent_mask = scan["divergent_mask"]

    # kappa = 0 : jamais divergent (delieur causal).
    idx_zero = int(np.where(np.isclose(kappa_grid, 0.0))[0][0])
    assert not divergent_mask[:, idx_zero].any(), (
        f"divergent_mask a kappa=0 devrait etre False partout, "
        f"recue {divergent_mask[:, idx_zero]}"
    )

    # kappa = 1.0 : toujours divergent (couplage fort, a_eff >> 1).
    idx_one = int(np.where(np.isclose(kappa_grid, 1.0))[0][0])
    assert divergent_mask[:, idx_one].all(), (
        f"divergent_mask a kappa=1.0 devrait etre True partout, "
        f"recue {divergent_mask[:, idx_one]}"
    )


# --------------------------------------------------------------------------- #
#  Gate 9 : estimate_stability_boundary : n_seeds valeurs, toutes > 0         #
# --------------------------------------------------------------------------- #


def test_estimate_stability_boundary_returns_per_seed_values():
    """``estimate_stability_boundary`` retourne ``n_seeds`` valeurs
    ``kappa_critical_per_seed``, toutes strictement positives
    (frontiere dans la grille ou au-dela : kappa_grid[-1] + 0.1 = 1.1).
    """
    scan = psr.stability_scan(seeds=(0, 1, 7, 42, 99))
    boundary = psr.estimate_stability_boundary(scan)

    expected_keys = {
        "kappa_critical_per_seed",
        "kappa_critical_median",
        "kappa_critical_std",
        "bias_vs_predicted",
    }
    assert set(boundary.keys()) == expected_keys, (
        f"cles boundary attendues {expected_keys}, "
        f"recues {set(boundary.keys())}"
    )

    kcps = boundary["kappa_critical_per_seed"]
    assert kcps.shape == (5,)
    assert (kcps > 0).all(), (
        f"kappa_critical_per_seed doit etre > 0, recu {kcps}"
    )

    # La mediane est dans la plage [0, kappa_grid[-1] + 0.1].
    kcm = boundary["kappa_critical_median"]
    assert 0.0 <= kcm <= psr.KAPPA_GRID[-1] + 0.1, (
        f"kappa_critical_median = {kcm} hors de [0, {psr.KAPPA_GRID[-1] + 0.1}]"
    )


# --------------------------------------------------------------------------- #
#  Gate 10 : delieur_verdict : delieur_stable = True sur la config par defaut #
# --------------------------------------------------------------------------- #


def test_delieur_verdict_is_stable():
    """Sur la configuration par defaut, ``delieur_verdict`` declare
    ``delieur_stable = True`` (le delieur causal reste dans le regime
    borne) -- la dissociation bouclee/delieur tient structurellement.
    """
    scan = psr.stability_scan(seeds=(0, 1, 7, 42, 99))
    delieur = psr.delieur_verdict(scan)

    expected_keys = {
        "delieur_ratio_per_seed",
        "delieur_ratio_max",
        "delieur_ratio_mean",
        "delieur_stable",
    }
    assert set(delieur.keys()) == expected_keys, (
        f"cles delieur attendues {expected_keys}, "
        f"recues {set(delieur.keys())}"
    )

    assert delieur["delieur_stable"] is True, (
        f"delieur devrait etre stable sur la config par defaut, "
        f"delieur_ratio_max = {delieur['delieur_ratio_max']}"
    )
    assert delieur["delieur_ratio_max"] < psr.RATIO_DIVERGENT, (
        f"delieur_ratio_max = {delieur['delieur_ratio_max']} "
        f">= {psr.RATIO_DIVERGENT}"
    )


# --------------------------------------------------------------------------- #
#  Gate 11 : predict_and_dissociate : verdict dans l'ensemble {CONFIRMED,     #
#         PARTIAL, FALSIFIED} avec toutes les sous-cles                        #
# --------------------------------------------------------------------------- #


def test_predict_and_dissociate_returns_valid_verdict():
    """``predict_and_dissociate`` retourne un verdict parmi
    ``{"CONFIRMED", "PARTIAL", "FALSIFIED"}`` avec toutes les sous-cles
    documentees (boundary, delieur, prediction_confirmed, etc.).
    """
    scan = psr.stability_scan(seeds=(0, 1, 7, 42, 99))
    result = psr.predict_and_dissociate(scan)

    expected_keys = {
        "verdict", "verdict_detail", "boundary", "delieur",
        "prediction_confirmed", "dissociation_confirmed",
        "n_seeds", "n_within_tolerance",
    }
    assert set(result.keys()) == expected_keys, (
        f"cles verdict attendues {expected_keys}, "
        f"recues {set(result.keys())}"
    )

    assert result["verdict"] in {"CONFIRMED", "PARTIAL", "FALSIFIED"}, (
        f"verdict = {result['verdict']!r} hors ensemble attendu"
    )
    assert isinstance(result["verdict_detail"], str)
    assert len(result["verdict_detail"]) > 0
    assert result["n_seeds"] == 5
    assert isinstance(result["n_within_tolerance"], int)
    assert 0 <= result["n_within_tolerance"] <= result["n_seeds"]


# --------------------------------------------------------------------------- #
#  Gate 12 : run_full_protocol : composition coherente scan + verdict         #
# --------------------------------------------------------------------------- #


def test_run_full_protocol_composes_scan_and_verdict():
    """``run_full_protocol`` produit ``scan`` (= sortie de
    ``stability_scan``) et ``verdict`` (= sortie de
    ``predict_and_dissociate``) coherents entre eux.
    """
    result = psr.run_full_protocol(seeds=(0, 1, 7, 42, 99))

    assert "scan" in result
    assert "verdict" in result

    # Le verdict reference bien le scan (memes n_seeds, n_kappa).
    assert result["verdict"]["n_seeds"] == 5
    assert result["scan"]["ratio_mean"].shape == (5, len(psr.KAPPA_GRID))

    # Les frontieres de stabilite sont coherentes entre les deux.
    v = result["verdict"]
    s = result["scan"]
    assert v["boundary"]["kappa_critical_median"] == psr.estimate_stability_boundary(s)[
        "kappa_critical_median"
    ]
    assert v["delieur"]["delieur_stable"] == psr.delieur_verdict(s)["delieur_stable"]


# --------------------------------------------------------------------------- #
#  Gate 13 : run_full_protocol : determinisme (memes seeds -> meme verdict)   #
# --------------------------------------------------------------------------- #


def test_run_full_protocol_is_deterministic():
    """``run_full_protocol`` est deterministe : deux appels successifs
    avec les memes seeds produisent le meme ``verdict`` et le meme
    ``verdict_detail`` byte-a-byte.
    """
    seeds = (0, 1, 7, 42, 99)
    r1 = psr.run_full_protocol(seeds=seeds)
    r2 = psr.run_full_protocol(seeds=seeds)

    assert r1["verdict"]["verdict"] == r2["verdict"]["verdict"]
    assert r1["verdict"]["verdict_detail"] == r2["verdict"]["verdict_detail"]
    # Et les arrays scan sont bit-a-bit egaux.
    assert np.array_equal(r1["scan"]["ratio_mean"], r2["scan"]["ratio_mean"])
    assert np.array_equal(r1["scan"]["ratio_median"], r2["scan"]["ratio_median"])
    assert np.array_equal(
        r1["scan"]["divergent_mask"], r2["scan"]["divergent_mask"]
    )
