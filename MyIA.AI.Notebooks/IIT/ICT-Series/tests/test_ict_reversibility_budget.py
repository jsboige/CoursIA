"""Tests unitaires du budget de reversibilite (ICT-18b, strate 5 Epic #4588).

Couvre ``ict.reversibility_budget`` :

* :func:`sample_ball` -- echantillonnage **uniforme en volume** dans une boule.
* :func:`state_space_budget` -- Monte-Carlo sur la dynamique.
* :func:`budget_curve` -- courbe de degradation sur grille de rayons.
* :func:`work_budget` -- distance L1/2 a la projection reversible ``P_rev``.
* :func:`work_budget_normalized` -- variante normalisee par la taille du vocabulaire.
* :func:`covariation_with_ews` -- contrat lecture-ressource (Kendall).

Methodologie
------------
Le scope est volontairement limite : on verifie la **forme** de la primitive
(dimensions, types, invariants), son **comportement statistique attendu** sur
des dynamiques **synthetiques** dont la veritie terrain est connue, et la
**coherence avec les primitives en amont** (``time_arrow.reversibilize``,
``early_warning.kendall_tau``). On n'invoque PAS les fixtures GPU-extractees
(SAE/J-Lens) -- ces fixtures relevent des notebooks ICT-Series.

Convention C.1 notebooks respectee (pas de ``raise NotImplementedError``).
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import reversibility_budget as RB  # noqa: E402


# --------------------------------------------------------------------------- #
#  Helpers de dynamiques synthetiques (verite terrain)                         #
# --------------------------------------------------------------------------- #
def _identity_step(x):
    """Dynamique triviale : point fixe partout."""
    return np.asarray(x, dtype=float)


def _fixed_point_step(x):
    """Dynamique contractive : tout revient vers 0 (budget ~1.0 a petite ray)."""
    return 0.5 * np.asarray(x, dtype=float)


def _repulsive_step(x):
    """Dynamique repulsive en 1-D : x_{t+1} = x_t * 2. Sortie rapide du voisinage."""
    return 2.0 * np.asarray(x, dtype=float)


def _uniform_random_step_factory(seed: int = 0):
    """Pas aleatoire uniforme (le budget tend vers 0 par perte de corelation)."""
    rng = np.random.default_rng(seed)
    state = {"x": np.array([0.0])}

    def step(x):
        x = np.asarray(x, dtype=float)
        out = rng.uniform(-1.0, 1.0, size=x.shape)
        state["x"] = out
        return out

    return step


def _two_state_chain():
    """Chaine a 2 etats reversible (P symetrique, pi uniforme) : B_work = 0 attendu."""
    P = np.array([[0.5, 0.5], [0.5, 0.5]])
    pi = np.array([0.5, 0.5])
    return P, pi


def _three_state_irreversible_cycle():
    """Chaine a 3 etats **irreversible** (cycle 1->2->3->1) : B_work > 0
    La reversibilisation redistribue les transitions pour satisfaire le
    detaille balance, d'ou une distance > 0 a la matrice d'origine."""
    P = np.array([
        [0.0, 0.5, 0.5],
        [0.0, 0.0, 1.0],
        [1.0, 0.0, 0.0],
    ], dtype=float)
    # Stationnaire : solve pi*P = pi.
    eigvals, eigvecs = np.linalg.eig(P.T)
    i = np.argmin(np.abs(eigvals - 1.0))
    pi = np.real(eigvecs[:, i])
    pi = pi / pi.sum()
    return P, pi


# --------------------------------------------------------------------------- #
#  sample_ball
# --------------------------------------------------------------------------- #
class TestSampleBall:
    """Echantillonnage uniforme **en volume** dans une boule n-dim."""

    def test_shape_is_n_samples_by_n_dims(self):
        rng = np.random.default_rng(0)
        x = RB.sample_ball(1.0, n_dims=3, n_samples=50, rng=rng)
        assert x.shape == (50, 3)

    def test_all_points_inside_ball(self):
        rng = np.random.default_rng(1)
        x = RB.sample_ball(2.0, n_dims=4, n_samples=200, rng=rng)
        norms = np.linalg.norm(x, axis=1)
        # Tous les points dans la boule fermee (tolere erreur fp pres de la surface).
        assert np.all(norms <= 2.0 + 1e-9)

    def test_rejects_nonpositive_radius(self):
        rng = np.random.default_rng(2)
        with pytest.raises(ValueError):
            RB.sample_ball(0.0, n_dims=2, n_samples=10, rng=rng)
        with pytest.raises(ValueError):
            RB.sample_ball(-1.0, n_dims=2, n_samples=10, rng=rng)

    def test_rejects_nonpositive_n_dims(self):
        rng = np.random.default_rng(3)
        with pytest.raises(ValueError):
            RB.sample_ball(1.0, n_dims=0, n_samples=10, rng=rng)
        with pytest.raises(ValueError):
            RB.sample_ball(1.0, n_dims=-3, n_samples=10, rng=rng)

    def test_radius_scales_norm(self):
        """Doubler radius double la borne sup des normes."""
        rng = np.random.default_rng(4)
        x = RB.sample_ball(1.0, n_dims=2, n_samples=500, rng=rng)
        norms_lo = np.linalg.norm(x, axis=1)
        x_hi = RB.sample_ball(2.0, n_dims=2, n_samples=500, rng=rng)
        norms_hi = np.linalg.norm(x_hi, axis=1)
        assert max(norms_lo) <= 1.0 + 1e-9
        # max > 1 (sinon on aurait rate le tirage de la coquille exterieure).
        assert max(norms_hi) > 1.5

    def test_1d_diameter(self):
        """n_dims=1 : les points sont sur un segment [-radius, +radius]."""
        rng = np.random.default_rng(5)
        x = RB.sample_ball(1.0, n_dims=1, n_samples=100, rng=rng)
        assert x.shape == (100, 1)
        assert np.all(np.abs(x[:, 0]) <= 1.0 + 1e-9)

    def test_deterministic_with_seed(self):
        rng1 = np.random.default_rng(42)
        rng2 = np.random.default_rng(42)
        x1 = RB.sample_ball(1.0, n_dims=3, n_samples=10, rng=rng1)
        x2 = RB.sample_ball(1.0, n_dims=3, n_samples=10, rng=rng2)
        np.testing.assert_array_equal(x1, x2)

    def test_volume_distribution_is_not_concentrated_on_shell(self):
        """Loi du rayon = radius * u**(1/n) distribue **uniformement en volume** ;
        la moitieite des points sont dans la moitiei interieure (de la boule)."""
        rng = np.random.default_rng(6)
        x = RB.sample_ball(1.0, n_dims=3, n_samples=2000, rng=rng)
        norms = np.linalg.norm(x, axis=1)
        # Volume integre jusqu'a r/R = (r/R)^n, donc P(N<=0.5) = 0.5^n = 0.125.
        frac_inner = np.mean(norms <= 0.5)
        assert 0.07 <= frac_inner <= 0.20  # tolerance large pour n=3


# --------------------------------------------------------------------------- #
#  state_space_budget
# --------------------------------------------------------------------------- #
class TestStateSpaceBudget:
    """Budget Monte-Carlo : fraction des perturbations depuis lesquelles
    le systeme revient dans la region de consigne en tau pas."""

    def test_returns_scalar_in_unit_interval(self):
        rng = np.random.default_rng(10)
        anchor = np.array([0.0, 0.0])
        b = RB.state_space_budget(
            _fixed_point_step,
            anchor,
            radius=0.1,
            tau=5,
            n_samples=20,
            rng=rng,
        )
        assert isinstance(b, float)
        assert 0.0 <= b <= 1.0

    def test_identity_step_conserves_consigne_fraction(self):
        """step_fn = identite : x_init = anchor + delta reste `a x_init.
        Succes si ``||delta|| <= consigne_radius`` ; attendu ~ (c/r)^n_dims
        (volume integre jusqu'a r)."""
        rng = np.random.default_rng(11)
        anchor = np.array([0.5])
        b = RB.state_space_budget(
            _identity_step,
            anchor,
            radius=0.1,
            tau=10,
            n_samples=2000,
            rng=rng,
            bounds=(-10, 10),
        )
        # Avec n_dims=1, fraction theorique = consigne_radius / radius = 0.5/0.1
        # = 0.5 (bornee par les arrondis fp). Tolerance large.
        assert 0.40 <= b <= 0.60, f"attendu ~0.5 (uniforme), obtenu {b}"

    def test_contractive_step_high_budget(self):
        """Pas contractif : depuis une petite perturbation, retour quasi garanti."""
        rng = np.random.default_rng(12)
        anchor = np.array([0.0, 0.0])
        b = RB.state_space_budget(
            _fixed_point_step,
            anchor,
            radius=0.1,
            tau=10,
            n_samples=30,
            rng=rng,
        )
        assert b == 1.0  # contraction vers 0 = sous la consigne apres 1 pas.

    def test_repulsive_step_low_budget(self):
        """Pas repulsif en 1-D : aucune chance de revenir dans la consigne."""
        rng = np.random.default_rng(13)
        anchor = np.array([0.0])
        b = RB.state_space_budget(
            _repulsive_step,
            anchor,
            radius=0.1,
            tau=5,
            n_samples=20,
            rng=rng,
            bounds=(-1e6, 1e6),
        )
        # Apres 1 pas x *= 2, donc 2x par rapport a 0.1 = 0.2 > consigne_radius=0.05.
        assert b == 0.0

    def test_consigne_radius_validated(self):
        """consigne_radius doit etre > 0 si explicite."""
        rng = np.random.default_rng(14)
        anchor = np.array([0.0])
        with pytest.raises(ValueError):
            RB.state_space_budget(
                _identity_step,
                anchor,
                radius=0.1,
                tau=1,
                n_samples=2,
                rng=rng,
                consigne_radius=0.0,
            )
        with pytest.raises(ValueError):
            RB.state_space_budget(
                _identity_step,
                anchor,
                radius=0.1,
                tau=1,
                n_samples=2,
                rng=rng,
                consigne_radius=-0.5,
            )

    def test_bounds_clip_initial_state(self):
        """bounds clip l'etat initial apres perturbation, evapore la fraction
        reellement exposee au step. Ici on contraint tout dans [0, 1], le
        point fixe est en 0.5 -> budget eleve."""
        rng = np.random.default_rng(15)

        def clamped_step(x):
            x = np.asarray(x, dtype=float)
            return np.clip(0.5 + 0.5 * (x - 0.5), 0.0, 1.0)

        anchor = np.array([0.5])
        b = RB.state_space_budget(
            clamped_step,
            anchor,
            radius=0.2,
            tau=5,
            n_samples=30,
            rng=rng,
            bounds=(0.0, 1.0),
        )
        assert b == 1.0

    def test_default_rng_consistent(self):
        """Sans rng, le resultat est deterministe (reproductibilite)."""
        anchor = np.array([0.0, 0.0])
        b1 = RB.state_space_budget(
            _fixed_point_step,
            anchor,
            radius=0.1,
            tau=3,
            n_samples=20,
        )
        b2 = RB.state_space_budget(
            _fixed_point_step,
            anchor,
            radius=0.1,
            tau=3,
            n_samples=20,
        )
        # _fixed_point_step donne systematiquement 1.0 (contraction immediate),
        # donc les deux valeurs sont identiques.
        assert b1 == b2 == 1.0

    def test_keys_and_types(self):
        """Invariants de forme : float, dans [0, 1]."""
        rng = np.random.default_rng(16)
        anchor = np.array([0.0, 0.0, 0.0])
        b = RB.state_space_budget(
            _fixed_point_step,
            anchor,
            radius=0.05,
            tau=5,
            n_samples=15,
            rng=rng,
        )
        assert isinstance(b, float)
        assert 0.0 <= b <= 1.0


# --------------------------------------------------------------------------- #
#  budget_curve
# --------------------------------------------------------------------------- #
class TestBudgetCurve:
    """Grille de rayons : doit retourner un ndarray de meme longueur."""

    def test_returns_array_of_expected_length(self):
        rng = np.random.default_rng(20)
        anchor = np.array([0.0])
        radii = np.array([0.05, 0.1, 0.2, 0.5])
        curve = RB.budget_curve(
            _fixed_point_step,
            anchor,
            radii,
            tau=5,
            n_samples=10,
            rng=rng,
        )
        assert isinstance(curve, np.ndarray)
        assert curve.shape == (4,)
        assert np.all(curve >= 0.0) and np.all(curve <= 1.0)

    def test_contractive_curve_all_ones(self):
        """Dynamique tres contractive : tout le budget reste a 1.0."""
        rng = np.random.default_rng(21)
        anchor = np.array([0.0])
        radii = np.array([0.1, 1.0, 5.0])
        curve = RB.budget_curve(
            _fixed_point_step,
            anchor,
            radii,
            tau=10,
            n_samples=10,
            rng=rng,
        )
        # _fixed_point_step multiplie par 0.5 a chaque pas -> converge vers 0
        # pour tout x_init, donc succes (independamment du rayon).
        np.testing.assert_array_equal(curve, np.ones(3))

    def test_repulsive_curve_all_zeros(self):
        """Dynamique repulsive : aucun retour, courbe plate a 0."""
        rng = np.random.default_rng(22)
        anchor = np.array([0.0])
        radii = np.array([0.01, 0.05, 0.1])
        curve = RB.budget_curve(
            _repulsive_step,
            anchor,
            radii,
            tau=5,
            n_samples=10,
            rng=rng,
            bounds=(-1e6, 1e6),
        )
        np.testing.assert_array_equal(curve, np.zeros(3))

    def test_curve_accepts_list_input(self):
        """``radii`` peut etre une liste, pas seulement un ndarray."""
        rng = np.random.default_rng(23)
        anchor = np.array([0.0])
        curve = RB.budget_curve(
            _fixed_point_step,
            anchor,
            [0.1, 0.2],  # list
            tau=3,
            n_samples=5,
            rng=rng,
        )
        assert curve.shape == (2,)


# --------------------------------------------------------------------------- #
#  work_budget + work_budget_normalized
# --------------------------------------------------------------------------- #
class TestWorkBudget:
    """Distance L1/2 a P_rev."""

    def test_returns_nonneg_scalar(self):
        P, pi = _three_state_irreversible_cycle()
        b = RB.work_budget(P, pi)
        assert isinstance(b, float)
        assert b >= 0.0

    def test_reversible_chain_yields_zero(self):
        """Chaine deja reversible (P symetrique, pi uniforme) : B_work = 0."""
        P, pi = _two_state_chain()
        b = RB.work_budget(P, pi)
        assert b == pytest.approx(0.0, abs=1e-12)

    def test_asymmetric_chain_yields_positive(self):
        """Chaine a 3 etats irreversible (cycle 1->2->3->1) : distance > 0."""
        P, pi = _three_state_irreversible_cycle()
        b = RB.work_budget(P, pi)
        assert b > 0.0
        # Borne grossiere (sur tout k=3, b <= k).
        assert b <= float(P.shape[0])

    def test_invalid_matrix_raises(self):
        with pytest.raises(ValueError):
            # work_budget_normalized refuse une matrice vide.
            RB.work_budget_normalized(np.zeros((0, 0)), np.array([]))


class TestWorkBudgetNormalized:
    def test_reversible_chain_normalized_zero(self):
        P, pi = _two_state_chain()
        b = RB.work_budget_normalized(P, pi)
        assert b == pytest.approx(0.0, abs=1e-12)

    def test_normalized_bounded_above_by_one(self):
        P, pi = _three_state_irreversible_cycle()
        b = RB.work_budget_normalized(P, pi)
        assert 0.0 <= b <= 1.0

    def test_normalization_reduces_with_k(self):
        """Normaliser par k reduit la valeur pour une chaine plus grande
        a meme distance brute. C'est un convenience (pas une borne exacte)."""
        rng = np.random.default_rng(30)
        # Chaine 3x3 irreversible : B_work brute = 1.0, normalised = 1/3.
        P3, pi3 = _three_state_irreversible_cycle()
        b3 = RB.work_budget_normalized(P3, pi3)
        # 2x2 reversible : B_work brute = 0.0, normalised = 0.0.
        P2, pi2 = _two_state_chain()
        b2 = RB.work_budget_normalized(P2, pi2)
        # Les deux dans [0, 1] ; le 3x3 est non-trivialement > 0.
        assert b2 == pytest.approx(0.0, abs=1e-12)
        assert b3 > 0.0


# --------------------------------------------------------------------------- #
#  covariation_with_ews
# --------------------------------------------------------------------------- #
class TestCovariationWithEWS:
    """Contrat lecture-ressource : anti-correlation budget <-> EWS."""

    def test_returns_expected_keys(self):
        param = np.linspace(0.0, 1.0, 5)
        budgets = np.array([1.0, 0.9, 0.7, 0.4, 0.1])
        ews = np.array([0.1, 0.2, 0.4, 0.7, 1.0])  # anti-correlee
        out = RB.covariation_with_ews(param, budgets, ews)
        expected = {
            "tau_budget",
            "p_budget",
            "tau_ews",
            "p_ews",
            "tau_budget_vs_ews",
            "p_budget_vs_ews",
            "contract_valid",
        }
        assert set(out.keys()) == expected

    def test_mismatched_lengths_raise(self):
        param = np.array([0.0, 0.5, 1.0])
        budgets = np.array([1.0, 0.5])
        ews = np.array([0.0, 0.5, 1.0])
        with pytest.raises(ValueError):
            RB.covariation_with_ews(param, budgets, ews)

    def test_perfect_anticorrelation_yields_contract_valid(self):
        """param croissant, budgets decroissants lineaires, ews croissants :
        Kendall(budget, ews) doit tendre vers -1 -> contract_valid = True."""
        rng = np.random.default_rng(40)
        n = 30
        param = np.linspace(0.0, 1.0, n)
        # Budget lisse et monotonement decroissant.
        budgets = np.linspace(1.0, 0.0, n)
        # EWS lisse et monotonement croissant.
        ews = np.linspace(0.0, 1.0, n)
        out = RB.covariation_with_ews(param, budgets, ews)
        # Kendall est exact (= -1.0 sur la monotonie parfaite).
        assert out["tau_budget"] == pytest.approx(-1.0, abs=1e-9)
        assert out["tau_ews"] == pytest.approx(+1.0, abs=1e-9)
        assert out["tau_budget_vs_ews"] == pytest.approx(-1.0, abs=1e-9)
        assert out["contract_valid"] is True

    def test_correlated_inputs_make_contract_fail(self):
        """Budget et EWS correlees positivement : contract_valid = False
        (on attend une anti-correlation budget/EWS)."""
        rng = np.random.default_rng(41)
        n = 25
        param = np.linspace(0.0, 1.0, n)
        budgets = np.linspace(1.0, 0.0, n)
        ews = np.linspace(1.0, 0.0, n)  # correlee positivement avec budget
        out = RB.covariation_with_ews(param, budgets, ews)
        # tau_budget_vs_ews ~ +1.0 (correlation positive) -> contract_valid False.
        assert out["tau_budget_vs_ews"] > 0.5
        assert out["contract_valid"] is False

    def test_output_types(self):
        """Les scalaires Kendall sont des float et contract_valid un bool."""
        out = RB.covariation_with_ews(
            np.array([0.0, 0.5, 1.0]),
            np.array([1.0, 0.5, 0.0]),
            np.array([0.0, 0.5, 1.0]),
        )
        for k in ("tau_budget", "p_budget", "tau_ews", "p_ews",
                  "tau_budget_vs_ews", "p_budget_vs_ews"):
            assert isinstance(out[k], float)
        assert isinstance(out["contract_valid"], bool)


# --------------------------------------------------------------------------- #
#  Sanity : le module s'importe et la couverture couvre les 6 fonctions      #
# --------------------------------------------------------------------------- #
def test_module_exports_all_documented_functions():
    """Toute la docstring module liste 6 fonctions ; elles doivent exister."""
    for name in (
        "sample_ball",
        "state_space_budget",
        "budget_curve",
        "work_budget",
        "work_budget_normalized",
        "covariation_with_ews",
    ):
        assert hasattr(RB, name), f"ict.reversibility_budget doit exposer {name}"
