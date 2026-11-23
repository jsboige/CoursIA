"""Tests du module :mod:`ict.perceptronium` (case 27, veille #8182).

Banc pre-enregistre : ``docs/ict/perceptronium-pre-enregistrement.md`` (commit
``6d9d793b57bb``, scelle avant toute mesure). Chaque test verrouille un
invariant falsifiable du banc AVANT la mesure complete :

- identites exactes : delta_H = sqrt((n^2-1)/12) (eq. 61), noyau de Dirichlet
  f_n (eq. 63) et ses zeros, orthogonalite des etats de position ;
- eq. 80-81 contre differences finies (derivee premiere nulle, derivee
  seconde exacte) sur le potentiel de base ET un potentiel de seed ;
- controle negatif H3 = 0 : S_lin(T) = 0 machine, S'' = 0 ;
- autonomie croissante en taille sur la plage petite ;
- integration : Phi(separable) = 0, Phi(pur) = 0, optimum theorique
  {1/3,1/3,1/3,0} = 0.2516 bit, arrangement min sur permutations ;
- determinisme des potentiels de seed.

Pattern herite de ``test_assembly_index.py`` : bootstrap ``sys.path``
module-level, sans fixtures. Module autonome (stdlib + numpy + scipy).
"""

from __future__ import annotations

import math
import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import perceptronium as c  # noqa: E402


# --------------------------------------------------------------------------- #
#  Construction
# --------------------------------------------------------------------------- #


def test_equispaced_spectrum():
    for n in (2, 3, 5, 8, 16):
        h = c.equispaced_hamiltonian(n)
        ek = np.diag(h)
        assert np.allclose(np.diff(ek), 1.0)
        assert abs(ek.sum()) < 1e-12  # spectre symetrique : <H> = 0


def test_position_states_orthonormal():
    for n in (2, 4, 7, 16):
        u = c.position_unitary(n)
        assert np.allclose(u.conj().T @ u, np.eye(n), atol=1e-12)


def test_position_operator_diagonal_in_position_basis():
    n = 8
    u = c.position_unitary(n)
    x_energy = u.conj().T @ c.position_operator(n) @ u
    x_back = u @ x_energy @ u.conj().T
    assert np.allclose(x_back, c.position_operator(n), atol=1e-10)


# --------------------------------------------------------------------------- #
#  H1 : coherence energetique (eq. 61)
# --------------------------------------------------------------------------- #


def test_h1_delta_h_exact_formula():
    for n in (2, 3, 4, 8, 13, 64):
        psi = c.position_state(n, 1)
        got = c.energy_coherence(psi, c.equispaced_hamiltonian(n))
        ref = math.sqrt((n * n - 1) / 12.0)
        assert got == pytest.approx(ref, rel=1e-12)


def test_h1_mean_energy_zero():
    for n in (5, 16):
        psi = c.position_state(n, 1)
        h = c.equispaced_hamiltonian(n)
        assert abs(np.vdot(psi, h @ psi)) < 1e-12


# --------------------------------------------------------------------------- #
#  H2 : fidelite de Dirichlet (eq. 63)
# --------------------------------------------------------------------------- #


def test_h2_dirichlet_kernel_correspondence():
    """|<x1|U(t)|x1>| = |f_n(t/2)| : identite de somme geometrique."""
    for n in (2, 5, 16, 64):
        h = c.equispaced_hamiltonian(n)
        psi = c.position_state(n, 1)
        w, v = np.linalg.eigh(h)
        coef = v.conj().T @ psi
        for t in (0.3, 1.0, 2.71, 5.0):
            overlap = abs(np.sum(np.abs(coef) ** 2 * np.exp(-1j * w * t)))
            formula = abs(c.dirichlet_fn(t / 2.0, n))
            assert overlap == pytest.approx(formula, abs=1e-12)


def test_h2_zeros_at_k_pi_over_n():
    for n in (4, 7, 32):
        ks = np.arange(1, n)
        zeros = c.dirichlet_fn(math.pi * ks / n, n)
        assert np.max(np.abs(zeros)) < 1e-12


def test_h2_dirichlet_formula_at_origin():
    """lim f_n(phi->0) = 1 (fidelite en t = 0)."""
    for n in (2, 8, 33):
        val = c.dirichlet_fn(1e-9, n)
        assert abs(val - 1.0) < 1e-6


# --------------------------------------------------------------------------- #
#  H3 : eq. 80-81 contre differences finies
# --------------------------------------------------------------------------- #


@pytest.mark.parametrize("n,pot", [
    (4, "base"), (8, "base"), (16, "base"), (8, "seed7"), (32, "seed0"),
])
def test_h3_three_point_validation(n, pot):
    """Validation 3 points de l'eq. 80-81 (amendements A2/A3, pre-mesure) :
    derivee premiere nulle au-dessus du bruit, residu exact nul + egalite au
    double calcul algebrique 4.Var(V), ordre quadratique de la difference finie."""
    v = c.potential_base(n) if pot == "base" else c.potential_seed(n, int(pot[4:]))
    h, h3, psi0 = c.build_hamiltonian(n, v)
    # (1) eq. 80 : derivee premiere nulle (seuil A2 : 1e-10)
    eps = 1e-3
    s_plus = c.linear_entropy_pure(c.evolve_pure(h, psi0, eps), n)
    s_minus = c.linear_entropy_pure(c.evolve_pure(h, psi0, -eps), n)
    assert abs((s_plus - s_minus) / (2 * eps)) < 1e-10
    # (2) eq. 81 : residu nul + double calcul independant (amendement A3 --
    # etat propre de position + V diagonal => S''(0) = 4.Var(V) = 0)
    exact = c.entropy_second_derivative(h3, psi0, n)
    u = c.position_unitary(n)
    v_e = u @ np.diag(v) @ u.conj().T
    psi_sub = c.position_state(n, 1)
    v_mean = float(np.real(np.vdot(psi_sub, v_e @ psi_sub)))
    v_var = float(np.real(np.vdot(psi_sub, (v_e @ v_e) @ psi_sub))) - v_mean ** 2
    assert abs(exact) < 1e-12
    assert exact == pytest.approx(4.0 * v_var, abs=1e-12)
    # (3) regime quartique : courbure effective en differences finies ∝ dt^2
    # (paire dt 1e-2/2e-2 : signal au-dessus du bruit d'entropie)
    fd1 = c.entropy_curvature_finite(h, psi0, n, dt=1e-2)
    fd2 = c.entropy_curvature_finite(h, psi0, n, dt=2e-2)
    if fd1 > 1e-8 and fd2 > 1e-8:
        assert 3.5 < fd2 / fd1 < 4.5


# --------------------------------------------------------------------------- #
#  Controle negatif : H3 = 0
# --------------------------------------------------------------------------- #


def test_control_decoupled_no_entropy():
    for b in (2, 4, 6):
        n = 2 ** b
        h, h3, psi0 = c.build_hamiltonian(n, np.zeros(n))
        psi_t = c.evolve_pure(h, psi0, c.T_ORBIT)
        assert c.linear_entropy_pure(psi_t, n) < 1e-12
        assert abs(c.entropy_second_derivative(h3, psi0, n)) < 1e-12


def test_control_autonomy_infinite_when_decoupled():
    tau_dyn, tau_ind, a = c.autonomy(2.0, 0.0)
    assert tau_ind == math.inf and a == math.inf
    assert tau_dyn == 0.5


# --------------------------------------------------------------------------- #
#  Banc : mesures par taille
# --------------------------------------------------------------------------- #


def test_measure_size_matches_h1_and_control_scales():
    n = 8
    m = c.measure_size(n, c.potential_base(n))
    assert m["delta_h"] == pytest.approx(math.sqrt((n * n - 1) / 12.0), rel=1e-12)
    assert 0.0 < m["s_lin_T"] < 1.0
    # A2/A3 scelles (pre-enregistrement) : pour l'etat propre de position de la
    # construction du papier, eq. 81 predit S''(0) = 0 exactement (temoin A3,
    # residu < 1e-12). La difference finie ne se compare a eq. 81 QUE si elle
    # est au-dessus du bruit numerique : au dt par defaut (1e-4), S(dt) est au
    # plancher eps machine et fd ne mesure que la troncature O(dt^2), pas un
    # accord. Le critere scelle est la signature quartique : quand le signal
    # sort du bruit, fd(2dt)/fd(dt) -> (2dt)^2/dt^2 = 4 (bande [3.5, 4.5]).
    assert abs(m["s_ddot_eq81"]) < 1e-12
    h, _h3, psi0 = c.build_hamiltonian(n, c.potential_base(n))
    fd_a = c.entropy_curvature_finite(h, psi0, n, dt=1e-2)
    fd_b = c.entropy_curvature_finite(h, psi0, n, dt=2e-2)
    assert 3.5 <= fd_b / fd_a <= 4.5
    assert m["autonomy"] == pytest.approx(m["tau_ind"] / m["tau_dyn"])


def test_effective_autonomy_finite_positive_coupled():
    """Invariant d'instrument : couple => A_eff fini et positif (la croissance en
    taille est la prediction H5, tranchee par le banc, pas par les tests)."""
    for b in (2, 3, 4, 5):
        n = 2 ** b
        m = c.measure_size(n, c.potential_base(n))
        assert math.isfinite(m["autonomy_effective"])
        assert m["autonomy_effective"] > 0.0


def test_effective_autonomy_formula():
    """A_eff = tau_ind_eff / tau_dyn avec tau_ind_eff = sqrt(T^2/(2 S(T)))."""
    d_h, s_t, t = 2.5, 1e-4, 2 * math.pi
    tau_dyn = 1.0 / d_h
    tau_ind_eff = math.sqrt(t * t / (2.0 * s_t))
    assert c.effective_autonomy(d_h, s_t, t) == pytest.approx(tau_ind_eff * d_h)
    assert c.effective_autonomy(d_h, 0.0, t) == math.inf


def test_potential_seed_deterministic_and_normalized():
    for s in (0, 1, 7, 42, 99):
        v1 = c.potential_seed(32, s)
        v2 = c.potential_seed(32, s)
        assert np.array_equal(v1, v2)
        assert float(np.max(np.abs(v1))) == pytest.approx(
            float(np.max(np.abs(c.potential_base(32)))), rel=1e-12)
        va = c.potential_seed(32, 99)
        assert not np.allclose(va, c.potential_seed(32, 0))


def test_potential_base_one_full_sinusoid():
    v = c.potential_base(16)
    xs = np.arange(16)
    assert np.allclose(v, np.sin(2 * math.pi * xs / 16))


# --------------------------------------------------------------------------- #
#  Integration (section II.C-II.D)
# --------------------------------------------------------------------------- #


def test_mutual_info_arrangement_hand_computed():
    # Lambda = (1/3, 1/3 ; 1/3, 0) : I = 2 H(2/3) - log2(3) = 0.2516 bit
    lam = np.array([[1 / 3, 1 / 3], [1 / 3, 0.0]])
    assert c.mutual_info_arrangement(lam) == pytest.approx(0.251629, abs=1e-5)
    # arrangement separable : I = 0
    sep = np.array([[0.5, 0.0], [0.5, 0.0]])
    assert c.mutual_info_arrangement(sep) == pytest.approx(0.0, abs=1e-12)


def test_phi_optimum_theory_spectrum():
    got = c.phi_from_spectrum([1 / 3, 1 / 3, 1 / 3, 0.0])
    paper = math.log(27 / 16) / math.log(8)      # expression close-form du papier
    assert got == pytest.approx(paper, abs=1e-9)
    assert got == pytest.approx(0.2516, abs=1e-4)  # arrondi 4 decimales du papier


def test_phi_separable_and_pure_zero():
    assert c.phi_from_spectrum([0.5, 0.5, 0.0, 0.0]) == pytest.approx(0.0, abs=1e-12)
    assert c.phi_from_spectrum([1.0, 0.0, 0.0, 0.0]) == pytest.approx(0.0, abs=1e-12)


def test_phi_unitary_invariance():
    """rhoDC : Phi ne depend que du spectre -- verifie sur un etat melange tourne."""
    lam = np.array([0.4, 0.3, 0.2, 0.1])
    rng = np.random.default_rng(3)
    z = rng.normal(size=(4, 4)) + 1j * rng.normal(size=(4, 4))
    q, _ = np.linalg.qr(z)
    rho = q @ np.diag(lam) @ q.conj().T
    assert c.phi_integrated_information(rho) == pytest.approx(
        c.phi_from_spectrum(lam), abs=1e-10)


def test_phi_k2_below_optimum():
    """k = 2 : spectre {1/2, 1/2, 0, 0} -- arrangement separable, Phi = 0."""
    assert c.phi_from_spectrum([0.5, 0.5, 0.0, 0.0]) < 0.2516


# --------------------------------------------------------------------------- #
#  Ajustements
# --------------------------------------------------------------------------- #


def test_ols_slope_exact_line():
    xs = [5, 6, 7, 8, 9]
    ys = [-4.0 * x + 3 for x in xs]
    assert c.ols_slope(xs, ys) == pytest.approx(-4.0, abs=1e-9)


def test_measure_size_keys():
    """Cles de mesure completes sur une taille (la boucle complete tourne en main)."""
    m = c.measure_size(8, c.potential_base(8))
    assert set(m) >= {"delta_h", "s_lin_T", "s_ddot_eq81", "s_ddot_finite",
                      "tau_dyn", "tau_ind", "autonomy"}
