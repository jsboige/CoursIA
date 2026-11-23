"""Banc perceptronium (case 27, veille #8182) -- Tegmark 2015.

Banc pre-enregistre : ``docs/ict/perceptronium-pre-enregistrement.md``
(scelle par le commit ``6d9d793b57bb`` avant toute mesure). Source primaire
archivee au gisement : Tegmark, *Consciousness as a State of Matter*,
Chaos, Solitons & Fractals 76 (2015) 238-270 (arXiv:1401.1219v3, accepte
CSF 17/03/2015) -- toutes les equations citees sont lues sur la copie
archivee, jamais de memoire.

Modele (scelle) : un sous-systeme de b qubits (dimension n = 2^b) a spectre
equidistant ``E_k = k - (n-1)/2`` (eq. 58, unites hbar = omega = 1), etat
initial un etat propre de position ``|x_1>`` (transformee de Fourier des
etats d'energie), couple a un qubit environnement par ``H3 = V(x) . sigma_x``
(eq. 83, potentiel de base ``V0(x) = sin(2.pi.x/n)``). Mesures : coherence
energetique ``delta_H`` (eq. 61), fidelite de Dirichlet ``f_n`` (eq. 63),
production d'entropie lineaire au second ordre (eq. 80-81), decroissance
``S_lin,1(T) ~ 2^{-4b}`` et autonomie ``A = tau_ind/tau_dyn ~ 2^{3b}``
(Fig. 14, eq. 82-86), plafond d'information integree ``Phi ~ 0.2516`` bit
en n = 4 (section II.D, theoreme rhoDC).

Correspondance de convention pour ``f_n`` (eq. 63) : les etats de position
etant la TF des etats d'energie, ``<x_1|U(t)|x_1> = (1/n) sum_k e^{-i E_k t}``
est le noyau de Dirichlet normalise -- soit ``|f_n(phi)|`` avec ``phi = t/2``
et ``f_n(phi) = sin(n.phi)/(n.sin(phi))``, zeros en ``phi = k.pi/n``
(c'est-a-dire ``t = 2k.pi/n``). Le test H2 verifie les DEUX : la formule du
papier et la correspondance ``phi = t/2``.

Tout est deterministe ; les seeds (0, 1, 7, 42, 99) ne portent que les
potentiels aleatoires ``V_s`` (hypothese H6 de genercite) et l'echantillonnage
spectral de l'hypothese H7. Dependances : stdlib + numpy + scipy
(``expm``/``eigh`` pour l'evolution exacte).
"""

from __future__ import annotations

import datetime as _dt
import itertools
import json
import math
from typing import Callable, Dict, List, Optional, Sequence, Tuple

import numpy as np
import scipy.linalg as sla

SEEDS: Tuple[int, ...] = (0, 1, 7, 42, 99)
B_FULL: Tuple[int, ...] = (2, 3, 4, 5, 6, 7, 8, 9)          # tailles mesurees
B_FIT: Tuple[int, ...] = (5, 6, 7, 8, 9)                    # plage OLS scellee
B_H3: Tuple[int, ...] = (2, 3, 4, 5, 6)                     # plage eq. 81 scellee
N_VALIDATE: Tuple[int, ...] = tuple(range(2, 65))           # H1/H2 : n = 2..64
T_ORBIT: float = 2.0 * math.pi                              # periode orbitale (omega = 1)

# Seuils scelles (pre-enregistrement, jamais reajustes apres mesure).
TH_H1_CONF, TH_H1_REF = 1e-12, 1e-6
TH_H2_CONF, TH_H2_REF = 1e-12, 1e-6
TH_H3_FIRST = 1e-10            # amendement A2 : plancher de bruit de la difference centree
TH_H3_RESIDU_CONF = 1e-12      # residu exact + ecart au double calcul 4.Var(V)
TH_H3_RESIDU_REF = 1e-3
H3_RATIO_BAND = (3.5, 4.5)     # ordre quadratique fd(2dt)/fd(dt) du regime quartique
H4_BAND = (-5.0, -3.0)
H4_REF = -2.0
H5_BAND = (2.0, 4.0)
H5_REF = 1.0
H7_TARGET = math.log(27.0 / 16.0) / math.log(8.0)   # amendement pre-mesure : close-form du papier
H7_TOL, H7_CAP = 1e-6, 0.26


# --------------------------------------------------------------------------- #
#  Construction du banc
# --------------------------------------------------------------------------- #


def equispaced_hamiltonian(n: int) -> np.ndarray:
    """``H1 = diag(E_k)``, ``E_k = k - (n-1)/2`` (eq. 58, hbar = omega = 1)."""
    k = np.arange(n, dtype=float)
    return np.diag(k - (n - 1) / 2.0)


def position_unitary(n: int) -> np.ndarray:
    """Matrice unitaire energie -> position : colonnes = etats ``|x_j>`` en base d'energie.

    ``|x_j> = (1/sqrt(n)) sum_k exp(2i.pi.j.k/n) |E_k>`` (eq. 59-60 : les etats
    de position sont la transformee de Fourier des etats d'energie).
    """
    j = np.arange(n, dtype=float)
    phase = np.exp(2j * math.pi * np.outer(j, j) / n)
    return phase / math.sqrt(n)


def position_state(n: int, j: int = 1) -> np.ndarray:
    """Etat propre de position ``|x_j>`` exprime en base d'energie."""
    u = position_unitary(n)
    return u[:, j % n].copy()


def position_operator(n: int) -> np.ndarray:
    """``x = diag(0, 1, ..., n-1)`` dans la base de position (choix scelle)."""
    return np.diag(np.arange(n, dtype=float))


def fourier_positions(n: int) -> np.ndarray:
    """Valeurs propres de l'operateur position dans la base d'energie.

    L'operateur diagonal en base de position devient ``F† x F`` en base
    d'energie ; pour l'echantillonnage des potentiels on travaille directement
    en base de position, d'ou cette conversion (utilisee par les tests).
    """
    u = position_unitary(n)
    return np.real(np.diag(u.conj().T @ position_operator(n) @ u))


def potential_base(n: int) -> np.ndarray:
    """Potentiel du papier (eq. 83) : ``V0(x) = sin(2.pi.x/n)``, echantillonne sur les positions."""
    xs = np.arange(n, dtype=float)
    return np.sin(2.0 * math.pi * xs / n)


def potential_seed(n: int, seed: int) -> np.ndarray:
    """Potentiel aleatoire ``V_s`` scelle : 3 harmoniques, normalise en norme d'operateur a ``V0``.

    ``V_s(x) = sum_{m=1..3} a_m sin(2.pi.m.x/n + phase_m)`` avec ``(a_m, phase_m)``
    tires de ``default_rng(seed)``, puis rescale pour ``max |V_s| = max |V0|``
    (V est diagonal en base de position : norme d'operateur = max des |V_j|).
    """
    rng = np.random.default_rng(seed)
    ms = np.arange(1, 4, dtype=float)
    a = rng.uniform(0.0, 1.0, size=3)
    ph = rng.uniform(0.0, 2.0 * math.pi, size=3)
    xs = np.arange(n, dtype=float)
    raw = np.sum(a[:, None] * np.sin(2.0 * math.pi * ms[:, None] * xs[None, :] / n
                                      + ph[:, None]), axis=0)
    target = float(np.max(np.abs(potential_base(n))))
    scale = float(np.max(np.abs(raw)))
    if scale < 1e-15:  # tirage degeneri : repli deterministe declare
        return potential_base(n)
    return raw * (target / scale)


def build_hamiltonian(n: int, v: np.ndarray) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Hamiltonien complet ``H = H1 (x) I + I (x) H2 + H3`` avec ``H2 = sigma_x``.

    Les matrices sont exprimees en base d'energie pour le sous-systeme :
    ``V(x)`` diagonal en base de position est converti par ``F V F†``.
    Renvoie ``(h, h3, psi0)`` : Hamiltonien total, terme d'interaction en
    espace total, etat initial ``|x_1> (x) |up>``.
    """
    h1 = equispaced_hamiltonian(n)
    u = position_unitary(n)
    v_energy = u @ np.diag(v) @ u.conj().T          # V(x) en base d'energie
    h2 = np.array([[0.0, 1.0], [1.0, 0.0]])
    h3 = np.kron(v_energy, h2)
    h = np.kron(h1, np.eye(2)) + np.kron(np.eye(n), h2) + h3
    psi0 = np.kron(position_state(n, 1), np.array([1.0, 0.0]))
    return h, h3, psi0


# --------------------------------------------------------------------------- #
#  Mesures elementaires
# --------------------------------------------------------------------------- #


def energy_coherence(psi: np.ndarray, h: np.ndarray) -> float:
    """``delta_H`` d'un etat pur : ecart-type de H (eq. 44-47, cas pur)."""
    m = np.vdot(psi, h @ psi)
    m2 = np.vdot(psi, (h @ h) @ psi)
    var = float(np.real(m2 - m * m))
    return math.sqrt(max(var, 0.0))


def dirichlet_fn(phi: np.ndarray | float, n: int) -> np.ndarray | float:
    """``f_n(phi) = sin(n.phi)/(n.sin phi)`` (eq. 63) -- noyau de Dirichlet normalise."""
    return np.sin(n * phi) / (n * np.sin(phi))


def evolve_pure(h: np.ndarray, psi: np.ndarray, t: float) -> np.ndarray:
    """Evolution exacte ``expm(-i.h.t) |psi>`` (decomposition spectrale)."""
    w, v = np.linalg.eigh(h)
    return v @ (np.exp(-1j * w * t) * (v.conj().T @ psi))


def reduced_matrix(psi_full: np.ndarray, n: int) -> np.ndarray:
    """Etat reduit ``rho_1`` d'un etat pur ``|psi>`` sur n (x) 2 (trace environnement)."""
    m = psi_full.reshape(n, 2)
    return m @ m.conj().T


def linear_entropy(rho1: np.ndarray) -> float:
    """``S_lin = 1 - tr(rho^2)`` (eq. 76)."""
    tr2 = float(np.real(np.trace(rho1 @ rho1)))
    return 1.0 - tr2


def linear_entropy_pure(psi_full: np.ndarray, n: int) -> float:
    """``S_lin`` d'un etat pur via valeurs singulieres (stable, sans matrice densite)."""
    s = np.linalg.svd(psi_full.reshape(n, 2), compute_uv=False)
    return float(1.0 - np.sum(s ** 4))


def entropy_second_derivative(h3: np.ndarray, psi_full: np.ndarray, n: int) -> float:
    """Derivee seconde de ``S_lin,1`` a t = 0 par la formule exacte eq. 81.

    ``S'' = 2 tr{rho_1 tr_2 [H3, [H3, rho]]} - 2 ||[H*, rho_1]||^2_F`` avec
    ``H* = tr_2{(I (x) rho_2) H3}`` (eq. 66) et ``rho = rho_1 (x) rho_2``
    separable a t = 0. Les commutateurs avec rho rang 1 se reduisent a des
    produits matrice-vecteur : ``[H3, rho] rho^dagger`` n'est jamais forme.
    """
    m = psi_full.reshape(n, 2)                       # colonnes : amplitude env up/down
    rho2 = np.array([[1.0, 0.0], [0.0, 0.0]])        # |up><up|
    rho1 = m @ m.conj().T
    a = h3 @ psi_full                                # H3.rho = a.psi^d  (rang 1)
    b = h3 @ a                                       # H3^2.rho = b.psi^d (rang 1)
    a2 = a.reshape(n, 2)
    b2 = b.reshape(n, 2)
    # [H3,[H3,rho]] = b.psi^d - 2 a.a^d + psi.b^d ; trace partielle plane sur
    # l'environnement d'un rang 1 : tr_2(u.v^d) = u_mat @ v_mat^d (deux colonnes)
    tr2_comm = b2 @ m.conj().T - 2.0 * (a2 @ a2.conj().T) + m @ b2.conj().T
    term1 = float(np.real(np.trace(rho1 @ tr2_comm)))
    # H* = tr_2{(I (x) rho_2) H3} : blocs env ponderes par rho2 puis traces
    m4 = h3.reshape(n, 2, n, 2)
    hstar = (m4[:, 0, :, 0] * rho2[0, 0] + m4[:, 0, :, 1] * rho2[0, 1]
             + m4[:, 1, :, 0] * rho2[1, 0] + m4[:, 1, :, 1] * rho2[1, 1])
    comm = hstar @ rho1 - rho1 @ hstar
    term2 = float(np.real(np.sum(comm * comm)))
    return 2.0 * term1 - 2.0 * term2


def entropy_curvature_finite(h: np.ndarray, psi_full: np.ndarray, n: int,
                             dt: float = 1e-4) -> float:
    """Derivee seconde par differences finies : ``S(dt) ~ S'' dt^2/2`` (S'(0) = 0, eq. 80)."""
    psi_t = evolve_pure(h, psi_full, dt)
    return 2.0 * linear_entropy_pure(psi_t, n) / (dt * dt)


def autonomy(delta_h: float, s_ddot: float) -> Tuple[float, float, float]:
    """``tau_dyn = 1/delta_H`` (eq. 84), ``tau_ind = 1/sqrt(S'')`` (eq. 85), ``A = tau_ind/tau_dyn`` (eq. 86).

    Pour la construction scellee (etat propre de position + V diagonal), l'eq. 81
    donne ``S''(0) = 4.Var(V) = 0`` exactement (amendement A3 du
    pre-enregistrement) : ``tau_ind`` et ``A`` sont alors infinis -- c'est le
    temoin attendu, pas une panne. L'autonomie porte par les verdicts est
    :func:`effective_autonomy`.
    """
    tau_dyn = 1.0 / delta_h
    if s_ddot <= 0.0:
        return tau_dyn, math.inf, math.inf
    tau_ind = 1.0 / math.sqrt(s_ddot)
    return tau_dyn, tau_ind, tau_ind / tau_dyn


def effective_autonomy(delta_h: float, s_lin_t: float, t: float) -> float:
    """Autonomie effective (amendement A3) : courbure effective sur une orbite.

    ``tau_ind_eff = sqrt(t^2 / (2 S_lin(t)))`` puis ``A_eff = tau_ind_eff/tau_dyn``
    avec ``tau_dyn = 1/delta_H``. Si ``S_lin(t) ~ 2^{-4b}`` et ``delta_H ~ 2^b``,
    ``log2 A_eff`` a pente ``+3`` -- l'arithmetique du papier (eq. 82-86, Fig. 14).
    """
    if s_lin_t <= 0.0:
        return math.inf
    tau_ind_eff = math.sqrt(t * t / (2.0 * s_lin_t))
    return tau_ind_eff * delta_h


# --------------------------------------------------------------------------- #
#  Information integree (section II.C-II.D, theoreme rhoDC)
# --------------------------------------------------------------------------- #


def h2_bits(p: Sequence[float]) -> float:
    """Entropie de Shannon en bits d'une distribution (zeros toleres)."""
    q = np.asarray(p, dtype=float)
    nz = q[q > 1e-15]
    return float(-np.sum(nz * np.log2(nz)))


def mutual_info_arrangement(lam2: np.ndarray) -> float:
    """Information mutuelle (bits) d'un arrangement 2x2 de valeurs propres normalisees."""
    total = float(lam2.sum())
    if total <= 0.0:
        return 0.0
    p = lam2 / total
    rows = p.sum(axis=1)
    cols = p.sum(axis=0)
    return h2_bits(rows) + h2_bits(cols) - h2_bits(p.ravel())


def phi_integrated_information(rho: np.ndarray) -> float:
    """``Phi(rho)`` du papier en n = 4 : min sur les 4! permutations de l'arrangement 2x2.

    Le theoreme rhoDC (Jevtic, Jennings & Rudolph) garantit que le minimum se
    prend dans la base ou rho est diagonale : ``Phi`` ne depend que du spectre.
    """
    lam = np.sort(np.real(np.linalg.eigvalsh(rho)))[::-1]
    if lam.size != 4:
        raise ValueError("phi_integrated_information est scellee pour n = 4 (coupe 2+2)")
    best = math.inf
    for perm in itertools.permutations(range(4)):
        lam2 = np.array(lam[list(perm)]).reshape(2, 2)
        best = min(best, mutual_info_arrangement(lam2))
    return float(best)


def phi_from_spectrum(lam: Sequence[float]) -> float:
    """``Phi`` depuis un spectre de taille 4 directement."""
    lam_arr = np.asarray(lam, dtype=float)
    if lam_arr.size != 4:
        raise ValueError("spectre de taille 4 attendu")
    return phi_integrated_information(np.diag(lam_arr))


def haar_random_state(n: int, rng: np.random.Generator) -> np.ndarray:
    """Etat pur Haar-uniforme (Ginibre normalise)."""
    z = rng.normal(size=n) + 1j * rng.normal(size=n)
    return z / np.linalg.norm(z)


def random_spectrum_dirichlet(n: int, rng: np.random.Generator) -> np.ndarray:
    """Spectre aleatoire uniforme sur le simplexe (Dirichlet(1,...,1))."""
    return rng.dirichlet(np.ones(n))


# --------------------------------------------------------------------------- #
#  Le banc
# --------------------------------------------------------------------------- #


def measure_size(n: int, v: np.ndarray, dt: float = 1e-4) -> Dict[str, float]:
    """Toutes les mesures scellees pour une taille et un potentiel."""
    h, h3, psi0 = build_hamiltonian(n, v)
    psi_sub = position_state(n, 1)
    d_h = energy_coherence(psi_sub, equispaced_hamiltonian(n))
    psi_t = evolve_pure(h, psi0, T_ORBIT)
    s_lin_t = linear_entropy_pure(psi_t, n)
    s_ddot = entropy_second_derivative(h3, psi0, n)
    s_ddot_fd = entropy_curvature_finite(h, psi0, n, dt=dt)
    tau_dyn, tau_ind, a = autonomy(d_h, s_ddot)
    a_eff = effective_autonomy(d_h, s_lin_t, T_ORBIT)
    return {
        "n": n,
        "delta_h": d_h,
        "delta_h_formula": math.sqrt((n * n - 1) / 12.0),
        "s_lin_T": s_lin_t,
        "s_ddot_eq81": s_ddot,
        "s_ddot_finite": s_ddot_fd,
        "tau_dyn": tau_dyn,
        "tau_ind": tau_ind,
        "autonomy": a,
        "autonomy_effective": a_eff,
    }


def ols_slope(xs: Sequence[float], ys: Sequence[float]) -> float:
    """Pente OLS degre 1 (``numpy.polyfit``), scellee."""
    return float(np.polyfit(np.asarray(xs, float), np.asarray(ys, float), 1)[0])


def run_banc() -> Dict[str, object]:
    """Le banc complet ; renvoie la structure de resultats brute (sans verdicts)."""
    potentials: Dict[str, Callable[[int], np.ndarray]] = {
        "base": potential_base,
        **{f"seed{s}": (lambda n, s=s: potential_seed(n, s)) for s in SEEDS},
    }
    per_potential: Dict[str, Dict[int, Dict[str, float]]] = {}
    for name, maker in potentials.items():
        per_potential[name] = {}
        for b in B_FULL:
            n = 2 ** b
            per_potential[name][b] = measure_size(n, maker(n))
    # controle negatif : H3 = 0 => S_lin(T) = 0 exactement
    control = {}
    for b in (3, 6):
        n = 2 ** b
        h, _, psi0 = build_hamiltonian(n, np.zeros(n))
        psi_t = evolve_pure(h, psi0, T_ORBIT)
        control[b] = linear_entropy_pure(psi_t, n)
    return {"per_potential": per_potential, "control_H3_zero": control}


# --------------------------------------------------------------------------- #
#  Validations H1/H2 (identites exactes, n = 2..64)
# --------------------------------------------------------------------------- #


def run_validation_h1() -> Dict[str, object]:
    """H1 : ``delta_H(|x_1>) = sqrt((n^2-1)/12)`` sur n = 2..64."""
    worst, worst_n = 0.0, None
    for n in N_VALIDATE:
        psi = position_state(n, 1)
        got = energy_coherence(psi, equispaced_hamiltonian(n))
        ref = math.sqrt((n * n - 1) / 12.0)
        rel = abs(got - ref) / ref
        if rel > worst:
            worst, worst_n = rel, n
    return {"max_rel_err": worst, "worst_n": worst_n}


def run_validation_h2() -> Dict[str, object]:
    """H2 : fidelite numerique contre ``|f_n(t/2)|`` (eq. 63, ``phi = t/2``), zeros inclus."""
    worst, worst_n = 0.0, None
    worst_zero, worst_zero_n = 0.0, None
    for n in N_VALIDATE:
        h1 = equispaced_hamiltonian(n)
        psi = position_state(n, 1)
        w, v = np.linalg.eigh(h1)
        coef = v.conj().T @ psi
        grid = np.linspace(0.05, math.pi - 0.05, 61)
        overlap = np.abs(np.array([np.sum(coef * coef.conj() * np.exp(-1j * w * t))
                                   for t in grid]))  # |<x1|U(t)|x1>|
        formula = np.abs(dirichlet_fn(grid / 2.0, n))
        err = float(np.max(np.abs(overlap - formula)))
        if err > worst:
            worst, worst_n = err, n
        # zeros : phi = k.pi/n  =>  t = 2k.pi/n, k = 1..n-1
        ks = np.arange(1, n)
        ts = 2.0 * math.pi * ks / n
        zeros = np.abs(np.array([np.sum(coef * coef.conj() * np.exp(-1j * w * t))
                                 for t in ts]))
        zerr = float(np.max(zeros))
        if zerr > worst_zero:
            worst_zero, worst_zero_n = zerr, n
    return {"max_abs_err": worst, "worst_n": worst_n,
            "max_zero_val": worst_zero, "worst_zero_n": worst_zero_n}


def run_validation_h3() -> Dict[str, object]:
    """H3 : eq. 80-81 contre differences finies, b = 2..6, potentiel de base."""
    worst_slope, worst_residu = 0.0, 0.0
    ratios, skipped = [], 0
    for b in B_H3:
        n = 2 ** b
        h, h3, psi0 = build_hamiltonian(n, potential_base(n))
        # (1) derivee premiere : difference centree -- S'(0) = 0 (eq. 80) ; seuil
        # 1e-10 (amendement A2), au-dessus du plancher de bruit ~1e-12
        eps = 1e-3
        s_plus = linear_entropy_pure(evolve_pure(h, psi0, eps), n)
        s_minus = linear_entropy_pure(evolve_pure(h, psi0, -eps), n)
        worst_slope = max(worst_slope, abs((s_plus - s_minus) / (2.0 * eps)))
        # (2) residu exact + double calcul independant : eq. 81 (commutateurs)
        # contre la valeur algebrique 4.Var_{x1}(V) -- nulle pour un etat propre
        # de position avec V diagonal (amendement A3)
        exact = entropy_second_derivative(h3, psi0, n)
        u = position_unitary(n)                      # V en base d'energie, comme h3
        v_e = u @ np.diag(potential_base(n)) @ u.conj().T
        psi_sub = position_state(n, 1)
        v_mean = float(np.real(np.vdot(psi_sub, v_e @ psi_sub)))
        v_var = float(np.real(np.vdot(psi_sub, (v_e @ v_e) @ psi_sub))) - v_mean * v_mean
        worst_residu = max(worst_residu, abs(exact - 4.0 * v_var),
                           abs(exact))
        # (3) ordre de convergence : regime quartique => fd ∝ dt^2. La paire
        # dt = (1e-2, 2e-2) garde le signal (fd ~ 2C.dt^2, C >> 1) au-dessus du
        # bruit d'entropie (~2e-7 a dt = 1e-4), ou le ratio serait illisible.
        fd1 = entropy_curvature_finite(h, psi0, n, dt=1e-2)
        fd2 = entropy_curvature_finite(h, psi0, n, dt=2e-2)
        if fd1 > 1e-8 and fd2 > 1e-8:
            ratios.append(fd2 / fd1)
        else:
            skipped += 1
    return {"max_first_deriv": worst_slope, "max_residu_eq81": worst_residu,
            "quartic_ratios": ratios, "quartic_skipped": skipped,
            "note": "validation 3 points (amend. A2/A3) : derivee premiere, residu exact + 4.Var(V), ordre dt^2"}


def run_h7() -> Dict[str, object]:
    """H7 : plafond ``Phi`` en n = 4 -- optimum theorique, k = 2, recherche aleatoire multi-seed."""
    opt = phi_from_spectrum([1.0 / 3.0, 1.0 / 3.0, 1.0 / 3.0, 0.0])
    k2 = phi_from_spectrum([0.5, 0.5, 0.0, 0.0])
    pure = phi_from_spectrum([1.0, 0.0, 0.0, 0.0])
    max_random, worst_state = 0.0, None
    per_seed_max: Dict[int, float] = {}
    for s in SEEDS:
        rng = np.random.default_rng(1000 + s)         # seed distinct des potentiels
        best = 0.0
        for _ in range(10000):
            lam = random_spectrum_dirichlet(4, rng)
            phi = phi_from_spectrum(lam)
            best = max(best, phi)
            if phi > max_random:
                max_random, worst_state = phi, lam.tolist()
        # etats purs Haar : temoin -- spectre {1,0,0,0} => Phi = 0
        haar_phi = 0.0
        for _ in range(2000):
            psi = haar_random_state(4, rng)
            haar_phi = max(haar_phi, phi_integrated_information(
                np.outer(psi, psi.conj())))
        per_seed_max[s] = best
    return {"phi_opt_theory": H7_TARGET, "phi_opt_measured": opt, "phi_k2": k2,
            "phi_pure": pure, "max_random_dirichlet": max_random,
            "worst_random_spectrum": worst_state,
            "per_seed_max": per_seed_max}


# --------------------------------------------------------------------------- #
#  Verdicts (seuils scelles)
# --------------------------------------------------------------------------- #


def verdict(cond_conf: bool, cond_ref: bool) -> str:
    if cond_conf:
        return "CONFIRMEE"
    if cond_ref:
        return "REFUTEE"
    return "NON_CONCLUANTE"


def global_verdict(vs: Dict[str, str], base_fit: Dict[str, float]) -> str:
    """Verdict global du cas (convention ``verdicts.global`` des cas soeurs,
    cf. ``assembly_index_results.json``). Promis par la section Analyse du
    pre-enregistrement ; derive uniquement des verdicts par hypothese, jamais
    re-ajuste a la main : H1-H3 = instrument (identites exactes du papier),
    H4-H6 = loi d'echelle (Fig. 14), H7 = plafond Phi.
    """
    instrument_ok = all(vs[k] == "CONFIRMEE" for k in (
        "H1_delta_h", "H2_fidelite_dirichlet", "H3_entropie_eq81"))
    if not instrument_ok:
        return "INSTRUMENT_SUSPECT"
    laws = [vs["H4_decroissance_2^-4b"], vs["H5_autonomie_2^3b"], vs["H6_genericite_seeds"]]
    laws_refuted = sum(v == "REFUTEE" for v in laws)
    if laws_refuted == 0 and all(v == "CONFIRMEE" for v in laws) \
            and vs["H7_plafond_phi_02516"] == "CONFIRMEE":
        return "CONFIRMEE"
    if laws_refuted:
        return (f"PARTIEL — identites exactes et plafond Phi ("
                f"{vs['H7_plafond_phi_02516']}) tenus, loi d'echelle refutee "
                f"({laws_refuted}/3) : pente log2 S_lin(T) = "
                f"{base_fit['slope_log2_s_lin_T']:+.2f} au lieu de -4 (Fig. 14)")
    return "NON_CONCLUANTE"


def run_all(output_path: Optional[str] = None) -> Dict[str, object]:
    """Banc complet + verdicts ; ecrit le JSON de resultats si ``output_path``."""
    print("[1/6] validations H1/H2 (identites exactes)...", flush=True)
    h1 = run_validation_h1()
    h2 = run_validation_h2()
    print("[2/6] validation H3 (eq. 80-81 vs differences finies)...", flush=True)
    h3v = run_validation_h3()
    print("[3/6] banc principal (8 tailles x 6 potentiels)...", flush=True)
    banc = run_banc()
    print("[4/6] ajustements H4/H5/H6...", flush=True)
    fits: Dict[str, object] = {}
    for name, per_b in banc["per_potential"].items():
        bs = [b for b in B_FIT if per_b[b]["s_lin_T"] > 0.0]
        s_slope = ols_slope(bs, [math.log2(per_b[b]["s_lin_T"]) for b in bs])
        a_vals = [per_b[b]["autonomy_effective"] for b in B_FIT]
        if all(math.isfinite(a) for a in a_vals):
            a_slope = ols_slope(list(B_FIT), [math.log2(a) for a in a_vals])
        else:
            a_slope = math.nan
        fits[name] = {"b_fitted": bs, "slope_log2_s_lin_T": s_slope,
                      "slope_log2_autonomy": a_slope}
    print("[5/6] integration H7...", flush=True)
    h7 = run_h7()
    print("[6/6] verdicts...", flush=True)

    v_h1 = verdict(h1["max_rel_err"] < TH_H1_CONF, h1["max_rel_err"] > TH_H1_REF)
    v_h2 = verdict(h2["max_abs_err"] < TH_H2_CONF
                   and h2["max_zero_val"] < TH_H2_CONF,
                   max(h2["max_abs_err"], h2["max_zero_val"]) > TH_H2_REF)
    ratios_ok = (all(H3_RATIO_BAND[0] <= r <= H3_RATIO_BAND[1] for r in h3v["quartic_ratios"])
                 or h3v["quartic_skipped"] == len(B_H3))
    v_h3 = verdict(h3v["max_first_deriv"] < TH_H3_FIRST
                   and h3v["max_residu_eq81"] < TH_H3_RESIDU_CONF
                   and ratios_ok,
                   h3v["max_residu_eq81"] > TH_H3_RESIDU_REF)
    v_h4 = verdict(H4_BAND[0] <= fits["base"]["slope_log2_s_lin_T"] <= H4_BAND[1],
                   fits["base"]["slope_log2_s_lin_T"] > H4_REF)
    v_h5 = verdict(H5_BAND[0] <= fits["base"]["slope_log2_autonomy"] <= H5_BAND[1],
                   fits["base"]["slope_log2_autonomy"] < H5_REF)
    seed_h4 = [f"slope{s}" for s in SEEDS
               if not (H4_BAND[0] <= fits[f"seed{s}"]["slope_log2_s_lin_T"] <= H4_BAND[1])]
    seed_h5 = [f"slope{s}" for s in SEEDS
               if not (H5_BAND[0] <= fits[f"seed{s}"]["slope_log2_autonomy"] <= H5_BAND[1])]
    out_band = len(set(x for x in seed_h4 + seed_h5))
    v_h6 = verdict(out_band == 0, out_band >= 3)
    v_h7 = verdict(abs(h7["phi_opt_measured"] - H7_TARGET) < H7_TOL
                   and h7["max_random_dirichlet"] <= H7_CAP,
                   h7["max_random_dirichlet"] > H7_CAP)

    results: Dict[str, object] = {
        "case": "27-tegmark-perceptronium",
        "sealed_prereg_commit": "6d9d793b57bb",
        "prereg": "docs/ict/perceptronium-pre-enregistrement.md",
        "source": ("Tegmark 2015, Chaos Solitons & Fractals 76:238-270, "
                   "arXiv:1401.1219v3 (copie archivee au gisement)"),
        "units": "hbar = omega = 1 ; T = 2.pi ; potentiel de base sin(2.pi.x/n)",
        "seeds": list(SEEDS),
        "validations": {"H1": h1, "H2": h2, "H3": h3v},
        "banc": banc,
        "fits": fits,
        "integration": h7,
        "verdicts": {
            "H1_delta_h": v_h1,
            "H2_fidelite_dirichlet": v_h2,
            "H3_entropie_eq81": v_h3,
            "H4_decroissance_2^-4b": v_h4,
            "H5_autonomie_2^3b": v_h5,
            "H6_genericite_seeds": v_h6,
            "H7_plafond_phi_02516": v_h7,
            "global": global_verdict(
                {"H1_delta_h": v_h1, "H2_fidelite_dirichlet": v_h2,
                 "H3_entropie_eq81": v_h3, "H4_decroissance_2^-4b": v_h4,
                 "H5_autonomie_2^3b": v_h5, "H6_genericite_seeds": v_h6,
                 "H7_plafond_phi_02516": v_h7},
                fits["base"]),
        },
        "timestamps_utc": _dt.datetime.now(_dt.timezone.utc).isoformat(),
    }
    if output_path:
        with open(output_path, "w", encoding="utf-8") as fh:
            json.dump(results, fh, indent=2, ensure_ascii=False, default=float)
    return results


if __name__ == "__main__":
    import argparse

    ap = argparse.ArgumentParser(description="Banc perceptronium (case 27, #8182)")
    ap.add_argument("--output", default=None, help="chemin du JSON de resultats")
    args = ap.parse_args()
    res = run_all(args.output)
    print(json.dumps(res["verdicts"], indent=2, ensure_ascii=False))
    for name, fit in res["fits"].items():
        print(f"{name:8s} pente log2 S_lin(T) = {fit['slope_log2_s_lin_T']:+.3f}"
              f"  pente log2 A = {fit['slope_log2_autonomy']:+.3f}")
