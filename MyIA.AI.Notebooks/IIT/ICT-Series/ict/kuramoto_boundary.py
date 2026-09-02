"""Kuramoto 2D — frontière topologique vs frontière fonctionnelle (case 6, #8182).

Contexte
--------
Case 6 de ``docs/ict/dissociations-matrix.md`` (pré-enregistrement PR #12170,
c.429) : la dissociation **« frontière topologique ⟂ frontière fonctionnelle »**
(boundary problem — Gómez-Emilsson & Percy 2023, lecture ICT grade C) est
pré-enregistrée sur un substrat de phase 2D **CPU-only**. Ce module est le
**chantier 6/3 = exécution** : il implémente le protocole verrouillé AVANT
test et rend un verdict honnête multi-niveau (CONFIRMED / INCONCLUSIF /
FALSIFIED), sans retouche post-hoc. Première case non-LLM de la vague —
la forme canonique ``R_X = propa(X)/propa(comparateur)`` des cases 3-5 est
réemployée sur un instrument différent (cohérence de phase, pas top-k SAE).

Prédiction pré-enregistrée (mesure primaire)
--------------------------------------------
Grille 64×64, couplage Kuramoto aux voisins les plus proches (von Neumann,
bords ouverts), K = 1.0, dt = 0.05, intégration RK4. Profil de fréquences
bimodal verrouillé par graine : région A (28 rangées hautes) ω ~ N(+0.5, 0.3),
bande centrale (8 rangées) ω ~ N(0, 0.3), région B (28 rangées basses)
ω ~ N(−0.5, 0.3).

- Config ``TOPO`` : conditions initiales = champ lisse (par graine) + 4 paires
  vortex-antivortex épinglées dans la bande (winding imposé). Config ``CTRL`` :
  le même champ lisse, sans défauts — contre-factuel exact, seule la
  topologie diffère.
- Kick δφ = 0.5 rad sur disque r = 5 au centre de A après relaxation 500 pas.
- ``C(nœud) = |⟨e^{i(φ_nœud − φ_kick)}⟩|`` sur fenêtre 50 pas autour de
  t₀+200, référence = moyenne circulaire du disque kick ; seuil 0.8.
- ``propa(within)`` = fraction des nœuds de A (hors disque kick) cohérents ;
  ``propa(cross)`` = fraction dans B ; ``R_cross = propa(cross)/propa(within)``.

Cible : ``R_cross(TOPO) ∈ [0.25, 0.75]`` ET ``Δtopo = R_cross(CTRL) −
R_cross(TOPO) ≥ 0.10``. Nulls adversariaux : pocket fermé (``R_cross(TOPO) <
0.10``) ; topologie inerte (``Δtopo < ε_topo``, ``ε_topo = 0.5·σ_Δ`` calibré
sur paires jumelles sans défauts, AVANT le test principal — anti-HARKing).

Validité : nombre de défauts stable à ±1 sur [t₀, t₀+200], sinon graine
rejetée (``INCONCLUSIF protocole``, jamais re-tirée).

Mesure secondaire (disruption) : reset des cœurs de défaut (disques r = 3
remis à la moyenne circulaire de leur anneau) à t₁, re-relaxation, nouveau
kick ; ``R_cross(post) ≥ R_cross(TOPO) + 0.10`` → travail de frontière causal.

Lecture grade C (discipline) : vortex de phase ≠ boucles de flux EM ;
l'analogie est de rôle, pas d'identité physique ; aucune phénoménologie
n'est mesurée ni revendiquée (détail dans la matrice, case 6).

numpy seul, CPU, déterministe par graine.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any, Dict, List, Tuple

import numpy as np

# --- Paramètres verrouillés par le pré-enregistrement (ne pas retoucher) ----- #

N = 64                 # grille N×N
K_COUPLING = 1.0       # couplage aux voisins les plus proches
DT = 0.05              # pas d'intégration (RK4)
RELAX_STEPS = 500      # relaxation avant kick
HORIZON = 200          # mesure à t₀ + 200 pas
WINDOW = 50            # fenêtre de moyennage de la cohérence
KICK_DPHI = 0.5        # amplitude du kick (rad)
KICK_RADIUS = 5.0      # rayon du disque kick
COHERENCE_THRESH = 0.8 # seuil de cohérence
BAND_ROWS = (28, 36)   # bande centrale : rangées [28, 36)
RESET_RADIUS = 3.0     # disque de reset des cœurs (disruption)
RESET_RING = 5.0       # anneau de référence pour la valeur de reset
SEEDS = (0, 1, 7, 42, 99)
N_BOOTSTRAP = 200
TWO_PI = 2.0 * math.pi

# 4 paires vortex-antivortex dans la bande, cœurs aux centres de plaquettes
# (positions demi-entières → charge concentrée sur une seule plaquette).
PAIR_GEOMETRY: List[Tuple[Tuple[float, float], Tuple[float, float]]] = [
    ((29.5, 6.0), (34.5, 14.0)),
    ((29.5, 22.0), (34.5, 30.0)),
    ((29.5, 38.0), (34.5, 46.0)),
    ((29.5, 54.0), (34.5, 62.0)),
]

KICK_CENTER = (14.0, 32.0)  # centre de la région A


def wrap(angle: np.ndarray | float) -> np.ndarray | float:
    """Ramène une différence de phase dans (−π, π]."""
    return (angle + math.pi) % TWO_PI - math.pi


def region_masks() -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Masques (A, bande, B) — A en haut, B en bas."""
    a = np.zeros((N, N), dtype=bool); a[: BAND_ROWS[0], :] = True
    band = np.zeros((N, N), dtype=bool); band[BAND_ROWS[0]: BAND_ROWS[1], :] = True
    b = np.zeros((N, N), dtype=bool); b[BAND_ROWS[1]:, :] = True
    return a, band, b


def disc_mask(center: Tuple[float, float], radius: float) -> np.ndarray:
    r2 = (np.arange(N)[:, None] - center[0]) ** 2 + (np.arange(N)[None, :] - center[1]) ** 2
    return r2 <= radius * radius


def make_frequency_profile(rng: np.random.Generator) -> np.ndarray:
    """Profil bimodal verrouillé par graine (A +0.5, bande 0, B −0.5)."""
    omega = rng.normal(0.5, 0.3, (N, N))
    omega[BAND_ROWS[0]: BAND_ROWS[1], :] = rng.normal(0.0, 0.3, (BAND_ROWS[1] - BAND_ROWS[0], N))
    omega[BAND_ROWS[1]:, :] = rng.normal(-0.5, 0.3, (N - BAND_ROWS[1], N))
    return omega


def make_smooth_ic(rng: np.random.Generator) -> np.ndarray:
    """Champ lisse aléatoire sans défaut (winding = 0 vérifié par construction).

    Modes |k| ≤ 3, amplitude 0.5 rad : gradient par arête ≪ π, aucun winding.
    """
    noise = rng.standard_normal((N, N))
    kx = np.fft.fftfreq(N)[:, None] * N
    ky = np.fft.fftfreq(N)[None, :] * N
    lowpass = (kx ** 2 + ky ** 2) <= 9.0
    field = np.fft.ifft2(np.fft.fft2(noise) * lowpass).real
    field /= max(np.abs(field).max(), 1e-12)
    return 0.5 * field


def defect_field() -> np.ndarray:
    """Superposition des 4 paires vortex-antivortex (winding ±2π par cœur)."""
    rows = np.arange(N)[:, None]
    cols = np.arange(N)[None, :]
    field = np.zeros((N, N))
    for (vr, vc), (ar, ac) in PAIR_GEOMETRY:
        field += np.arctan2(cols - vc, rows - vr)
        field -= np.arctan2(cols - ac, rows - ar)
    return field


def dphi(phi: np.ndarray, omega: np.ndarray) -> np.ndarray:
    """dφ/dt = ω + K·Σ_voisins sin(φ_voisin − φ) — bords ouverts (padding bord)."""
    p = np.pad(phi, 1, mode="edge")
    neighbors = (
        np.sin(p[:-2, 1:-1] - phi)
        + np.sin(p[2:, 1:-1] - phi)
        + np.sin(p[1:-1, :-2] - phi)
        + np.sin(p[1:-1, 2:] - phi)
    )
    return omega + K_COUPLING * neighbors


def rk4_step(phi: np.ndarray, omega: np.ndarray) -> np.ndarray:
    k1 = dphi(phi, omega)
    k2 = dphi(phi + 0.5 * DT * k1, omega)
    k3 = dphi(phi + 0.5 * DT * k2, omega)
    k4 = dphi(phi + DT * k3, omega)
    return phi + (DT / 6.0) * (k1 + 2.0 * k2 + 2.0 * k3 + k4)


def plaquette_charges(phi: np.ndarray) -> np.ndarray:
    """Charge topologique par plaquette (winding entier sur la maille 1×1).

    Circulation sur la boucle (i,j)→(i+1,j)→(i+1,j+1)→(i,j+1)→(i,j) :
    ``up[i,j] + right[i+1,j] − up[i,j+1] − right[i,j]`` avec up = différence
    verticale wrapée, right = différence horizontale wrapée.
    """
    up = wrap(phi[1:, :] - phi[:-1, :])       # (N-1, N)
    right = wrap(phi[:, 1:] - phi[:, :-1])    # (N, N-1)
    circulation = up[:, :-1] + right[1:, :] - up[:, 1:] - right[:-1, :]
    charges = np.zeros((N - 1, N - 1))
    nonzero = np.abs(circulation) > math.pi  # |winding| >= 1 sûr ; sinon 0
    charges[nonzero] = np.round(circulation[nonzero] / TWO_PI)
    return charges


def detect_defects(phi: np.ndarray) -> List[Tuple[float, float, int]]:
    """Défauts = clusters de plaquettes chargées (8-connexité, même signe).

    Retourne (row, col, charge) par cœur — positions aux centres de plaquette
    (coordonnées demi-entières en nœuds).
    """
    charges = plaquette_charges(phi)
    seen = np.zeros_like(charges, dtype=bool)
    defects: List[Tuple[float, float, int]] = []
    for i in range(N - 1):
        for j in range(N - 1):
            if seen[i, j] or charges[i, j] == 0:
                continue
            sign = int(np.sign(charges[i, j]))
            total = 0
            count = 0
            stack = [(i, j)]
            seen[i, j] = True
            rows_acc, cols_acc = [], []
            while stack:
                ci, cj = stack.pop()
                total += int(charges[ci, cj])
                count += 1
                rows_acc.append(ci)
                cols_acc.append(cj)
                for di in (-1, 0, 1):
                    for dj in (-1, 0, 1):
                        ni, nj = ci + di, cj + dj
                        if (
                            0 <= ni < N - 1
                            and 0 <= nj < N - 1
                            and not seen[ni, nj]
                            and charges[ni, nj] != 0
                            and int(np.sign(charges[ni, nj])) == sign
                        ):
                            seen[ni, nj] = True
                            stack.append((ni, nj))
            defects.append((
                float(np.mean(rows_acc)) + 0.5,
                float(np.mean(cols_acc)) + 0.5,
                int(round(total / count)) * sign,
            ))
    return defects


def circular_mean(angles: np.ndarray) -> float:
    return float(np.angle(np.exp(1j * angles).mean()))


def relax_kick_measure(
    phi_start: np.ndarray, omega: np.ndarray, record_defects_at: Tuple[int, ...] = ()
) -> Dict[str, Any]:
    """Relaxation 500 → kick → fenêtre de mesure [t₀+176, t₀+225].

    Retourne propa/R_cross/défauts et l'état final à t₁ (pour brancher la
    disruption dessus). ``record_defects_at`` compte les défauts aux pas
    demandés après kick (contrôle de stabilité).
    """
    mask_a, _, mask_b = region_masks()
    kick_disc = disc_mask(KICK_CENTER, KICK_RADIUS)
    phi = phi_start.copy()

    for _ in range(RELAX_STEPS):
        phi = rk4_step(phi, omega)
    defects_t0 = len(detect_defects(phi))
    defects_at: Dict[int, int] = {0: defects_t0}

    phi[kick_disc] += KICK_DPHI  # t₀

    w_start = HORIZON - WINDOW // 2 + 1      # t₀+176
    w_end = HORIZON + WINDOW // 2            # t₀+225
    window_phases: List[np.ndarray] = []
    window_refs: List[float] = []
    for step in range(1, w_end + 1):
        phi = rk4_step(phi, omega)
        if step in record_defects_at:
            defects_at[step] = len(detect_defects(phi))
        if step >= w_start:
            window_phases.append(phi.copy())
            window_refs.append(circular_mean(phi[kick_disc]))

    phases = np.stack(window_phases)                       # (50, N, N)
    refs = np.exp(1j * np.array(window_refs))[:, None, None]
    coherence = np.abs((np.exp(1j * phases) / refs).mean(axis=0))

    within_nodes = mask_a & ~kick_disc
    propa_within = float((coherence[within_nodes] > COHERENCE_THRESH).mean())
    propa_cross = float((coherence[mask_b] > COHERENCE_THRESH).mean())

    return {
        "propa_within": propa_within,
        "propa_cross": propa_cross,
        "r_cross": propa_cross / propa_within if propa_within > 0 else float("nan"),
        "defects_t0": defects_t0,
        "defects_at": {str(k): v for k, v in defects_at.items()},
        "_phi_t1": phi.copy(),
    }


def disrupt_cores(phi: np.ndarray) -> Tuple[np.ndarray, int]:
    """Reset des cœurs de défaut : disque r=3 ← moyenne circulaire de l'anneau."""
    reset = phi.copy()
    defects = detect_defects(phi)
    for dr, dc, _charge in defects:
        r2 = (np.arange(N)[:, None] - dr) ** 2 + (np.arange(N)[None, :] - dc) ** 2
        core = r2 <= RESET_RADIUS ** 2
        ring = (r2 > RESET_RADIUS ** 2) & (r2 <= RESET_RING ** 2)
        if ring.any():
            reset[core] = circular_mean(phi[ring])
    return reset, len(defects)


def bootstrap_ic95(values: List[float]) -> Tuple[float, float]:
    """IC95 bootstrap (n=200) sur la médiane d'un échantillon de graines."""
    if not values:
        return float("nan"), float("nan")
    rng = np.random.default_rng(0)
    arr = np.array(values)
    medians = [
        float(np.median(arr[rng.integers(0, len(arr), len(arr))])) for _ in range(N_BOOTSTRAP)
    ]
    return float(np.percentile(medians, 2.5)), float(np.percentile(medians, 97.5))


def run_protocol() -> Dict[str, Any]:
    """Phase A (calibration null) PUIS phase B (test principal) — ordre anti-HARKing."""
    # --- Phase A : paires jumelles sans défauts (σ_Δ, ε_topo) — AVANT test --- #
    twin_diffs: List[float] = []
    twin_detail: List[Dict[str, Any]] = []
    per_seed_states: Dict[int, Dict[str, Any]] = {}
    for seed in SEEDS:
        rng = np.random.default_rng(seed)
        omega = make_frequency_profile(rng)
        smooth_1 = make_smooth_ic(np.random.default_rng([seed, 1]))
        smooth_2 = make_smooth_ic(np.random.default_rng([seed, 2]))
        run_1 = relax_kick_measure(smooth_1, omega)
        run_2 = relax_kick_measure(smooth_2, omega)
        d = run_1["r_cross"] - run_2["r_cross"]
        twin_diffs.append(d)
        twin_detail.append(
            {"seed": seed, "twin_1": run_1["r_cross"], "twin_2": run_2["r_cross"], "diff": d}
        )
        per_seed_states[seed] = {"omega": omega, "smooth_1": smooth_1, "run_1": run_1}

    sigma_delta = float(np.std(twin_diffs, ddof=1))
    eps_topo = 0.5 * sigma_delta

    # --- Phase B : test principal (TOPO vs CTRL) + disruption --- #
    seeds_out: List[Dict[str, Any]] = []
    for seed in SEEDS:
        state = per_seed_states[seed]
        omega, smooth = state["omega"], state["smooth_1"]
        ctrl = state["run_1"]  # CTRL = champ lisse seul (même run que jumeau 1)
        topo = relax_kick_measure(
            (smooth + defect_field()) % TWO_PI, omega, record_defects_at=(100, 200)
        )

        n_t0 = topo["defects_t0"]
        n_t200 = topo["defects_at"].get("200", n_t0)
        valid = abs(n_t200 - n_t0) <= 1

        # Disruption : reset des cœurs à t₁, re-relaxation, re-kick, re-mesure.
        reset_phi, defects_reset = disrupt_cores(topo["_phi_t1"])
        post = relax_kick_measure(reset_phi, omega)

        delta = ctrl["r_cross"] - topo["r_cross"] if valid else float("nan")
        seeds_out.append({
            "seed": seed,
            "defects_t0": n_t0,
            "defects_t200": n_t200,
            "valid": valid,
            "r_cross_topo": topo["r_cross"],
            "propa_within_topo": topo["propa_within"],
            "propa_cross_topo": topo["propa_cross"],
            "r_cross_ctrl": ctrl["r_cross"],
            "propa_within_ctrl": ctrl["propa_within"],
            "propa_cross_ctrl": ctrl["propa_cross"],
            "delta_topo": delta,
            "disruption": {
                "defects_reset": defects_reset,
                "defects_post_relax": post["defects_t0"],
                "r_cross_post": post["r_cross"],
            },
        })

    # --- Scoreboard + verdict multi-niveau (verrouillé avant test) --- #
    valid_seeds = [s for s in seeds_out if s["valid"]]
    rejected = len(seeds_out) - len(valid_seeds)
    r_topo = [s["r_cross_topo"] for s in valid_seeds]
    r_ctrl = [s["r_cross_ctrl"] for s in valid_seeds]
    deltas = [s["delta_topo"] for s in valid_seeds]
    r_post = [s["disruption"]["r_cross_post"] for s in valid_seeds]

    med_topo = float(np.median(r_topo)) if r_topo else float("nan")
    med_ctrl = float(np.median(r_ctrl)) if r_ctrl else float("nan")
    med_delta = float(np.median(deltas)) if deltas else float("nan")
    med_post = float(np.median(r_post)) if r_post else float("nan")

    n_inert = sum(1 for d in deltas if d < eps_topo) if deltas else 0

    if rejected >= 2:
        verdict = "INCONCLUSIF (>= 2 graines rejetees — vortex instables)"
    elif med_topo < 0.10:
        verdict = "FALSIFIED (pocket ferme : median R_cross(TOPO) < 0.10)"
    elif n_inert >= 3:
        verdict = "FALSIFIED (topologie inerte : delta_topo < eps_topo sur >= 3 graines)"
    elif med_topo >= 0.25 and med_topo <= 0.75 and med_delta >= 0.10 and rejected == 0 and n_inert == 0:
        verdict = "CONFIRMED (bande + delta_topo >= 0.10, 5/5 graines valides)"
    else:
        verdict = "INCONCLUSIF (l'instrument ne separe pas topologie et gradient a cette echelle)"

    borderline = bool(
        not math.isnan(med_topo)
        and (abs(med_topo - 0.25) <= 0.05 or abs(med_topo - 0.75) <= 0.05 or abs(med_delta - 0.10) <= 0.05)
    )

    if not (math.isnan(med_post) or math.isnan(med_topo)):
        if med_post >= med_topo + 0.10:
            disruption_verdict = "CAUSAL (frontiere ouverte par la disruption)"
        elif abs(med_post - med_topo) < eps_topo:
            disruption_verdict = "EPIPHENOMENE (delta < eps_topo — lecture causale retiree)"
        else:
            disruption_verdict = "NON CONCLUANT (entre les deux seuils)"
    else:
        disruption_verdict = "NON MESURABLE"

    return {
        "protocol": {
            "grid": N, "K": K_COUPLING, "dt": DT, "relax_steps": RELAX_STEPS,
            "horizon": HORIZON, "window": WINDOW, "kick_dphi": KICK_DPHI,
            "kick_radius": KICK_RADIUS, "coherence_thresh": COHERENCE_THRESH,
            "band_rows": list(BAND_ROWS), "seeds": list(SEEDS),
            "pairs": len(PAIR_GEOMETRY), "numpy_only_cpu": True,
        },
        "calibration_null": {
            "twin_detail": twin_detail,
            "sigma_delta": sigma_delta,
            "eps_topo": eps_topo,
            "note": "executée AVANT le test principal (anti-HARKing)",
        },
        "per_seed": seeds_out,
        "scoreboard": {
            "median_r_cross_topo": med_topo,
            "median_r_cross_ctrl": med_ctrl,
            "median_delta_topo": med_delta,
            "median_r_cross_post_disruption": med_post,
            "ic95_topo": bootstrap_ic95(r_topo),
            "ic95_ctrl": bootstrap_ic95(r_ctrl),
            "ic95_delta": bootstrap_ic95(deltas),
            "ic95_post": bootstrap_ic95(r_post),
            "seeds_valid": len(valid_seeds),
            "seeds_rejected": rejected,
            "n_delta_below_eps": n_inert,
            "verdict": verdict,
            "borderline_prudence_pm_0_05": borderline,
            "disruption_verdict": disruption_verdict,
        },
    }


def main() -> None:
    results = run_protocol()
    out = Path(__file__).parent / "results" / "kuramoto_boundary_results.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(results, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    sb = results["scoreboard"]
    cal = results["calibration_null"]
    print("=== Case 6 — frontiere topologique vs frontiere fonctionnelle (Kuramoto 2D) ===")
    print(f"Calibration null (avant test) : sigma_delta = {cal['sigma_delta']:.4f}, eps_topo = {cal['eps_topo']:.4f}")
    for s in results["per_seed"]:
        print(
            f"  seed {s['seed']:>2} | defects {s['defects_t0']}->{s['defects_t200']} valid={s['valid']} | "
            f"R_topo={s['r_cross_topo']:.3f} R_ctrl={s['r_cross_ctrl']:.3f} delta={s['delta_topo']:+.3f} | "
            f"R_post={s['disruption']['r_cross_post']:.3f}"
        )
    print(
        f"median R_topo={sb['median_r_cross_topo']:.3f} [{sb['ic95_topo'][0]:.3f},{sb['ic95_topo'][1]:.3f}] "
        f"R_ctrl={sb['median_r_cross_ctrl']:.3f} delta={sb['median_delta_topo']:+.3f} "
        f"R_post={sb['median_r_cross_post_disruption']:.3f}"
    )
    print(f"VERDICT: {sb['verdict']}")
    print(f"Disruption: {sb['disruption_verdict']}")
    if sb["borderline_prudence_pm_0_05"]:
        print("ATTENTION bande de prudence +/-0.05 atteinte — verdict a la marge.")
    print(f"Resultats: {out}")


if __name__ == "__main__":
    main()
