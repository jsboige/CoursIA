"""Case 17 - STV : la valence comme fonction de la symetrie (iceberg #8182).

Execution du pre-enregistrement ``docs/ict/stv-valence-symmetry-pre-enregistrement.md``
(commits a6ad3c46 + amendements v2 1fae882d et v3 40941ed6, PR #17164),
scelle AVANT ce banc -- l'anteriorite repose sur la relation de parente des
commits (lecon case 8c).

La these testee (lecture grade C de la Symmetry Theory of Valence,
Gomez-Emilsson/Johnson, QRI) : la valence d'une experience est fonction de la
**symetrie de son objet formel** -- invariance sous un groupe de
transformations, avec la dualite annoncee ``symmetry in space and synchrony in
time``. Le mecanisme source : l'annealing neuronal, les configurations
consonantes comme **meilleurs attracteurs** -- ``It's not the energy that
feels good. It is the end result, the attractor that it takes you to.``

Dissociation substrat : un indice dynamique de qualite d'attracteur suit-il
la **consonance harmonique** de la configuration de frequences,
**independamment de l'energie**, et distingue-t-il coherence harmonique vs
coherence non-harmonique a coherence brute appariee ?

Modele (amendements v2/v3 du pre-enregistrement, sections 6bis/6ter)
---------------------------------------------------------------------
K oscillateurs de phase a couplage global, **couplage a contenu harmonique
fixe non accorde** ``H(phi) = somme_{h=1..4} sin(h*phi)/h`` (le couplage sin
pur ne produit que des locks 1:1 ; defaut analytique v1, corrige avant toute
execution, bandes inchangees) :

    dtheta_i/dt = w_i + (K_c/N) * somme_j a_i*a_j*H(theta_j - theta_i)

Configurations : f0 fixe (220 Hz) x ratios — echelle continue de consonance.
Chaque configuration associe la fondamentale a une **permutation de
l'echelle octave** (2, 3, 4, 6, 8, 12, 16), chaque membre etant soit **exact**
(pole harmonique, prob u) soit **decale** de +-3 a 8 % en log (pole
inharmonique) — etallement de frequences APPARIE par construction entre les
deux poles : seule l'harmonicite varie, pas le detuning (amendement v3 — le
pole v2 « ratios uniformes dans [1, 2] » etait un quasi-unison qui collapse
en 1:1 a tout couplage, rendant P1 insatisfaisable par construction).

Observables :

* sigma (consonance, amendement v3) : **harmonicite octave-repliee** — pour
  chaque paire, rapport replie dans [1, 2) par octaves puis distance
  logarithmique CIRCULAIRE au p/q le plus proche avec p, q <= LOCK_MAX = 4
  (jeu {1, 4/3, 3/2}, aligne sur le contenu harmonique du couplage) ;
  ``sigma_pair = exp(-d/tau)`` avec tau = 0.03 gele. C'est la
  formalisation directe de la symetrie des rapports (le construct de la
  source) ; la forme v1 (p, q <= 16) etait degeneree par densite des
  rationnels, le jeu p, q <= 8 NON MONOTONE sur ce substrat (mesure
  pre-execution 0.878 / 0.843 / 0.886 sur decalages croissants, section
  6ter.4), la forme v2 (Sethares) mesurait la roughness de proximite —
  anti-correlee a la facilite d'entrainement sur ce substrat.
* v (valence-proxy, aveugle aux VALEURS des ratios, amendement v3) :
  fraction de paires verrouillees m:n — paire lock s'il existe (m, n) <= 4
  (aligne sur le contenu harmonique 1/h du couplage, non accorde) tel que
  ``m*theta_i - n*theta_j`` soit concentre (ecart-type circulaire <
  1.5 rad) sur la seconde moitie. La stationnarite v2 etait aussi celle des
  paires LIBRES. ``r(t)``, aveugle aux locks m:n, reste reserve au
  discriminateur P3.
* P3 : bras H (echelle octave complete) vs N (6 frequences proches + 2 a
  rapports irrationnels — coherence brute sans structure harmonique),
  phases initiales tirees de la meme loi => coherence initiale appariee par
  construction.

Predictions scellees (graines test (0, 1, 7, 42, 99), calibration gelee sur
(11, 22, 33), jamais relues) :

* P1 — attracteur ~ consonance : Spearman rho(v, sigma) >= 0.6, >= 4/5 graines ;
* P2 — dissociation energie : sous perturbation d'amplitudes +-10 %,
  |rho(v, E)| <= 0.2, >= 4/5 graines ;
* P3 — discriminateur jhana/crise : CV(r | N) / CV(r | H) >= 2.0 a
  coherence brute appariee, >= 4/5 graines ;
* Null (a) — sigma permute : |rho| <= 0.2 en mediane ;
* Null (b) — couplage fort (K_c x 8) : rho < 0.2 -> NON_CONCLUSIF_INSTRUMENT ;
* portes — r_bar(H) < 0.3 ou > 0.95 sur >= 3/5 graines ->
  NON_CONCLUSIF_INSTRUMENT ; controle mecanique K_c = 0 : phases libres,
  |w_hat - w| < 1e-6 (parade aux bugs d'integrateur).

References
----------
M. E. Johnson, « Principia Qualia » (2016) ; A. Gomez-Emilsson, « The
Symmetry Theory of Valence 2020 Overview » (qri.org) ; M. E. Johnson,
« Qualia Formalism and a Symmetry Theory of Valence » (2023).
Pre-enregistrement : ``docs/ict/stv-valence-symmetry-pre-enregistrement.md``
(case 17 de ``docs/ict/dissociations-matrix.md``).
"""

from __future__ import annotations

import argparse
import json
import os
from multiprocessing import Pool

import numpy as np

# --- Parametres du jouet (scelles, amendements v2/v3) ---
K = 8                          # oscillateurs
F0 = 220.0                     # fondamentale (Hz, informative seulement)
HARMONIC_LADDER = (1.0, 2.0, 3.0, 4.0, 6.0, 8.0, 12.0, 16.0)
COUPLING_HARMONICS = (1.0, 0.5, 0.25, 0.125)   # 1/h, h = 1..4, fixe non accorde
LOCK_MAX = 4         # candidats (m, n) <= 4 — aligne sur les harmoniques 1/h

# Harmonicite octave-repliee (amendement v3) : jeu de repliement p/q avec
# p, q <= LOCK_MAX — aligne sur les resonances que le couplage possede
# reellement (harmoniques 1/h, h <= 4). Un jeu Farey d'ordre superieur
# (p, q <= 8 : ecart minimal 0.014 en log) est plus dense que les decalages
# inharmoniques eux-memes (>= 0.03) et ne discrimine plus — la degenerescence
# v1 (p, q <= 16) reaparaissant a l'ordre 8, constatee en calibration.
FOLD_SET = np.array(sorted({p / q for p in range(1, LOCK_MAX + 1)
                            for q in range(1, LOCK_MAX + 1)
                            if 1.0 <= p / q < 2.0}), dtype=float)
LN_FOLD_SET = np.log(FOLD_SET)
TAU_HARM = 0.03        # echelle de decroissance de l'harmonicite (gele)
SHIFT_LO, SHIFT_HI = 0.03, 0.08   # amplitude ln des decalages inharmoniques
DISSIDENT_DIST = 0.04  # distance ln minimale au jeu de repliement (bras N)

# Constantes de mesure scellees par le pre-enregistrement.
SEEDS_TEST = (0, 1, 7, 42, 99)
SEEDS_CALIB = (11, 22, 33)
M_CONFIGS = 120      # configurations sur l'echelle de consonance par graine
M_PAIRS = 40         # paires H/N par graine
LOCK_TOL = 1.5       # ecart-type circulaire (rad) declarant le verrouillage
SLOPE_TOL = 0.03     # |dpsi/dt| (rad/unite) — la moitie du derive minimal
#                    # impose par SHIFT_LO sur le meilleur couple (m, n)

# Bandes scellees (P1/P2/P3, nulls, portes) — ne jamais recalibrer apres mesure.
BAND_P1 = 0.6          # rho(v, sigma) >=
BAND_P2 = 0.2          # |rho(v, E)| <=
BAND_P3 = 2.0          # CV_ratio >=
BAND_P3_FAIL = 1.2     # en dessous : discriminateur tombe (NOT_SUPPORTED)
BAND_P2_FAIL = 0.5     # au-dessus : l'energie porte tout (NOT_SUPPORTED)
GATE_RBAR = (0.3, 0.95)
GATE_MIN_SEEDS = 3

# Integration (RK4 vectorisee sur les configurations).
DT = 5.0e-4
T_TOTAL = 40.0
SUBSAMPLE = 10        # pas de stockage : DT * 10 = 5e-3 unites

# Calibration gelee (graines 11/22/33 via --calibrate, figee avant le run
# principal). Cible scellee : r_bar(H) dans [0.5, 0.8] ; repli declare :
# variance de v sur l'echelle maximale (sensibilite d'instrument, neutre en
# signe). La valeur ci-dessous est le produit gele de ce protocole.
#
# PRODUIT GELE, mesure du 2026-09-21 (jamais relu sur les graines de test) :
# k_coupling = 32.0 par la FENETRE SCELLEE (pas le repli) -- r_bar(H) median
# sur les trois graines de calibration = 0.6587, milieu de [0.5, 0.8].
# Grille balayee par --calibrate : 4, 8, 16, 24, 32, 48, 64, 96, 128 (seule
# la valeur retenue est consignee par l'outil ; une re-execution de
# --calibrate est deterministe). Les bornes de regime sont situees par la
# SONDE pre-execution section 6ter.1 du pre-enregistrement (graine 11,
# K_c = 8/16/32/48) : sous la fenetre a k_c <= 16 (r_bar(H) 0.319 / 0.332),
# collapse 1:1 des deux poles a k_c >= 48.
K_COUPLING = 32.0


# --- Consonance : harmonicite octave-repliee (amendement v3) ---

def sigma_config(ratios: np.ndarray) -> float:
    """Consonance d'une configuration : moyenne des harmonicites par paires.

    Chaque rapport de paire est replie dans [1, 2) par octaves, puis score
    ``exp(-d/tau)`` ou d = distance logarithmique circulaire au point de
    repliement p/q le plus proche (p, q <= LOCK_MAX = 4 — les resonances
    que le couplage possede ; un jeu plus dense ne discrimine pas les
    decalages). L'octave et l'unison sont maximalement harmoniques, un
    rapport 21:20 ne l'est pas — le construct « symetrie des rapports » de
    la source, pas la roughness de proximite (v2, ecartee).
    """
    r = np.asarray(ratios, dtype=float)
    i, j = np.triu_indices(len(r), k=1)
    pair = np.maximum(r[i], r[j]) / np.minimum(r[i], r[j])
    ln_pair = np.mod(np.log(pair), np.log(2.0))          # dans [0, ln 2)
    # Espace de repliement circulaire : 2.0 est identique a 1.0 (octave).
    raw = np.abs(ln_pair[:, None] - LN_FOLD_SET[None, :])
    d = np.min(np.minimum(raw, np.log(2.0) - raw), axis=1)
    return float(np.mean(np.exp(-d / TAU_HARM)))


# --- Generation des configurations (echelle de consonance + paires H/N) ---

def _inharmonic_shift(rng: np.random.Generator, base: float) -> float:
    """Decale un membre de l'echelle de +-SHIFT_LO..HI en log (pole v3)."""
    sign = -1.0 if rng.uniform() < 0.5 else 1.0
    return float(base * np.exp(sign * rng.uniform(SHIFT_LO, SHIFT_HI)))


def _dissident_ratio(rng: np.random.Generator) -> float:
    """Ratio uniforme dans [1, 2] a distance ln >= DISSIDENT_DIST du jeu
    octave-replie p/q, p,q <= 8 (bras N de P3)."""
    while True:
        r = rng.uniform(1.0, 2.0)
        if np.min(np.abs(np.log(r) - LN_FOLD_SET)) >= DISSIDENT_DIST:
            return r


def draw_configs(seed: int, m_configs: int, n_pairs: int = M_PAIRS) -> dict:
    """Tire l'echelle de consonance (+ paires H/N si n_pairs > 0).

    Pole harmonique : la permutation de l'echelle octave, membres exacts.
    Pole inharmonique : les MEMBRES de la meme permutation, decales
    +-3-8 % en log — etallement apparie par construction, seule
    l'harmonicite varie (amendement v3, section 6ter).
    """
    rng = np.random.default_rng(seed)
    ladder, phases0, amps = [], [], []
    for _ in range(m_configs):
        u = rng.uniform()                      # position sur l'echelle
        pool = list(HARMONIC_LADDER[1:])
        rng.shuffle(pool)
        ratios = [1.0]
        for base in pool:
            if rng.uniform() < u:
                ratios.append(base)
            else:
                ratios.append(_inharmonic_shift(rng, base))
        ladder.append(np.sort(np.array(ratios)))
        phases0.append(rng.uniform(0.0, 2.0 * np.pi, size=K))
        amps.append(np.ones(K))
    # Paires : H = echelle octave complete ; N = 6 proches + 2 irrationnels.
    pairs_h, pairs_n = [], []
    for _ in range(n_pairs):
        close = 1.0 + rng.uniform(-0.02, 0.02, size=K - 3)
        irr = np.array([_dissident_ratio(rng), _dissident_ratio(rng)])
        pairs_n.append(np.sort(np.concatenate([[1.0], close, irr])))
        pairs_h.append(np.array(HARMONIC_LADDER))
        for _ in range(2):
            phases0.append(rng.uniform(0.0, 2.0 * np.pi, size=K))
            amps.append(np.ones(K))
    ratios_all = np.array(ladder + pairs_h + pairs_n)
    return {"ratios": ratios_all,
            "phases0": np.array(phases0),
            "amps": np.array(amps),
            "n_ladder": m_configs, "n_pairs": n_pairs}


# --- Dynamique (RK4 vectorisee sur les configurations) ---

def _rhs(theta: np.ndarray, omega: np.ndarray, amps: np.ndarray,
         k_c: float) -> np.ndarray:
    """dtheta/dt : couplage global a contenu harmonique fixe 1/h."""
    d = theta[:, None, :] - theta[:, :, None]          # (n, i, j) = t_j - t_i
    hsum = np.zeros_like(d)
    for coeff in COUPLING_HARMONICS:
        h_i = int(round(1.0 / coeff))
        hsum += coeff * np.sin(h_i * d)
    aa = amps[:, :, None] * amps[:, None, :]
    coupling = (k_c / K) * (aa * hsum).sum(axis=2)
    return omega + coupling


def integrate(ratios: np.ndarray, phases0: np.ndarray, amps: np.ndarray,
              k_c: float, t_total: float = T_TOTAL,
              coupling_harmonics: tuple | None = None) -> np.ndarray:
    """Integre le champ de phases ; renvoie les phases sous-echantillonnees.

    Sortie shape (n_steps, n_configs, K), sous-echantillonnage SUBSAMPLE.
    ``coupling_harmonics`` ne sert qu'au test de la premisse de l'amendement
    v2 (couplage sin pur) — le protocole n'y touche jamais.
    """
    global COUPLING_HARMONICS  # noqa: PLW0603 — override test-only, restaure
    saved = COUPLING_HARMONICS
    if coupling_harmonics is not None:
        COUPLING_HARMONICS = tuple(coupling_harmonics)
    try:
        omega = 2.0 * np.pi * ratios
        theta = phases0.copy()
        n_steps = int(t_total / DT)
        out = [theta.copy()]
        for step in range(n_steps):
            k1 = _rhs(theta, omega, amps, k_c)
            k2 = _rhs(theta + 0.5 * DT * k1, omega, amps, k_c)
            k3 = _rhs(theta + 0.5 * DT * k2, omega, amps, k_c)
            k4 = _rhs(theta + DT * k3, omega, amps, k_c)
            theta = theta + (DT / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4)
            if (step + 1) % SUBSAMPLE == 0:
                out.append(theta.copy())
        return np.array(out)
    finally:
        COUPLING_HARMONICS = saved


# --- Observables ---

def _unwrap(phases: np.ndarray) -> np.ndarray:
    return np.unwrap(phases, axis=0)


def order_parameter(phases: np.ndarray) -> np.ndarray:
    """r(t) = |mean e^{i theta}| par configuration — aveugle aux locks m:n."""
    z = np.exp(1j * phases).mean(axis=-1)
    return np.abs(z)


def v_settling(phases_sub: np.ndarray) -> np.ndarray:
    """v = fraction de paires verrouillees m:n (amendement v3, section 6ter).

    Degenerescence v2 constatee en calibration (graine 11, jamais sur
    graines de test) : la stationnarite des rapports est satisfaite aussi
    par les paires LIBRES (omega_hat = omega constant). v3 detecte les
    verrouillages REELS : paire lock s'il existe (m, n) <= LOCK_MAX —
    aligne sur le contenu harmonique du couplage (1/h, h <= 4), non accorde
    — tel que la phase combinee m*theta_i - n*theta_j soit concentree
    (ecart-type circulaire < LOCK_TOL) sur la seconde moitie. Un lock 2:1
    compte exactement autant qu'un lock 3:2 — la VALEUR du ratio n'est
    jamais lue (pas de circularite avec sigma).
    """
    uw = _unwrap(phases_sub[phases_sub.shape[0] // 2::4])   # sous-ech. dense
    i, j = np.triu_indices(K, k=1)
    n_pairs_idx = len(i)
    locked = np.zeros((uw.shape[1], n_pairs_idx), dtype=bool)
    for a in range(1, LOCK_MAX + 1):
        for b in range(1, LOCK_MAX + 1):
            psi_raw = a * uw[:, :, i] - b * uw[:, :, j]
            # Critere 1 — concentration circulaire : la phase combinee est
            # piegee autour d'une valeur fixe.
            psi = psi_raw % (2.0 * np.pi)
            z = np.exp(1j * psi).mean(axis=0)               # (n_conf, n_pairs)
            r_bar_pair = np.abs(z)
            circ_std = np.sqrt(np.maximum(
                -2.0 * np.log(np.maximum(r_bar_pair, 1e-12)), 0.0))
            # Critere 2 — derive nulle : une derive lente (< 1 tour par
            # fenetre) echappe a la concentration seule ; les decalages
            # inharmoniques (>= 3 %) imposent |dpsi/dt| >= 2*SHIFT_LO sur le
            # meilleur couple, un verrouillage reel l'annule.
            diffs = np.diff(psi_raw, axis=0)
            slope = (diffs.mean(axis=0) / (DT * SUBSAMPLE * 4)
                     if diffs.size else np.full(psi_raw.shape[1:], np.inf))
            locked |= (circ_std < LOCK_TOL) & (np.abs(slope) < SLOPE_TOL)
    return locked.mean(axis=1)


def cv(x: np.ndarray) -> float:
    x = np.asarray(x, dtype=float)
    return float(np.std(x) / np.mean(x)) if np.mean(x) > 0 else float("nan")


def _spearman(a: np.ndarray, b: np.ndarray) -> float:
    ra = np.argsort(np.argsort(a)).astype(float)
    rb = np.argsort(np.argsort(b)).astype(float)
    if np.std(ra) == 0 or np.std(rb) == 0:
        return float("nan")
    return float(np.corrcoef(ra, rb)[0, 1])


# --- Protocol ---

def run_seed(seed: int, m_configs: int, k_c: float,
             perturb: np.ndarray | None = None, n_pairs: int = M_PAIRS,
             t_total: float = T_TOTAL) -> dict:
    """Tous les bras d'une graine (echelle + paires H/N + P2 si perturb)."""
    cfg = draw_configs(seed, m_configs, n_pairs=n_pairs)
    amps = cfg["amps"] if perturb is None else cfg["amps"] * perturb
    ph = integrate(cfg["ratios"], cfg["phases0"], amps, k_c, t_total=t_total)
    v = v_settling(ph)
    r = order_parameter(ph)
    r_bar = r[len(r) // 2:].mean(axis=0)
    r_cv = np.array([cv(rr) for rr in r[len(r) // 2:].T])
    sig = np.array([sigma_config(rr) for rr in cfg["ratios"]])
    e_tot = (amps ** 2).sum(axis=1)
    n, m = cfg["n_ladder"], cfg["n_pairs"]
    return {"v": v, "sigma": sig, "r_bar": r_bar, "r_cv": r_cv, "e": e_tot,
            "slice_ladder": slice(0, n), "slice_h": slice(n, n + m),
            "slice_n": slice(n + m, n + 2 * m), "ratios": cfg["ratios"]}


def _mechanical_control(seed: int) -> bool:
    """K_c = 0 : phases libres, w_hat doit reproduire w (tolerance 1e-6)."""
    rng = np.random.default_rng(seed)
    ratios = np.array([HARMONIC_LADDER,
                       np.concatenate([[1.0], rng.uniform(1.2, 1.9, K - 1)])])
    ph0 = rng.uniform(0.0, 2.0 * np.pi, size=(2, K))
    ph = integrate(ratios, ph0, np.ones((2, K)), 0.0, t_total=4.0)
    uw = _unwrap(ph)
    w_hat = np.gradient(uw, DT * SUBSAMPLE, axis=0)[len(uw) // 2:]
    return bool(np.max(np.abs(w_hat.mean(axis=0) - 2 * np.pi * ratios)) < 1e-6)


def _seed_result(job: tuple[int, float]) -> dict:
    """Bras complet d'une graine (worker parallelisable, deterministe)."""
    seed, k_c = job
    base = run_seed(seed, M_CONFIGS, k_c)
    pert = 1.0 + np.random.default_rng(seed + 1000).uniform(
        -0.1, 0.1, size=(base["v"].shape[0], K))
    perturbed = run_seed(seed, M_CONFIGS, k_c, perturb=pert)
    sl, sh, sn = base["slice_ladder"], base["slice_h"], base["slice_n"]
    # P3 : coherence initiale appariee par construction (memes tirages de
    # phases initiales) ; discriminateur = ratio des CV de r (medianes par
    # famille) — (CV|N)/(CV|H).
    return {
        "seed": seed,
        "rho1": float(_spearman(base["v"][sl], base["sigma"][sl])),
        "rho_e": float(_spearman(perturbed["v"][sl], perturbed["e"][sl])),
        "r_bar_h": float(np.median(base["r_bar"][sh])),
        "r_bar_n": float(np.median(base["r_bar"][sn])),
        "p3_ratio": float(np.median(base["r_cv"][sn])
                          / np.median(base["r_cv"][sh])),
        "ctrl_mechanical": _mechanical_control(seed),
        "v_ladder": base["v"][sl].tolist(),
        "sigma_ladder": base["sigma"][sl].tolist(),
    }


def _strong_result(k_c: float) -> float:
    """Null (b) : couplage fort (x8) — saturation de l'entrainement."""
    strong = run_seed(SEEDS_TEST[0], M_CONFIGS, k_c * 8.0)
    sl = strong["slice_ladder"]
    return abs(_spearman(strong["v"][sl], strong["sigma"][sl]))


def run_protocol(k_c: float = K_COUPLING, parallel: bool = True) -> dict:
    """Run principal : graines test, constantes gelees K_COUPLING.

    Les cinq graines sont independantes : elles s'executent en parallele
    (une par processus) et sont fusionnees dans l'ordre scelle — le
    resultat est identique au run sequentiel, graine par graine.
    """
    jobs = [(s, k_c) for s in SEEDS_TEST]
    if parallel and len(jobs) > 1 and (os.cpu_count() or 2) > 2:
        n_proc = max(1, min(len(jobs) + 1, (os.cpu_count() or 2) - 1))
        with Pool(n_proc) as pool:
            per_seed = pool.map(_seed_result, jobs)
            (null_b,) = pool.map(_strong_result, [k_c])
    else:
        per_seed = [_seed_result(j) for j in jobs]
        null_b = _strong_result(k_c)

    rho1s = [d["rho1"] for d in per_seed]
    rho_es = [d["rho_e"] for d in per_seed]
    p3s = [d["p3_ratio"] for d in per_seed]
    rb_h = [d["r_bar_h"] for d in per_seed]
    rb_n = [d["r_bar_n"] for d in per_seed]
    mech_ok = all(d["ctrl_mechanical"] for d in per_seed)

    # Null (a) : permutation des etiquettes sigma, graine 0 (bras reutilise).
    perm_rng = np.random.default_rng(0)
    v0 = np.array(per_seed[0]["v_ladder"])
    s0 = np.array(per_seed[0]["sigma_ladder"])
    null_a = float(np.median([
        abs(_spearman(v0, perm_rng.permutation(s0))) for _ in range(200)]))

    p1 = sum(r >= BAND_P1 for r in rho1s) >= 4
    p2 = sum(abs(r) <= BAND_P2 for r in rho_es) >= 4
    p3_ok = sum(p >= BAND_P3 for p in p3s) >= 4
    gate = (sum(rb < GATE_RBAR[0] or rb > GATE_RBAR[1] for rb in rb_h)
            >= GATE_MIN_SEEDS)

    if gate:
        verdict = "NON_CONCLUSIF_INSTRUMENT (porte plancher/plafond r_bar(H))"
    elif null_b < 0.2 and not p1:
        verdict = "NON_CONCLUSIF_INSTRUMENT (null b : saturation forte)"
    elif p1 and p2 and p3_ok and null_a <= 0.2 and mech_ok:
        verdict = "SUPPORTED"
    elif (not p1) or any(abs(r) > BAND_P2_FAIL for r in rho_es) \
            or all(p < BAND_P3_FAIL for p in p3s):
        verdict = "NOT_SUPPORTED"
    else:
        verdict = "NON_CONCLUSIF"

    return {
        "case": "17-stv-valence-as-symmetry",
        "k_coupling": k_c,
        "seeds": list(SEEDS_TEST), "m_configs": M_CONFIGS,
        "per_seed": per_seed,
        "rho1_by_seed": rho1s, "rho_e_by_seed": rho_es,
        "p3_by_seed": p3s, "r_bar_h_by_seed": rb_h,
        "r_bar_n_by_seed": rb_n,
        "null_a_median_abs_rho": null_a, "null_b_abs_rho": null_b,
        "p1": bool(p1), "p2": bool(p2), "p3": bool(p3_ok),
        "ctrl_mechanical_ok": mech_ok,
        "verdict": verdict,
        "bands": {"p1_min": BAND_P1, "p2_max": BAND_P2, "p2_fail": BAND_P2_FAIL,
                  "p3_min": BAND_P3, "p3_fail": BAND_P3_FAIL},
    }


def calibrate() -> dict:
    """Calibration sur graines disjointes (11/22/33) : gel de K_c.

    Cible scellee : r_bar(H) dans [0.5, 0.8]. Repli declare si la fenetre
    est inatteignable : K_c a **variance de v maximale** sur l'echelle —
    sensibilite d'instrument, neutre en signe.
    """
    grid = [4.0, 8.0, 16.0, 24.0, 32.0, 48.0, 64.0, 96.0, 128.0]
    best_window, best_var = None, None
    for k_c in grid:
        rbs, vvars = [], []
        for s in SEEDS_CALIB:
            d = run_seed(s, 24, k_c, n_pairs=6)
            rbs.append(float(np.median(d["r_bar"][d["slice_h"]])))
            vvars.append(float(np.var(d["v"][d["slice_ladder"]])))
        med = float(np.median(rbs))
        if 0.5 <= med <= 0.8 and (best_window is None
                                  or abs(med - 0.65) < best_window[0]):
            best_window = (abs(med - 0.65), k_c, med)
        if best_var is None or float(np.mean(vvars)) > best_var[0]:
            best_var = (float(np.mean(vvars)), k_c, med)
    if best_window is not None:
        return {"k_coupling": best_window[1], "source": "fenetre r_bar scellee",
                "r_bar_h_median": best_window[2], "v_variance": None}
    return {"k_coupling": best_var[1], "source": "repli variance v (declare)",
            "r_bar_h_median": best_var[2], "v_variance": best_var[0]}


def main() -> None:
    ap = argparse.ArgumentParser(description="Case 17 - STV valence as symmetry")
    ap.add_argument("--calibrate", action="store_true",
                    help="calibration sur graines disjointes (11/22/33)")
    ap.add_argument("--json", action="store_true", help="sortie JSON")
    args = ap.parse_args()
    out = calibrate() if args.calibrate else run_protocol()
    if args.json:
        print(json.dumps(out, indent=2, ensure_ascii=False))
    else:
        for key, val in out.items():
            print(f"{key}: {val}")


if __name__ == "__main__":
    main()
