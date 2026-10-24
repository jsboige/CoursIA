"""Case 17bis - STV v2 : seconde operationnalisation, structure du lock (iceberg #8182).

Execution du pre-enregistrement
``docs/ict/stv-valence-symmetry-v2-pre-enregistrement.md`` (scelle AVANT ce
banc -- l'anteriorite repose sur la relation de parente des commits, lecon
case 8c). Le banc v1 (``stv_valence_symmetry.py``, case 17, verdict
``NON_CONCLUSIF_INSTRUMENT``) est CONSERVE tel quel -- jamais reecrit : ce
module est l'instrument n.o 2 du meme claim, pattern case 6 -> case 14.

Les deux correctifs scelles (limite mesuree v1 -> correctif v2) :

1. P3 lisait ``CV(r)`` : la coherence brute du bras N (collapse 1:1 parfait,
   CV ~ 1e-15) y est MINIMALE -- l'observable etait aveugle au contraste
   qu'elle visait. v2 : score de structure ``S`` = entropie normalisee (ln 6)
   de la distribution des classes de ratio des paires verrouillees (6 classes
   : 1:1, 4:3, 3:2, 2:1, 3:1, 4:1). Le bras H (echelle octave) est
   structurellement riche, le bras N (quasi-unisson + irrationnels)
   trivialement uniforme.
2. La perturbation d'energie v1 passait par l'heterogeneite d'amplitude
   (``a_i * a_j`` par paire) : le drive decidait du verrouillage. v2 :
   amplitudes unitaires partout, energie = drive global uniforme
   ``K_eff = K2_c * (1 + eps)``, ``eps in {-0.1, 0, +0.1}``, applique a la
   seule echelle (les bras H/N restent au point nominal).

Mecanique heritee du banc v1 par import, jamais dupliquee : tirage des
configurations, detecteur m:n (concentration circulaire + derive nulle),
sigma octave-repliee, graines, constantes d'integration. Nouvelle fenetre de
calibration : ``v_bar(u = 1) in [0.5, 0.8]`` -- la lecture de l'instrument
lui-meme, plus le ``r_bar`` aveugle aux locks m:n de la fenetre v1.

Predictions scellees (graines test (0, 1, 7, 42, 99), calibration gelee sur
(11, 22, 33), jamais relues) :

* P1 attracteur ~ consonance (inchangee) : rho(v, sigma) >= 0.6, >= 4/5 ;
* P2bis dissociation drive : |rho(v, eps | decile de sigma)| <= 0.2, >= 4/5 ;
* P3bis discriminateur structure : dS = S(H) - S(N) >= 0.25 a coherence
  brute appariee (porte |r_bar(H) - r_bar(N)| <= 0.15), >= 4/5 ;
* Null (a) sigma permute ; Null (a3) etiquettes H/N permutees ; Null (b)
  couplage fort x8 sature -> NON_CONCLUSIF_INSTRUMENT ;
* portes instrumentales v_bar(u=1) >= 0.3, v_bar(u=0) <= 0.7 ;
* controle mecanique K_eff=0 sur irrationnelles : v <= 0.05 ; la
  commensurabilite cinematique des membres exacts y est un plafond DECLARE
  (mesure en diagnostic, pas une porte).

References : celles du scelle v1 (Johnson 2016 ; Gomez-Emilsson 2020 ;
Johnson 2023). Pre-enregistrement :
``docs/ict/stv-valence-symmetry-v2-pre-enregistrement.md``.
"""

from __future__ import annotations

import argparse
import json
import os
from multiprocessing import Pool

import numpy as np

from ict import stv_valence_symmetry as v1
from ict.stv_valence_symmetry import (
    DT,
    K,
    LOCK_MAX,
    LOCK_TOL,
    M_CONFIGS,
    M_PAIRS,
    SEEDS_CALIB,
    SEEDS_TEST,
    SLOPE_TOL,
    SUBSAMPLE,
    T_TOTAL,
    _spearman,
    _unwrap,
    draw_configs,
    integrate,
    order_parameter,
    sigma_config,
)

# K2_c nominal : GELE par --calibrate (graines 11/22/33) — fenetre scellee
# v(u=1) in [0.5, 0.8], mediane mesuree 0.75 a K=48 (seul point de grille
# dans la fenetre ; trace : ict/results/stv_valence_symmetry_v2_calibration.json).
K2_COUPLING = 48.0

# --- Bandes scellees case 17bis (jamais recalculees apres mesure) ---
BAND_P1 = 0.6            # rho(v, sigma) >=
BAND_P1_FAIL = 0.2       # en deca : indifference au regime propre (NOT_SUPPORTED)
BAND_P2 = 0.2            # |rho(v, eps | decile sigma)| <=
BAND_P2_FAIL = 0.5       # au-dela : le drive porte tout (NOT_SUPPORTED)
BAND_P3 = 0.25           # dS = S(H) - S(N) >=
BAND_P3_FAIL = 0.10      # en deca : structure indiscernable (NOT_SUPPORTED)
GATE_V_U1 = 0.3          # plancher v_bar(u=1)
GATE_V_U0 = 0.7          # plafond v_bar(u=0)
GATE_MATCH_RB = 0.15     # porte d'appariement |r_bar(H) - r_bar(N)| <=
GATE_MIN_SEEDS = 3
CTRL_V0_MAX = 0.05       # controle mecanique, configs irrationnelles
NULL_B_SCALE = 8.0       # couplage fort x K2_c
EPS_GRID = (-0.10, 0.0, 0.10)

# Classes de ratio (m, n <= 4, m >= n, valeurs repliees distinctes).
RATIO_CLASSES = (1.0, 4.0 / 3.0, 1.5, 2.0, 3.0, 4.0)
_CLASS_INDEX = {round(c, 9): i for i, c in enumerate(RATIO_CLASSES)}
_LN_C = float(np.log(len(RATIO_CLASSES)))

_DT_STORE = DT * SUBSAMPLE * 4   # espacement de la serie analysee (v1)


# --- Detecteur m:n v1 + classe du meilleur candidat ---

def lock_analysis(phases_sub: np.ndarray) -> tuple[np.ndarray, np.ndarray,
                                                   np.ndarray]:
    """Detecteur m:n v1 (meilleur candidat, criteres inchanges) + classe.

    Reprise EXACTE des criteres v1 par paire : combine ``psi = a*th_i -
    b*th_j`` avec (a, b) <= 4, concentre (ecart-type circulaire < LOCK_TOL)
    ET derive nulle (|dpsi/dt| < SLOPE_TOL) sur la seconde moitie ; parmi
    les candidats satisfaisants, le MEILLEUR (ecart-type minimal) l'emporte
    -- un verrouillage 2:1 satisfait aussi 4:2, le choix du minimal evite
    le double compte et designe la classe primitive.

    Retourne ``(v, S, comptes)`` :

    * ``v`` : fraction de paires verrouillees (definition v1, inchangee) ;
    * ``S`` : entropie normalisee (ln 6) de la distribution des classes des
      paires verrouillees CLASSEES ; un verrouillage atypique (ratio hors
      des 6 classes, ex. 2:3) compte dans ``v`` mais pas dans ``S`` ;
      ``nan`` si aucune paire classee ;
    * ``comptes`` : histogramme (n_conf, 6) des classes du meilleur candidat.
    """
    uw = _unwrap(phases_sub[phases_sub.shape[0] // 2::4])
    i, j = np.triu_indices(K, k=1)
    n_conf = uw.shape[1]
    n_pair = i.size
    best_std = np.full((n_conf, n_pair), np.inf)
    best_cls = np.full((n_conf, n_pair), -1, dtype=int)
    for a in range(1, LOCK_MAX + 1):
        for b in range(1, LOCK_MAX + 1):
            psi_raw = a * uw[:, :, i] - b * uw[:, :, j]
            psi = psi_raw % (2.0 * np.pi)
            z = np.exp(1j * psi).mean(axis=0)
            circ_std = np.sqrt(np.maximum(
                -2.0 * np.log(np.maximum(np.abs(z), 1e-12)), 0.0))
            diffs = np.diff(psi_raw, axis=0)
            slope = (np.abs(diffs.mean(axis=0)) / _DT_STORE
                     if diffs.size else np.full(circ_std.shape, np.inf))
            ok = (circ_std < LOCK_TOL) & (np.abs(slope) < SLOPE_TOL)
            cls = _CLASS_INDEX.get(round(a / b, 9), -1)
            better = ok & (circ_std < best_std)
            best_std = np.where(better, circ_std, best_std)
            best_cls = np.where(better, cls, best_cls)
    locked = best_std < np.inf
    v = locked.sum(axis=1) / n_pair
    counts = np.zeros((n_conf, len(RATIO_CLASSES)), dtype=int)
    for ci in range(len(RATIO_CLASSES)):
        counts[:, ci] = (locked & (best_cls == ci)).sum(axis=1)
    n_classed = counts.sum(axis=1)
    probs = counts / np.maximum(n_classed[:, None], 1)
    with np.errstate(divide="ignore", invalid="ignore"):
        ent = -(probs * np.where(probs > 0,
                                 np.log(np.maximum(probs, 1e-300)), 0.0)
                ).sum(axis=1)
    s = np.where(n_classed > 0, ent / _LN_C, np.nan)
    return v, s, counts


def u_hat(ratios_row: np.ndarray) -> float:
    """Fraction de membres EXACTS de l'echelle octave (reconstruction de u).

    Le tirage v1 ne stocke pas u ; il se reconstruit exactement : un membre
    decale differe de son ancre octave de >= 3 % en log, un membre exact
    coincide au flottant pres (comparaison a 1e-9 pres).
    """
    anchors = {round(float(x), 9) for x in v1.HARMONIC_LADDER}
    exact = sum(1 for r in ratios_row if round(float(r), 9) in anchors)
    return exact / len(ratios_row)


# --- Jambe d'une graine ---

def run_seed_v2(seed: int, k2_c: float, m_configs: int = M_CONFIGS,
                n_pairs: int = M_PAIRS, eps_grid=EPS_GRID) -> dict:
    """Tous les bras v2 d'une graine.

    Jambe echelle : les ``m_configs`` configurations d'echelle integrees a
    CHAQUE eps du grid (drive uniforme ``k2_c * (1 + eps)``, amplitudes
    unitaires). Jambe paires : les ``2 * n_pairs`` configurations H/N
    integrees une seule fois au point nominal ``k2_c`` (P3bis + portes).
    """
    cfg = draw_configs(seed, m_configs, n_pairs=n_pairs)
    n, m = cfg["n_ladder"], cfg["n_pairs"]
    ratios, ph0 = cfg["ratios"], cfg["phases0"]
    amps = np.ones_like(ph0)                 # amplitudes unitaires PARTOUT

    v_eps, s_eps0 = {}, {}
    for eps in eps_grid:
        ph = integrate(ratios[:n], ph0[:n], amps[:n],
                       k2_c * (1.0 + eps), t_total=T_TOTAL)
        v, s, _c = lock_analysis(ph)
        v_eps[str(eps)] = v.tolist()
        s_eps0[str(eps)] = s.tolist()

    ph_p = integrate(ratios[n:], ph0[n:], amps[n:], k2_c, t_total=T_TOTAL)
    v_p, s_p, _cp = lock_analysis(ph_p)
    r_p = order_parameter(ph_p)
    r_bar_p = r_p[len(r_p) // 2:].mean(axis=0)

    sig = np.array([sigma_config(rr) for rr in ratios[:n]])
    u = np.array([u_hat(rr) for rr in ratios[:n]])

    return {"seed": seed, "k2_c": k2_c, "n": n, "m": m,
            "v_eps": v_eps, "s_eps0": s_eps0,
            "v_pairs": v_p.tolist(), "s_pairs": s_p.tolist(),
            "r_bar_pairs": r_bar_p.tolist(),
            "sigma_ladder": sig.tolist(), "u_ladder": u.tolist()}


# --- Statistiques scellees ---

def _decile_partial_spearman(v_eps: dict, sigma0: np.ndarray) -> float:
    """rho(v, eps | decile de sigma) : rangs residuels par decile (scelle).

    Pour chaque decile de sigma (12 deciles de 10 configurations sur
    l'echelle de 120), ``v`` et ``eps`` sont remplaces par leur rang MOINS
    le rang moyen du decile ; Spearman sur les rangs residuels pooles.
    """
    eps_arr = np.concatenate(
        [np.full(len(v_eps[str(e)]), float(e)) for e in EPS_GRID])
    v_arr = np.concatenate([np.asarray(v_eps[str(e)], dtype=float)
                            for e in EPS_GRID])
    v_rank = np.argsort(np.argsort(v_arr)).astype(float)
    e_rank = np.argsort(np.argsort(eps_arr)).astype(float)
    # Deciles de SIGMA (scelle : 12 deciles de 10 configs x 3 eps), pas de
    # l'index — les blocs eps-major rendraient chaque decile eps-pur et la
    # correlation partielle muette par construction.
    sig_tile = np.tile(sigma0, len(EPS_GRID))
    order = np.argsort(sig_tile, kind="stable")
    rv = np.empty_like(v_arr)
    re = np.empty_like(eps_arr)
    for idx in np.array_split(order, 12):
        rv[idx] = v_rank[idx] - v_rank[idx].mean()
        re[idx] = e_rank[idx] - e_rank[idx].mean()
    if np.std(rv) == 0 or np.std(re) == 0:
        return float("nan")
    return float(np.corrcoef(rv, re)[0, 1])


def _mean_s_excluding_nan(s_list: list) -> tuple:
    arr = np.asarray([x for x in s_list if np.isfinite(x)], dtype=float)
    excl = sum(1 for x in s_list if not np.isfinite(x))
    return (float(arr.mean()) if arr.size else float("nan")), excl


def _seed_result_v2(job: tuple) -> dict:
    seed, k2_c = job
    d = run_seed_v2(seed, k2_c)
    sigma0 = np.asarray(d["sigma_ladder"])
    v0 = np.asarray(d["v_eps"]["0.0"])
    m = d["m"]
    s_h, excl_h = _mean_s_excluding_nan(d["s_pairs"][:m])
    s_n, excl_n = _mean_s_excluding_nan(d["s_pairs"][m:])
    rb_h = float(np.median(np.asarray(d["r_bar_pairs"][:m])))
    rb_n = float(np.median(np.asarray(d["r_bar_pairs"][m:])))
    u_arr = np.asarray(d["u_ladder"])
    v_u1 = float(np.median(v0[u_arr >= 0.999])) if (u_arr >= 0.999).any() \
        else float("nan")
    # Porte plafond scellee : « echelle entierement decalee » = ancre seule
    # exacte, soit u_hat = 1/8 (l'ancre 1.0 est toujours presente dans le
    # tirage v1, donc u_hat > 0 par construction -- un filtre a u_hat <= 0
    # serait toujours vide et la porte jamais evaluable).
    v_u0 = float(np.median(v0[u_arr <= 1 / 8 + 1e-9])) \
        if (u_arr <= 1 / 8 + 1e-9).any() else float("nan")
    return {
        "seed": seed,
        "rho1": float(_spearman(v0, sigma0)),
        "rho_eps_partial": _decile_partial_spearman(d["v_eps"], sigma0),
        "dS": s_h - s_n, "s_h": s_h, "s_n": s_n,
        "excl_h": excl_h, "excl_n": excl_n,
        "r_bar_h": rb_h, "r_bar_n": rb_n,
        "v_u1_median": v_u1, "v_u0_median": v_u0,
        "v_ladder": v0.tolist(), "sigma_ladder": sigma0.tolist(),
        "u_ladder": u_arr.tolist(),
        "v_eps": d["v_eps"], "s_pairs": d["s_pairs"], "m": m,
    }


def _strong_result_v2(k2_c: float) -> float:
    """Null (b) : couplage fort x8 -- si l'attracteur ne discrimine plus
    (|rho| < 0.2), l'instrument est sature, NON_CONCLUSIF."""
    d = run_seed_v2(SEEDS_TEST[0], k2_c * NULL_B_SCALE, eps_grid=(0.0,))
    v0 = np.asarray(d["v_eps"]["0.0"])
    return abs(_spearman(v0, np.asarray(d["sigma_ladder"])))


def _perm_null_a3(seed_data: dict, draws: int = 200) -> float:
    """Null (a3) : etiquettes H/N permutees (graine 0, bras reutilise)."""
    rng = np.random.default_rng(0)
    s_pairs = np.asarray(seed_data["s_pairs"], dtype=float)
    m = seed_data["m"]
    vals = []
    for _ in range(draws):
        sp = s_pairs[rng.permutation(2 * m)]
        h, _ = _mean_s_excluding_nan(sp[:m].tolist())
        nn, _ = _mean_s_excluding_nan(sp[m:].tolist())
        if np.isfinite(h) and np.isfinite(nn):
            vals.append(abs(h - nn))
    return float(np.median(vals)) if vals else float("nan")


def _mechanical_control_v2(seed: int) -> dict:
    """K_eff = 0 : irrationnelles -> v ~ 0 (porte scellee) ; membres exacts
    -> verrouillage cinematique SANS couplage (plafond DECLARE, diagnostic)."""
    rng = np.random.default_rng(seed)
    ratios_irr = np.array([
        np.concatenate([[1.0], np.exp(rng.uniform(np.log(1.05), np.log(1.95),
                                                  K - 1))])
        for _ in range(6)])
    ratios_exact = np.array([v1.HARMONIC_LADDER] * 4)
    ratios = np.concatenate([ratios_irr, ratios_exact])
    ph0 = rng.uniform(0.0, 2.0 * np.pi, size=ratios.shape)
    ph = integrate(ratios, ph0, np.ones_like(ph0), 0.0, t_total=10.0)
    v, _s, _c = lock_analysis(ph)
    return {"seed": seed,
            "v0_irr_mean": float(v[:6].mean()),
            "v0_exact_mean": float(v[6:].mean())}


def run_protocol_v2(k2_c: float = None, parallel: bool = True) -> dict:
    """Run principal : graines test, K2_c gele par --calibrate."""
    if k2_c is None:
        k2_c = K2_COUPLING
    jobs = [(s, k2_c) for s in SEEDS_TEST]
    if parallel and len(jobs) > 1 and (os.cpu_count() or 2) > 2:
        n_proc = max(1, min(len(jobs) + 1, (os.cpu_count() or 2) - 1))
        with Pool(n_proc) as pool:
            per_seed = pool.map(_seed_result_v2, jobs)
            (null_b,) = pool.map(_strong_result_v2, [k2_c])
            ctrls = pool.map(_mechanical_control_v2, list(SEEDS_TEST))
    else:
        per_seed = [_seed_result_v2(j) for j in jobs]
        null_b = _strong_result_v2(k2_c)
        ctrls = [_mechanical_control_v2(s) for s in SEEDS_TEST]

    rho1s = [d["rho1"] for d in per_seed]
    rho_eps = [d["rho_eps_partial"] for d in per_seed]
    dss = [d["dS"] for d in per_seed]
    rb_h = [d["r_bar_h"] for d in per_seed]
    rb_n = [d["r_bar_n"] for d in per_seed]
    v_u1 = [d["v_u1_median"] for d in per_seed]
    v_u0 = [d["v_u0_median"] for d in per_seed]

    # Null (a) : permutation sigma, graine 0.
    perm_rng = np.random.default_rng(0)
    v0 = np.asarray(per_seed[0]["v_ladder"])
    s0 = np.asarray(per_seed[0]["sigma_ladder"])
    null_a = float(np.median([
        abs(_spearman(v0, perm_rng.permutation(s0))) for _ in range(200)]))
    # Null (a3) : permutation etiquettes H/N, graine 0.
    null_a3 = _perm_null_a3(per_seed[0])

    # Controle mecanique scelle « sur 5/5 graines » (§3) : la porte porte
    # sur toutes les graines test, pas sur la seule graine 0.
    ctrl_ok = all(c["v0_irr_mean"] <= CTRL_V0_MAX for c in ctrls)

    p1 = sum(r >= BAND_P1 for r in rho1s) >= 4
    p2 = sum(abs(r) <= BAND_P2 for r in rho_eps) >= 4
    p3_ok = sum(x >= BAND_P3 for x in dss) >= 4
    gate_floor = sum(np.isfinite(x) and x < GATE_V_U1 for x in v_u1) \
        >= GATE_MIN_SEEDS
    gate_ceiling = sum(np.isfinite(x) and x > GATE_V_U0 for x in v_u0) \
        >= GATE_MIN_SEEDS
    gate_match = sum(abs(h - n) > GATE_MATCH_RB
                     for h, n in zip(rb_h, rb_n)) >= GATE_MIN_SEEDS

    if gate_floor:
        verdict = "NON_CONCLUSIF_INSTRUMENT (porte plancher v(u=1))"
    elif gate_ceiling:
        verdict = "NON_CONCLUSIF_INSTRUMENT (porte plafond v(u=0))"
    elif gate_match:
        verdict = "NON_CONCLUSIF_INSTRUMENT (porte appariement r_bar H/N)"
    elif null_b < 0.2:
        verdict = "NON_CONCLUSIF_INSTRUMENT (null b : saturation forte)"
    elif not ctrl_ok:
        verdict = "NON_CONCLUSIF_INSTRUMENT (controle mecanique)"
    elif p1 and p2 and p3_ok and null_a <= 0.2 and null_a3 <= 0.05:
        verdict = "SUPPORTED"
    # Declencheurs NOT SUPPORTED du scelle §4 : « P1 < 0.2 (indifference) »,
    # pas « P1 rate sa bande 0.6 » -- quantifies >= 4/5 graines comme les
    # predictions P1/P2bis/P3bis. Branche non atteinte ce run (null b sort
    # avant), la correction vaut pour les executions futures.
    elif sum(r < BAND_P1_FAIL for r in rho1s) >= 4 \
            or sum(abs(r) > BAND_P2_FAIL for r in rho_eps) >= 4 \
            or sum(x < BAND_P3_FAIL for x in dss) >= 4:
        verdict = "NOT_SUPPORTED"
    else:
        verdict = "NON_CONCLUSIF"

    return {
        "case": "17bis-stv-v2-lock-structure",
        "k2_coupling": k2_c,
        "seeds": list(SEEDS_TEST), "m_configs": M_CONFIGS,
        "per_seed": [{k: d[k] for k in d if k not in ("v_eps", "s_pairs")}
                     for d in per_seed],
        "rho1_by_seed": rho1s, "rho_eps_by_seed": rho_eps,
        "dS_by_seed": dss, "r_bar_h_by_seed": rb_h,
        "r_bar_n_by_seed": rb_n, "v_u1_by_seed": v_u1, "v_u0_by_seed": v_u0,
        "null_a_median_abs_rho": null_a, "null_a3_median_abs_dS": null_a3,
        "null_b_abs_rho": null_b,
        "ctrl_mechanical": ctrls,
        "p1": bool(p1), "p2": bool(p2), "p3": bool(p3_ok),
        "gates": {"floor_v_u1": bool(gate_floor),
                  "ceiling_v_u0": bool(gate_ceiling),
                  "match_r_bar": bool(gate_match)},
        "verdict": verdict,
        "bands": {"p1_min": BAND_P1, "p1_fail": BAND_P1_FAIL,
                  "p2_max": BAND_P2,
                  "p2_fail": BAND_P2_FAIL, "p3_min": BAND_P3,
                  "p3_fail": BAND_P3_FAIL, "match_r_bar_max": GATE_MATCH_RB,
                  "ctrl_v0_max": CTRL_V0_MAX},
    }


# --- Calibration (graines disjointes 11/22/33) ---

def _calib_point(k_c: float) -> dict:
    """Un point de la grille de calibration : v(u=1) et variance de v."""
    v_exact_pool, vvars = [], []
    for s in SEEDS_CALIB:
        cfg = draw_configs(s, 24, n_pairs=6)
        nl = cfg["n_ladder"]
        ph = integrate(cfg["ratios"][:nl], cfg["phases0"][:nl],
                       np.ones((nl, K)), k_c, t_total=T_TOTAL)
        v, _s, _c = lock_analysis(ph)
        u_arr = np.array([u_hat(rr) for rr in cfg["ratios"][:nl]])
        v_exact_pool.extend(v[u_arr >= 0.999].tolist())
        vvars.append(float(np.var(v)))
    med = float(np.median(v_exact_pool)) if v_exact_pool else float("nan")
    return {"k2": k_c, "v_u1_median": med, "n_exact": len(v_exact_pool),
            "v_variance_mean": float(np.mean(vvars))}


def calibrate_v2(parallel: bool = True) -> dict:
    """Gel de K2_c : cible scellee ``v_bar(u = 1) in [0.5, 0.8]``.

    Mediane de ``v`` sur les configurations toutes-exactes (``u_hat = 1``)
    au point nominal, pool des trois graines de calibration (11/22/33,
    disjointes des graines de test). Parmi les K2_c dont la mediane tombe
    dans la fenetre, on retient celui le plus proche de 0.65 (centre).
    Repli declare si la fenetre est inatteignable sur toute la grille :
    K2_c a variance de ``v`` maximale (sensibilite, neutre en signe).
    """
    grid = [4.0, 8.0, 16.0, 24.0, 32.0, 48.0, 64.0, 96.0, 128.0]
    if parallel and (os.cpu_count() or 2) > 2:
        with Pool(min(len(grid), (os.cpu_count() or 2) - 1)) as pool:
            trace = pool.map(_calib_point, grid)
    else:
        trace = [_calib_point(k_c) for k_c in grid]
    best_window, best_var = None, None
    for row in trace:
        med = row["v_u1_median"]
        if np.isfinite(med) and 0.5 <= med <= 0.8 \
                and (best_window is None
                     or abs(med - 0.65) < best_window[0]):
            best_window = (abs(med - 0.65), row["k2"], med)
        if best_var is None or row["v_variance_mean"] > best_var[0]:
            best_var = (row["v_variance_mean"], row["k2"], med)
    if best_window is not None:
        return {"k2_coupling": best_window[1],
                "source": "fenetre v(u=1) scellee",
                "v_u1_median": best_window[2], "v_variance": None,
                "trace": trace}
    return {"k2_coupling": best_var[1],
            "source": "repli variance v (declare)",
            "v_u1_median": best_var[2], "v_variance": best_var[0],
            "trace": trace}


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Case 17bis - STV v2 : structure du lock")
    ap.add_argument("--calibrate", action="store_true",
                    help="gel de K2_c sur graines disjointes (11/22/33)")
    ap.add_argument("--k2", type=float, default=None,
                    help="K2_c explicite (defaut : K2_COUPLING gele)")
    ap.add_argument("--out", type=str, default=None,
                    help="ecrire le JSON resultat a ce chemin")
    ap.add_argument("--json", action="store_true",
                    help="sortie JSON sur stdout")
    args = ap.parse_args()
    if args.calibrate:
        out = calibrate_v2()
    else:
        out = run_protocol_v2(k2_c=args.k2)
    text = json.dumps(out, indent=2, ensure_ascii=False)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(text + "\n")
    if args.json:
        print(text)
    else:
        for key, val in out.items():
            if key in ("per_seed", "trace"):
                continue
            print(f"{key}: {val}")


if __name__ == "__main__":
    main()
