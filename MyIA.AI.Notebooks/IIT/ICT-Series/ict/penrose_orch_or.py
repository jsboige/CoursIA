"""Jouet « réduction objective Orch-OR » pour la distillation Penrose (case 24, #8182 iceberg L3).

La review formalise ELLE-MÊME sa mécanique quantitative : la loi de vie
« τ ≈ ħ/E_G [...] very much like a **half-life** in a radioactive decay »
(§4.4, p.52-53), l'auto-énergie de la **différence** des deux distributions
(« one mass distribution counts positively and the other, negatively », p.53),
le régime des noyaux (E_c = G·m²/a_c, « roughly 2 × 10¹⁰ tubulins [...] for
25 ms », p.61), le **double effet** environnemental (l'entanglement externe
fournit l'essentiel de E_G **et** « completely masked » tout élément non
aléatoire, §4.5, p.54) et l'**hésitation de scaling** que la source porte
elle-même (2× vs √2, « the mass enters quadratically in E_G », p.62). Ce
module rend la triple structure falsifiable AU NIVEAU MÉCANIQUE (grade C —
aucune physique nouvelle n'est testée, cf scellé §6.1) :

- P1 : l'horloge exponentielle exécute fidèlement τ ≈ ħ/E_G (moyenne ET
  demi-vie empirique sur l'échelle de cibles) ;
- P2 : le MÊME w_env = η/(1+η) raccourcit la vie (τ_eff = τ_iso/(1+η)) et
  lave le biais interne (rétention R = 1/(1+η)) — le couple (τ, masquage)
  lié par une seule variable, qu'un bruit générique ne réalise pas ;
- P3 : dissociation de régimes — Fermi (chaque noyau déplacé de son
  diamètre) E_G linéaire en K ; blob (réseau entier déplacé de lui-même)
  E_G quadratique — l'« hésitation » 2×/√2 de la review est une séparation
  de régimes, mesurée : diviser τ par 2 coûte 2× la masse en Fermi,
  2^(1/α_eff) ≈ √2 en blob ;
- P3d : confrontation arithmétique aux nombres publiés (2×10¹⁰ à 25 ms,
  ~10⁹ à 500 ms, ratio 20) + constat documenté de l'écart interne
  (E_G cité ≈ 10⁻¹⁰ eV vs ħ/25 ms ≈ 2,6×10⁻¹⁴ eV, facteur ~3 800).

Glose d'une prose scellée : « survie à ln 2 ∈ [0.68, 0.72] » se lit comme la
**demi-vie empirique normalisée** median̂/τ_target, attendue ln 2 = 0.693 —
seule lecture où la bande contient sa cible (la survie à ln2·τ vaudrait 0,5,
hors bande). La survie S(ln2·τ) est aussi rapportée, sans bande.

Le scellé (bandes, graines, nulls, portes, verdicts bornés) vit dans
docs/ict/penrose-orch-or-pre-enregistrement.md (v1 + amendement v2 du
2026-11-20, pré-exécution) — ce module ne le redéfinit pas, il l'exécute.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path

import numpy as np

__all__ = [
    "sample_disc",
    "eg_fermi",
    "eg_blob",
    "required_tubulins_fermi",
    "required_tubulins_blob",
    "lifetime_checks",
    "dual_effect_checks",
    "calibrate",
    "verdict",
    "run_seed",
    "TEST_SEEDS",
    "CALIB_SEEDS",
]

# ---------------------------------------------------------------------------
#  Constantes gelées par le scellé v1 §4 — aucune ne bouge au run.
# ---------------------------------------------------------------------------
G = 6.67430e-11              # m³ kg⁻¹ s⁻²
HBAR = 1.054571817e-34       # J s
U_AMU = 1.66053906660e-27    # kg
M_CARBON = 12.0 * U_AMU      # noyau de carbone (12 u)
A_CARBON = 2.5e-15           # m — rayon nucléaire du carbone (p.61)
M_TUBULIN = 110_000.0 * U_AMU  # 110 kDa
N_CARBON = M_TUBULIN / M_CARBON      # ≈ 9166,7 équivalents-masse (scellé §6.3)
E_CARBON = G * M_CARBON**2 / A_CARBON  # ≈ 1,060×10⁻⁴⁷ J — formule de la source
E_TUBULIN_FERMI = N_CARBON * E_CARBON  # contribution Fermi par tubuline

# Réseaux — Fermi : scellé v1 ; blob : amendement v2 (étendue 400 nm, plancher
# dur 2 nm, échelle {1024..8192}, doublement à (4096, 8192)).
DIAM_FERMI = 100e-9          # m — étendue (diamètre) du disque Fermi
HARDCORE_FERMI = 1e-9        # m — plancher dur (implémente « espacement ≥ ~1,6 nm »)
K_FERMI = (64, 256, 1024, 4096)
DIAM_BLOB = 400e-9           # m — étendue (diamètre) du disque blob (v2)
HARDCORE_BLOB = 2e-9         # m — plancher dur (v2)
K_BLOB = (1024, 2048, 4096, 8192)
D_BLOB = 8.0 * DIAM_BLOB     # m — séparation rigide du régime chat (v2 : D = 8·R_lat)
D_FERMI = 2.0 * A_CARBON     # m — déplacement nucléaire = diamètre du carbone (p.61)

# Processus de réduction et effet dual (scellé v1 §4).
TAU_LADDER_MS = (500.0, 100.0, 25.0, 10.0, 2.5)
TAU_ISO_MS = 25.0            # point de référence isolé pour l'effet dual
ETA_GRID = (0.1, 0.5, 1.0, 10.0, 100.0)
BIAS_GRID = (0.2, 0.35, 0.65, 0.8)   # contrôle 0.5 exclu (rétention non définie)
M_GRID = (10_000, 20_000, 40_000)
TEST_SEEDS = (0, 1, 7, 42, 99)
CALIB_SEEDS = (11, 22, 33)
Z_WILSON = 1.959963985       # quantile 0.975 normal (Wilson 95 %)

# Confrontation arithmétique à la source (scellé v1 §4, P3d — lecture directe).
SOURCE_N_25MS = 2.0e10       # « roughly 2 × 10¹⁰ » tubulines à 25 ms (p.61)
SOURCE_N_500MS = 1.0e9       # « ~10⁹ » à 500 ms (p.61)
SOURCE_EG_QUOTED_EV = 1.0e-10  # « roughly 10⁻¹⁰ eV » cité à p.67 (constat, pas bande)

# Bandes du scellé v1 + amendement v2 — source unique pour tests et verdict.
BANDS = {
    "p1_mean_lo": 0.97, "p1_mean_hi": 1.03,      # τ̂/τ_target
    "p1_halflife_lo": 0.68, "p1_halflife_hi": 0.72,  # median̂/τ_target, attendu ln2
    "p2_tol": 0.05,                               # |x̂ − 1/(1+η)| aux deux observables
    "p3a_linearity_lo": 0.99, "p3a_linearity_hi": 1.01,
    "p3a_cross_gate": 1e-6,                       # porte de linéarité (croisés/propres)
    "p3b_cat_lo": 0.80, "p3b_cat_hi": 1.05,       # E_G^B/[2G·E_AA]
    "p3b_doubling_lo": 3.5, "p3b_doubling_hi": 4.5,
    "p3c_fermi_lo": 1.98, "p3c_fermi_hi": 2.02,   # 2.00 ± 0.02
    "p3c_blob_lo": 1.39, "p3c_blob_hi": 1.49,     # √2 élargie (amendement v2)
    "p3d_lo": 1.5, "p3d_hi": 3.5,                 # rapports aux nombres publiés
    "p3d_ratio_tol": 0.1,                         # N(25)/N(500) = 20 ± 0.1
    "null_a_halfwidth": 0.005,                    # Wilson à M calibré, graines de calib
    "null_b_lo": 0.45, "null_b_hi": 0.55,         # contrôle b = 0.5
    # Seuils REFUTED (sens de la non-réalisabilité) — scellé v1 verdict borné.
    "refuted_p1_mean": 0.10,                      # |τ̂/τ − 1| > 0.10 : loi non fidèle
    "refuted_p1_halflife": (0.60, 0.80),          # demi-vie hors de [0.60, 0.80]
    "refuted_blob_doubling_max": 2.5,             # blob ~linéaire
    "refuted_fermi_linearity": (0.90, 1.10),      # Fermi ~quadratique (impossible ici, déclaré)
}


# ---------------------------------------------------------------------------
#  Réseaux : Poisson 2D à plancher dur dans un disque, préfixes imbriqués.
# ---------------------------------------------------------------------------
def sample_disc(seed: int, k: int, diameter: float, hardcore: float,
                rng: np.random.Generator | None = None) -> np.ndarray:
    """Tire k sites-tubulines dans le disque (Poisson 2D, rejet hors disque
    + rejet sous le plancher dur), positions reproductibles par graine.

    L'échelle de densification est **imbriquée** : les K-ladders du scellé
    utilisent des préfixes du même processus séquentiel par graine (le K-ladder
    est une densification à étendue fixe — choix déclaré, scellé §6.5).
    """
    own = rng is None
    rng = np.random.default_rng(seed) if own else rng
    radius = diameter / 2.0
    out = np.empty((k, 2))
    n = 0
    while n < k:
        need = k - n
        cand = rng.uniform(-radius, radius, size=(max(4 * need, 1024), 2))
        cand = cand[cand[:, 0] ** 2 + cand[:, 1] ** 2 < radius**2]
        for p in cand:
            if n >= k:
                break
            if n == 0 or np.min(np.sum((out[:n] - p) ** 2, axis=1)) >= hardcore**2:
                out[n] = p
                n += 1
    return out


def _pair_inv_sum(a: np.ndarray, b: np.ndarray, offset: np.ndarray | None = None,
                  exclude_diag: bool = False, block: int = 1024) -> float:
    """Σ 1/|a_i − b_j (+offset)| en blocs mémoire bornés.

    ``exclude_diag`` ne s'emploie que pour a is b (termes propres exclus,
    somme ordonnée sur les paires i≠j).
    """
    total = 0.0
    same = exclude_diag and offset is None
    for i0 in range(0, len(a), block):
        d = b[None, :, :] - a[i0:i0 + block, None, :]
        if offset is not None:
            d = d + offset[None, None, :]
        r = np.sqrt(np.sum(d * d, axis=-1))
        if same:
            rows = np.arange(i0, min(i0 + block, len(a)))
            r[rows - i0, rows] = np.inf   # diagonale : colonne GLOBALE, pas bloc-relative
        total += float(np.sum(1.0 / r))
    return total


# ---------------------------------------------------------------------------
#  E_G exacte (double somme newtonienne sur la distribution de différence).
# ---------------------------------------------------------------------------
def eg_fermi(sites: np.ndarray, directions: np.ndarray) -> dict:
    """E_G du régime Fermi : chaque noyau déplacé de d = 2·a_c.

    Termes propres : E_c par carbone (sphère étendue au-delà de son rayon,
    formule de la source, scellé v1 §4) — exacts, analytiques. Termes
    croisés : dipôle-dipôle par paires de SITES (valide : espacement ~nm ≫
    5 fm), développement au second ordre exact :

        E_ij = G·m²·[d_i·d_j − 3 (d_i·r̂)(d_j·r̂)] / r³   (par carbone de chaque site)

    agrégé en μ_i = n_c·m_c·d_i. La porte P3a mesure croisés/propres.
    """
    k = len(sites)
    self_energy = k * N_CARBON * E_CARBON
    d_vec = D_FERMI * directions                      # (K, 2)
    mu = N_CARBON * M_CARBON * d_vec                  # moments dipolaires par site
    cross = 0.0
    block = 1024
    for i0 in range(0, k, block):
        sl = slice(i0, min(i0 + block, k))
        diff = sites[None, :, :] - sites[sl, None, :]  # (b, K, 2) : r_ij = site_j − site_i
        r = np.sqrt(np.sum(diff * diff, axis=-1))
        rows = np.arange(i0, min(i0 + block, k))
        r[rows - i0, rows] = np.inf      # diagonale : colonne GLOBALE, pas bloc-relative
        r_hat = diff / r[..., None]
        mu_dot = mu[sl] @ mu.T                         # (b, K)
        mur_i = np.einsum("ik,ijk->ij", mu[sl], r_hat)
        mur_j = np.einsum("jk,ijk->ij", mu, r_hat)
        term = mu_dot - 3.0 * mur_i * mur_j
        cross += 0.5 * float(np.sum(G * term / r**3))  # ½ : somme non ordonnée
    total = self_energy + cross
    return {
        "self": self_energy,
        "cross": cross,
        "total": total,
        "linearity_ratio": total / self_energy,
        "cross_over_self": abs(cross) / self_energy,
    }


def eg_blob(sites: np.ndarray) -> dict:
    """E_G du régime blob : réseau ENTIER rigidement déplacé de D (chat).

    Sites agrégés en masses ponctuelles M_s = n_c·m_c (dispersion intra-site
    ~nm ≪ D). Énergie exacte de la distribution de différence (signes ±) :

        E_G = G·M_s²·[ Σ_{i≠j} 1/r_ij  −  Σ_{i,j} 1/|D + p_i − p_j| ]

    La quantité « 2G·E_AA » du scellé vaut G·M_s²·Σ_{i≠j} 1/r_ij (somme
    ordonnée) ; la clause P3b-1 mesure 1 − S_AB/S_AA.
    """
    m_site = N_CARBON * M_CARBON
    sum_aa = _pair_inv_sum(sites, sites, exclude_diag=True)      # ordonnée i≠j
    d_offset = np.array([D_BLOB, 0.0])
    sum_ab = _pair_inv_sum(sites, sites, offset=d_offset)        # pleine i,j
    e_aa_2g = G * m_site**2 * sum_aa
    e_ab = G * m_site**2 * sum_ab
    total = e_aa_2g - e_ab
    return {
        "E_AA_2G": e_aa_2g,
        "E_AB": e_ab,
        "total": total,
        "cat_ratio": total / e_aa_2g,
        "tau_seconds": HBAR / total,
    }


# ---------------------------------------------------------------------------
#  Conséquence opérationnelle : N requis par cible τ, dans chaque régime.
# ---------------------------------------------------------------------------
def required_tubulins_fermi(tau_seconds: float) -> float:
    """N linéaire : N·n_c·E_c = ħ/τ (les croisés sont ≤ 10⁻¹² des propres)."""
    return HBAR / (tau_seconds * E_TUBULIN_FERMI)


def required_tubulins_blob(eg_by_k: dict[int, float], tau_seconds: float) -> float:
    """N blob par loi puissance locale sur le bracket supérieur (4096, 8192).

    α_eff = ln[E(8192)/E(4096)]/ln 2 (correction de plancher déclarée,
    amendement v2 point 2) ; N(τ) = 8192·(τ(8192)/τ)^{1/α_eff}.
    """
    k1, k2 = 4096, 8192
    e1, e2 = eg_by_k[k1], eg_by_k[k2]
    alpha = math.log(e2 / e1) / math.log(k2 / k1)
    tau_k2 = HBAR / e2
    return k2 * (tau_k2 / tau_seconds) ** (1.0 / alpha)


# ---------------------------------------------------------------------------
#  P1 — loi de vie : l'horloge exponentielle réalise-t-elle τ ≈ ħ/E_G ?
# ---------------------------------------------------------------------------
def lifetime_checks(seed: int, m_ens: int) -> dict:
    """Ensembles de M durées ~ Exp(τ_target) sur l'échelle scellée.

    Observables : τ̂/τ_target (moyenne) et median̂/τ_target (demi-vie
    empirique, attendue ln 2 = 0.693 — glose du scellé, cf docstring module).
    La survie S(ln2·τ) est rapportée sans bande (attendue 0.5).
    """
    rng = np.random.default_rng(100_000 + seed)
    rows = {}
    for tau_ms in TAU_LADDER_MS:
        tau = tau_ms * 1e-3
        durs = rng.exponential(tau, m_ens)
        mean_ratio = float(durs.mean() / tau)
        half_ratio = float(np.median(durs) / tau)
        survival = float(np.mean(durs > tau * math.log(2.0)))
        ok = (BANDS["p1_mean_lo"] <= mean_ratio <= BANDS["p1_mean_hi"]
              and BANDS["p1_halflife_lo"] <= half_ratio <= BANDS["p1_halflife_hi"])
        rows[f"{tau_ms:g}"] = {
            "mean_ratio": mean_ratio,
            "halflife_ratio": half_ratio,
            "survival_ln2": survival,
            "ok": bool(ok),
        }
    return {"ladder": rows, "ok": all(r["ok"] for r in rows.values())}


# ---------------------------------------------------------------------------
#  P2 + null (b) — effet dual : la même part lave le biais et raccourcit τ.
# ---------------------------------------------------------------------------
def _p_effective(b: float, eta: float) -> float:
    """P(A) = (b + η/2)/(1+η) — poids du résultat A quand l'environnement
    détient la part η de E_G (règle de mélange du scellé §4, vrai par
    construction — ce que P2 mesure est l'estimateur empirique du couple)."""
    return (b + eta / 2.0) / (1.0 + eta)


def dual_effect_checks(seed: int, m_ens: int) -> dict:
    """Pour chaque η : τ̂(η)/τ̂(0) et rétention R̂ agrégée sur les 4 biais."""
    rng_tau = np.random.default_rng(200_000 + seed)
    tau_iso = TAU_ISO_MS * 1e-3
    tau0_hat = float(rng_tau.exponential(tau_iso, m_ens).mean())
    rows = {}
    for eta in ETA_GRID:
        tau_eta_hat = float(rng_tau.exponential(tau_iso / (1.0 + eta), m_ens).mean())
        ratio = tau_eta_hat / tau0_hat
        expected = 1.0 / (1.0 + eta)
        r_hats = []
        for b in BIAS_GRID:
            p = _p_effective(b, eta)
            rng_b = np.random.default_rng(300_000 + seed + int(eta * 1000) * 10 + int(b * 100))
            draws = rng_b.random(m_ens) < p
            p_hat = float(draws.mean())
            r_hats.append((p_hat - 0.5) / (b - 0.5))
        r_hat = float(np.mean(r_hats))
        ok = (abs(ratio - expected) <= BANDS["p2_tol"]
              and abs(r_hat - expected) <= BANDS["p2_tol"])
        rows[f"{eta:g}"] = {
            "tau_ratio": ratio,
            "retention": r_hat,
            "retention_by_bias": r_hats,
            "expected": expected,
            "ok_tau": bool(abs(ratio - expected) <= BANDS["p2_tol"]),
            "ok_retention": bool(abs(r_hat - expected) <= BANDS["p2_tol"]),
            "ok": bool(ok),
        }
    # Null (b) : contrôle b = 0.5 neutre quel que soit η.
    rng_n = np.random.default_rng(400_000 + seed)
    null_b = []
    for eta in ETA_GRID:
        p = _p_effective(0.5, eta)   # = 0.5 exactement
        draws = rng_n.random(m_ens) < p
        null_b.append(bool(BANDS["null_b_lo"] <= draws.mean() <= BANDS["null_b_hi"]))
    return {
        "tau0_hat": tau0_hat,
        "by_eta": rows,
        "ok": all(r["ok"] for r in rows.values()),
        "null_b_ok": all(null_b),
        "null_b": null_b,
    }


# ---------------------------------------------------------------------------
#  Calibration — M sur graines disjointes {11, 22, 33}, jamais sur les tests.
# ---------------------------------------------------------------------------
def _wilson_half(p_hat: float, m: int) -> float:
    denom = 1.0 + Z_WILSON**2 / m
    center = (p_hat + Z_WILSON**2 / (2.0 * m)) / denom
    rad = Z_WILSON * math.sqrt(p_hat * (1.0 - p_hat) / m
                               + Z_WILSON**2 / (4.0 * m * m)) / denom
    return float(rad)  # demi-largeur ; le centre est rapporté par l'appelant si besoin


def calibrate() -> dict:
    """Taille d'ensemble M : plus petite valeur de la grille donnant une
    demi-largeur Wilson (p = 0.5) ≤ 0.005 sur TOUTES les graines 11/22/33."""
    scan = {}
    for m in M_GRID:
        halves = []
        for seed in CALIB_SEEDS:
            rng = np.random.default_rng(500_000 + seed + m % 1000)
            p_hat = float((rng.random(m) < 0.5).mean())
            halves.append(_wilson_half(p_hat, m))
        scan[str(m)] = {"wilson_halves": halves, "max_half": max(halves)}
    selected = None
    for m in M_GRID:
        if scan[str(m)]["max_half"] <= BANDS["null_a_halfwidth"]:
            selected = m
            break
    return {
        "grid_scan": scan,
        "m_selected": selected,
        "null_a_ok": selected is not None
        and scan[str(selected)]["max_half"] <= BANDS["null_a_halfwidth"],
    }


# ---------------------------------------------------------------------------
#  P3d — confrontation arithmétique (analytique, sans graine).
# ---------------------------------------------------------------------------
def confrontation_source() -> dict:
    """N̂(25 ms) vs « roughly 2 × 10¹⁰ » ; N̂(500 ms) vs « ~10⁹ » ; ratio vs 20 ;
    et le constat documenté (sans bande) de l'écart interne de la source."""
    n25 = required_tubulins_fermi(25e-3)
    n500 = required_tubulins_fermi(500e-3)
    eg_25_ev = (HBAR / 25e-3) / 1.602176634e-19   # ħ/25 ms en eV
    checks = {
        "n25_ratio": n25 / SOURCE_N_25MS,
        "n500_ratio": n500 / SOURCE_N_500MS,
        "n25_over_n500": n25 / n500,
        "ok_n25": bool(BANDS["p3d_lo"] <= n25 / SOURCE_N_25MS <= BANDS["p3d_hi"]),
        "ok_n500": bool(BANDS["p3d_lo"] <= n500 / SOURCE_N_500MS <= BANDS["p3d_hi"]),
        "ok_ratio": bool(abs(n25 / n500 - 20.0) <= BANDS["p3d_ratio_tol"]),
    }
    checks["ok"] = bool(checks["ok_n25"] and checks["ok_n500"] and checks["ok_ratio"])
    checks["constat"] = {
        "eg_quoted_ev": SOURCE_EG_QUOTED_EV,
        "hbar_over_25ms_ev": eg_25_ev,
        "factor": SOURCE_EG_QUOTED_EV / eg_25_ev,
        "note": ("constat de lecture, pas une bande : le passage p.67 (réponse à "
                 "Tuszynski) peut citer l'E_G d'une autre configuration — scellé §6.4"),
    }
    return checks


# ---------------------------------------------------------------------------
#  Run par graine.
# ---------------------------------------------------------------------------
@dataclass
class SeedResult:
    """Une graine complète : réseaux, trois régimes, loi de vie, effet dual."""
    seed: int
    p3a: dict
    p3b: dict
    p3c: dict
    p1: dict
    p2: dict

    def to_dict(self) -> dict:
        return {
            "seed": self.seed, "p1": self.p1, "p2": self.p2,
            "p3a": self.p3a, "p3b": self.p3b, "p3c": self.p3c,
        }


def run_seed(seed: int, m_ens: int) -> dict:
    """Une graine de test : Fermi (4 K, 2 variantes), blob (4 K), loi de vie, dual."""
    # Réseaux imbriqués par graine (un tir chacun, préfixes pour les K-ladders).
    lattice_f = sample_disc(seed, max(K_FERMI), DIAM_FERMI, HARDCORE_FERMI)
    lattice_b = sample_disc(70_000 + seed, max(K_BLOB), DIAM_BLOB, HARDCORE_BLOB)

    rng_dir = np.random.default_rng(60_000 + seed)
    common_dir = rng_dir.normal(size=2)
    common_dir /= np.linalg.norm(common_dir)

    # --- P3a : Fermi linéaire + porte croisés/propres, 4 K, 2 variantes. ---
    p3a_rows = {}
    for k in K_FERMI:
        sites = lattice_f[:k]
        dirs_common = np.tile(common_dir, (k, 1))
        dirs_indep = rng_dir.normal(size=(k, 2))
        dirs_indep /= np.linalg.norm(dirs_indep, axis=1, keepdims=True)
        res_c = eg_fermi(sites, dirs_common)
        res_i = eg_fermi(sites, dirs_indep)
        ok_k = all(
            BANDS["p3a_linearity_lo"] <= r["linearity_ratio"] <= BANDS["p3a_linearity_hi"]
            and r["cross_over_self"] <= BANDS["p3a_cross_gate"]
            for r in (res_c, res_i)
        )
        p3a_rows[str(k)] = {
            "common": {kk: r for kk, r in res_c.items()},
            "independent": {kk: r for kk, r in res_i.items()},
            "ok": bool(ok_k),
        }
    p3a = {"by_k": p3a_rows,
           "ok": all(r["ok"] for r in p3a_rows.values()),
           "gate_ok": all(
               v["common"]["cross_over_self"] <= BANDS["p3a_cross_gate"]
               and v["independent"]["cross_over_self"] <= BANDS["p3a_cross_gate"]
               for v in p3a_rows.values())}

    # --- P3b : blob quadratique — chat ratio + doublement à (4096, 8192). ---
    eg_by_k = {k: eg_blob(lattice_b[:k])["total"] for k in K_BLOB}
    blob_detail = {str(k): eg_blob(lattice_b[:k]) for k in K_BLOB}
    cat_ok = all(BANDS["p3b_cat_lo"] <= blob_detail[str(k)]["cat_ratio"] <= BANDS["p3b_cat_hi"]
                 for k in K_BLOB)
    doubling = eg_by_k[8192] / eg_by_k[4096]
    doubling_ok = BANDS["p3b_doubling_lo"] <= doubling <= BANDS["p3b_doubling_hi"]
    p3b = {"by_k": blob_detail, "doubling_4096_8192": doubling,
           "ok": bool(cat_ok and doubling_ok)}

    # --- P3c : N(τ/2)/N(τ) — 2,00 en Fermi (analytique, exact par linéarité),
    #     2^(1/α_eff) en blob (amendement v2, bande [1.39, 1.49]). ---
    n_fermi_half = required_tubulins_fermi(TAU_ISO_MS * 1e-3 / 2.0)
    n_fermi_full = required_tubulins_fermi(TAU_ISO_MS * 1e-3)
    fermi_ratio = n_fermi_half / n_fermi_full
    tau_8192 = HBAR / eg_by_k[8192]
    n_blob_half = required_tubulins_blob(eg_by_k, tau_8192)          # N(τ(8192))
    n_blob_full = required_tubulins_blob(eg_by_k, 2.0 * tau_8192)    # N(2·τ(8192))
    blob_ratio = n_blob_half / n_blob_full
    p3c = {
        "fermi_ratio": fermi_ratio,
        "blob_ratio": blob_ratio,
        "alpha_eff": math.log(eg_by_k[8192] / eg_by_k[4096]) / math.log(2.0),
        "tau_8192_us": tau_8192 * 1e6,
        "ok": bool(BANDS["p3c_fermi_lo"] <= fermi_ratio <= BANDS["p3c_fermi_hi"]
                   and BANDS["p3c_blob_lo"] <= blob_ratio <= BANDS["p3c_blob_hi"]),
        "ok_fermi": bool(BANDS["p3c_fermi_lo"] <= fermi_ratio <= BANDS["p3c_fermi_hi"]),
        "ok_blob": bool(BANDS["p3c_blob_lo"] <= blob_ratio <= BANDS["p3c_blob_hi"]),
    }

    p1 = lifetime_checks(seed, m_ens)
    p2 = dual_effect_checks(seed, m_ens)
    return SeedResult(seed=seed, p3a=p3a, p3b=p3b, p3c=p3c, p1=p1, p2=p2).to_dict()


# ---------------------------------------------------------------------------
#  Verdict borné (scellé v1 §4 — aucune bande relue ici, seulement BANDS).
# ---------------------------------------------------------------------------
def _count(flags: list[bool]) -> int:
    return sum(1 for f in flags if f)


def verdict(calib: dict, per_seed: list[dict]) -> dict:
    n = len(per_seed)
    p1_flags = [s["p1"]["ok"] for s in per_seed]
    p2_flags = [s["p2"]["ok"] for s in per_seed]
    p2_tau_only = [all(r["ok_tau"] for r in s["p2"]["by_eta"].values()) for s in per_seed]
    p2_ret_only = [all(r["ok_retention"] for r in s["p2"]["by_eta"].values()) for s in per_seed]
    p3a_flags = [s["p3a"]["ok"] for s in per_seed]
    p3b_flags = [s["p3b"]["ok"] for s in per_seed]
    p3c_flags = [s["p3c"]["ok"] for s in per_seed]
    gate_flags = [s["p3a"]["gate_ok"] for s in per_seed]
    nullb_flags = [s["p2"]["null_b_ok"] for s in per_seed]
    doublings = [s["p3b"]["doubling_4096_8192"] for s in per_seed]

    # P1 : distinguer quelle observable claque (moyenne vs demi-vie).
    p1_mean_bad = []
    p1_half_bad = []
    for s in per_seed:
        bad_mean = any(not (BANDS["p1_mean_lo"] <= r["mean_ratio"] <= BANDS["p1_mean_hi"])
                       for r in s["p1"]["ladder"].values())
        bad_half = any(not (BANDS["p1_halflife_lo"] <= r["halflife_ratio"] <= BANDS["p1_halflife_hi"])
                       for r in s["p1"]["ladder"].values())
        p1_mean_bad.append(bad_mean)
        p1_half_bad.append(bad_half)

    checks = {
        "P1_lifetime_law": _count(p1_flags) >= n - 1,
        "P2_dual_effect_linked": _count(p2_flags) >= n - 1,
        "P3a_fermi_linear": _count(p3a_flags) >= n,          # 5/5 scellé
        "P3b_blob_quadratic": _count(p3b_flags) >= n - 1,
        "P3c_regime_dissociation": _count(p3c_flags) >= n - 1,
        "null_a_instrument": bool(calib.get("null_a_ok")),
        "null_b_control_neutral": _count(nullb_flags) >= n,
        "door_linearity_cross": _count(gate_flags) >= n,
    }
    if not checks["null_a_instrument"]:
        outcome = ("NON_CONCLUSIF_INSTRUMENT (null a : demi-largeur Wilson > 0.005 "
                   "à M calibré sur les graines 11/22/33)")
    elif not checks["door_linearity_cross"]:
        outcome = ("NON_CONCLUSIF_INSTRUMENT (porte : croisés/propres > 10⁻⁶ en Fermi — "
                   "l'approximation dipolaire ne tient pas sur ce réseau)")
    elif not checks["null_b_control_neutral"]:
        outcome = "NON_CONCLUSIF (null b : le contrôle b = 0.5 n'est pas neutre)"
    elif all(checks[c] for c in ("P1_lifetime_law", "P2_dual_effect_linked",
                                 "P3a_fermi_linear", "P3b_blob_quadratic",
                                 "P3c_regime_dissociation")):
        outcome = "SUPPORTED"
    elif _count(p1_mean_bad) >= 3 and any(
            abs(r["mean_ratio"] - 1.0) > BANDS["refuted_p1_mean"]
            for s in per_seed for r in s["p1"]["ladder"].values()):
        outcome = "REFUTED (P1 : la loi de vie n'est pas fidèle — τ̂ hors de ±10 %)"
    elif _count(p1_half_bad) >= 3:
        lo, hi = BANDS["refuted_p1_halflife"]
        if any(not (lo <= r["halflife_ratio"] <= hi)
               for s in per_seed for r in s["p1"]["ladder"].values()):
            outcome = "REFUTED (P1 : la demi-vie empirique n'est pas ln2·τ — horloge non exponentielle)"
    elif _count([t and not r for t, r in zip(p2_tau_only, p2_ret_only)]) >= 3:
        outcome = ("REFUTED (P2 : τ raccourci SANS lavage du biais — le couple (τ, "
                   "masquage) est rompu, la part d'E_G ne lie pas les deux)")
    elif _count([r and not t for t, r in zip(p2_tau_only, p2_ret_only)]) >= 3:
        outcome = ("REFUTED (P2 : lavage du biais SANS raccourcissement de τ — "
                   "le couple (τ, masquage) est rompu dans l'autre sens)")
    elif _count([d < BANDS["refuted_blob_doubling_max"] for d in doublings]) >= 3:
        outcome = "REFUTED (P3b : le blob est ~linéaire — les régimes ne se séparent pas)"
    else:
        outcome = "NON_CONCLUSIF (une prédiction sous sa bande sans cassure dans le sens refuté)"
    return {"verdict": outcome, "checks": checks}


# ---------------------------------------------------------------------------
#  CLI.
# ---------------------------------------------------------------------------
def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seeds", type=int, nargs="+", default=list(TEST_SEEDS))
    parser.add_argument("--m-ens", type=int, default=None,
                        help="si omis : calibration scellée (graines 11/22/33) puis gel")
    parser.add_argument("--pilot", action="store_true",
                        help="diagnostic une graine (ni calibration ni verdict)")
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args(argv)

    if args.pilot:
        diag = run_seed(555, 20_000)
        print(json.dumps({"pilot_seed": 555, **diag}, indent=2, ensure_ascii=False))
        return 0

    calib = calibrate() if args.m_ens is None else None
    m_ens = args.m_ens if args.m_ens is not None else calib["m_selected"]
    if m_ens is None:
        result = {"frozen": {"m_ens": None}, "calibration": calib,
                  "verdict": verdict(calib, [])}
        text = json.dumps(result, indent=2, ensure_ascii=False)
        if args.out:
            args.out.write_text(text, encoding="utf-8")
            print(f"written: {args.out}")
        print(json.dumps(result["verdict"], indent=2, ensure_ascii=False))
        return 0
    runs = [run_seed(s, m_ens) for s in args.seeds]
    result = {
        "frozen": {
            "G": G, "hbar": HBAR, "m_carbon_kg": M_CARBON, "a_carbon_m": A_CARBON,
            "m_tubulin_kg": M_TUBULIN, "n_carbon": N_CARBON, "e_carbon_J": E_CARBON,
            "diam_fermi_m": DIAM_FERMI, "hardcore_fermi_m": HARDCORE_FERMI,
            "k_fermi": list(K_FERMI), "diam_blob_m": DIAM_BLOB,
            "hardcore_blob_m": HARDCORE_BLOB, "k_blob": list(K_BLOB),
            "d_blob_m": D_BLOB, "d_fermi_m": D_FERMI,
            "tau_ladder_ms": list(TAU_LADDER_MS), "eta_grid": list(ETA_GRID),
            "bias_grid": list(BIAS_GRID), "m_ens": m_ens, "seeds": list(args.seeds),
            "seal": "docs/ict/penrose-orch-or-pre-enregistrement.md (v1 + amendement v2 2026-11-20)",
        },
        "calibration": calib,
        "runs": runs,
        "confrontation_source": confrontation_source(),
        "verdict": verdict(calib or {"null_a_ok": True, "m_selected": m_ens}, runs),
    }
    text = json.dumps(result, indent=2, ensure_ascii=False)
    if args.out:
        args.out.write_text(text, encoding="utf-8")
        print(f"written: {args.out}")
    print(json.dumps(result["verdict"], indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
