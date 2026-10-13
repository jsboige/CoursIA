"""Case 16 — alertness tonique ⟂ saillance phasique (iceberg #8182, Metzinger MPE 2020).

Exécution du pré-enregistrement ``docs/ict/metzinger-mpe-pre-enregistrement.md``
(commit 01f79291, PR #17159), scellé AVANT ce banc — l'antériorité repose sur la
relation de parenté des commits (leçon case 8c). Amendement pré-exécution v1 → v2
(§6bis du pré-enregistrement) : le bras phasique v1 plafonnait structurellement
sous la bande P3 ; re-spécifié en compétition inter-contenus à appariement par
contenu moyen, AVANT toute exécution. Les bandes P1/P2/P3, graines et portes
sont inchangées.

La thèse testée (lecture grade C de Metzinger 2020, §3-§4) : l'expérience
phénoménale minimale est un modèle prédictif de la vigilance tonique — un gain
de disponibilité **lent, global, sans contenu** (« preparatory to treat and
respond », Posner cité par Metzinger) — dont la propriété structurelle est la
**non-partition** de l'espace épistémique (« the as-yet-unpartitioned nature of
this space », l.1234) ; par contraste, l'alerte phasique est orientée-contenu et
dirigée par la saillance (§3.2). Dissociation substrat : *l'attente de
connaissance amplifie sans sélectionner ; la saillance sélectionne sans être une
attente*.

Modèle
------
K canaux ; N consommateurs, chacun lisant un sous-ensemble stable S_j
(|S_j| = s) via lectures bruitées ``l_jk = a_k * b_k + eps``. Contenu **unicast** :
b ∈ {±1}^K portant son signal (amplitude 1.0) sur un seul canal dominant, 0
ailleurs. Adoption :

    A_j = sum_{k in S_j} (l_jk * b_k) / sigma_read,   adopt ⟺ A_j > theta_eff

Le même tirage de bruit sert TOUS les bras d'une graine (appariement par
paires, variance réduite) ; en mode compétition les adoptions sont évaluées par
contenu indépendamment (simplification déclarée du pré-enregistrement).

Bras :

* tonique τ bas : theta_eff = theta pour tous (aucune modulation) ;
* tonique τ haut : theta_eff = theta - Delta_to pour TOUS les consommateurs —
  τ ne lit jamais le contenu injecté, ni son canal (le gain de disponibilité) ;
* phasique : compétition — deux contenus par essai (canaux dominants distincts),
  le module booste le contenu au canal dominant le plus saillant (saillance
  intrinsèque s_k par canal, tirée une fois par graine, ordre stable) : pour la
  seule évaluation du contenu gagnant, theta_eff = theta - Delta_ph pour les
  consommateurs lisant son canal ; le perdant est évalué au seuil nu.
  Appariement par contenu moyen (le module ne sert qu'un contenu sur deux) :
  ``Delta_ph = 2 * Delta_to * N / N_lecteurs(k_gagnant)`` ;
* contrôle mécanique : « tonique avec Delta_to = 0 » contre « aucune
  modulation » — égalité exacte attendue sur la même trace (parade aux bugs de
  pipeline, analogue du D({tout}) = 0 de la case 14).

Prédictions scellées (graines test (0, 1, 7, 42, 99), M paires par graine) :

* P1 — gain de disponibilité : R_alert = propa(τ haut)/propa(τ bas), médiane
  5 graines ∈ [1.2, 3.0] ;
* P2 — non-partition : g_k = propa_k(τ haut)/propa_k(τ bas),
  max_k g_k / min_k g_k ≤ 1.25 sur ≥ 4/5 graines ;
* P3 — double dissociation : le module phasique au même budget hiérarchise,
  max_k g_k / min_k g_k ≥ 2.0 sur ≥ 4/5 graines ;
* contrôle mécanique : égalité exacte bas/ctrl sur 5/5 graines ;
* portes instrumentales (leçon cases 8b/8c) : propa(τ bas) < 0.05 ou
  propa(τ haut) > 0.95 sur ≥ 3/5 graines → NON_CONCLUSIF_INSTRUMENT ;
* Null (b) : phasique non-hiérarchisé (< 2.0 sur ≥ 3/5 graines) →
  NON_CONCLUSIF_INSTRUMENT.

Calibration gelée avant le run principal (graines (11, 22, 33), disjointes des
graines de test — pattern eps_self case 4) : theta visant propa(τ bas) ≈ 0.25,
Delta_to visant R_alert(tonique) ∈ [1.4, 1.8]. Résultats figés ci-dessous
(THETA, DELTA_TO) ; le runner principal ne relit jamais la calibration.

References
----------
T. Metzinger, « Minimal phenomenal experience: Meditation, tonic alertness, and
the phenomenology of "pure" consciousness », Philosophy and the Mind Sciences
1(I)7 (2020), DOI 10.33766/jphims.1128. Pré-enregistrement :
``docs/ict/metzinger-mpe-pre-enregistrement.md`` (case 16 de
``docs/ict/dissociations-matrix.md``).
"""

from __future__ import annotations

import argparse
import json

import numpy as np

# --- Paramètres du jouet (scellés par l'amendement v2, §6bis.4) ---
K = 4                # canaux
N_CONSUMERS = 48     # consommateurs
S_READS = 2          # canaux lus par consommateur (stables par graine)
SIGMA_READ = 0.60    # bruit de lecture
AMP_DOMINANT = 1.0   # amplitude du canal dominant (contenu unicast)

# Constantes de mesure scellées par le pré-enregistrement.
SEEDS_TEST = (0, 1, 7, 42, 99)
SEEDS_CALIB = (11, 22, 33)
M_PAIRS = 200        # paires de contenus par graine (2*M_PAIRS contenus mesurés)

# Bandes scellées (P1/P2/P3, portes) — ne jamais recalibrer après mesure.
BAND_R_ALERT = (1.2, 3.0)
BAND_UNIFORMITY = 1.25   # tonique : max_k g_k / min_k g_k <=
BAND_HIERARCHY = 2.0     # phasique : max_k g_k / min_k g_k >=
GATE_FLOOR = 0.05        # propa(tau bas) <
GATE_CEIL = 0.95         # propa(tau haut) >
GATE_MIN_SEEDS = 3       # graines déclenchant une porte

# Calibration gelée (graines 11/22/33 via --calibrate, figée avant le run
# principal — mesure du 2026-09-21 : propa(tau bas) médiane 0.245, R_alert
# médiane 1.603 sur les graines de calibration uniquement).
THETA = 2.0
DELTA_TO = 0.7


def _draw_grain(rng: np.random.Generator, m_pairs: int) -> dict:
    """Tire la géométrie et les traces d'une graine : lectures, contenus, bruit.

    Tout ce qui suit est figé pour la graine : sous-ensembles lus, saillance
    par canal, 2*m_pairs contenus (paires à canaux dominants distincts) et le
    bruit de lecture partagé par tous les bras.
    """
    reads_idx = np.array([rng.choice(K, size=S_READS, replace=False)
                          for _ in range(N_CONSUMERS)])
    salience = rng.permutation(np.arange(1, K + 1)).astype(float)

    bits = rng.choice((-1.0, 1.0), size=(2 * m_pairs, K))
    dom = np.empty(2 * m_pairs, dtype=int)
    for i in range(m_pairs):
        k1, k2 = rng.choice(K, size=2, replace=False)
        dom[2 * i], dom[2 * i + 1] = k1, k2

    noise = rng.normal(0.0, SIGMA_READ, size=(2 * m_pairs, N_CONSUMERS, S_READS))
    return {"reads_idx": reads_idx, "salience": salience,
            "bits": bits, "dom": dom, "noise": noise}


def _scores(grain: dict) -> np.ndarray:
    """Scores d'adoption de chaque contenu pour chaque consommateur.

    A[i, j] = sum_{k in S_j} (l_ijk * b_ik) / sigma_read, shape (2m, N).
    """
    reads_idx = grain["reads_idx"]                       # (N, s)
    b_lu = grain["bits"][:, reads_idx]                   # (2m, N, s)
    amp = (np.arange(K)[None, :] == grain["dom"][:, None]) * AMP_DOMINANT
    amp_lu = amp[:, reads_idx]                           # (2m, N, s)
    lectures = amp_lu * b_lu + grain["noise"]
    return (lectures * b_lu).sum(axis=2) / SIGMA_READ


def _propa_per_channel(adoption: np.ndarray, dom: np.ndarray) -> np.ndarray:
    """propa par canal dominant : fraction moyenne de consommateurs adoptant."""
    out = np.zeros(K)
    for k in range(K):
        mask = dom == k
        if mask.any():
            out[k] = adoption[mask].mean()
    return out


def run_seed(seed: int, m_pairs: int, theta: float, delta_to: float) -> dict:
    """Tous les bras d'une graine sur la même trace."""
    rng = np.random.default_rng(seed)
    grain = _draw_grain(rng, m_pairs)
    scores = _scores(grain)
    reads_idx, salience, dom = grain["reads_idx"], grain["salience"], grain["dom"]

    # --- Bras toniques ---
    propa_bas = _propa_per_channel(scores > theta, dom)
    propa_haut = _propa_per_channel(scores > (theta - delta_to), dom)
    # Contrôle mécanique : la voie « tonique avec Delta nul » (soustraction de 0)
    # doit reproduire EXACTEMENT la voie « aucune modulation ».
    propa_ctrl = _propa_per_channel(scores > (theta - 0.0), dom)
    ctrl_mechanical = bool(np.array_equal(propa_ctrl, propa_bas))

    r_alert = float(propa_haut.sum() / propa_bas.sum()) if propa_bas.sum() else float("inf")
    g_tonic = np.divide(propa_haut, propa_bas,
                        out=np.full(K, np.nan), where=propa_bas > 0)
    uniformity = (float(np.nanmax(g_tonic) / np.nanmin(g_tonic))
                  if not np.isnan(g_tonic).all() else float("nan"))

    # --- Bras phasique : compétition par paires ---
    # Base (module inactif) : seuil nu pour tous.
    propa_base = _propa_per_channel(scores > theta, dom)

    # Module actif : par paire, le contenu au canal le plus saillant est boosté
    # (seuil abaissé de Delta_ph pour les consommateurs lisant SON canal),
    # l'autre est évalué au seuil nu.
    reads_mask = np.zeros((N_CONSUMERS, K), dtype=bool)
    for j in range(N_CONSUMERS):
        reads_mask[j, reads_idx[j]] = True
    n_lect = reads_mask.sum(axis=0)

    theta_eff = np.full((2 * m_pairs, N_CONSUMERS), theta)
    for i in range(m_pairs):
        d1, d2 = dom[2 * i], dom[2 * i + 1]
        i_win = 2 * i if salience[d1] >= salience[d2] else 2 * i + 1
        k_win = dom[i_win]
        delta_ph = 2.0 * delta_to * N_CONSUMERS / max(int(n_lect[k_win]), 1)
        theta_eff[i_win][reads_mask[:, k_win]] = theta - delta_ph

    propa_active = _propa_per_channel(scores > theta_eff, dom)
    g_phasic = np.divide(propa_active, propa_base,
                         out=np.full(K, np.nan), where=propa_base > 0)
    hierarchy = (float(np.nanmax(g_phasic) / np.nanmin(g_phasic))
                 if not np.isnan(g_phasic).all() else float("nan"))

    return {
        "propa_bas": propa_bas.tolist(),
        "propa_haut": propa_haut.tolist(),
        "r_alert": r_alert,
        "g_tonic": g_tonic.tolist(),
        "uniformity": uniformity,
        "ctrl_mechanical": ctrl_mechanical,
        "propa_phasic_base": propa_base.tolist(),
        "propa_phasic_active": propa_active.tolist(),
        "g_phasic": g_phasic.tolist(),
        "hierarchy": hierarchy,
        "salience_rank": salience.tolist(),
    }


def calibrate() -> dict:
    """Calibration sur graines disjointes (11/22/33) : theta, delta_to.

    Cible : propa(tau bas) ≈ 0.25 (fenêtre [0.15, 0.35]) et
    R_alert(tonique) ∈ [1.4, 1.8] au milieu de la bande P1 scellée.
    """
    grid_theta = np.arange(1.60, 2.301, 0.05)
    grid_delta = np.arange(0.40, 0.901, 0.05)
    best = None
    for th in grid_theta:
        for dl in grid_delta:
            base, rs = [], []
            for s in SEEDS_CALIB:
                d = run_seed(s, M_PAIRS // 4, float(th), float(dl))
                base.append(float(np.mean(d["propa_bas"])))
                rs.append(d["r_alert"])
            med_r, med_b = float(np.median(rs)), float(np.median(base))
            if 1.4 <= med_r <= 1.8 and 0.15 <= med_b <= 0.35:
                cost = abs(med_r - 1.6) + abs(med_b - 0.25)
                if best is None or cost < best[0]:
                    best = (cost, float(th), float(dl), med_b, med_r)
    if best is None:
        raise SystemExit("calibration: aucune (theta, delta) dans la fenetre visee")
    return {"theta": best[1], "delta_to": best[2],
            "propa_bas_median": best[3], "r_alert_median": best[4], "cost": best[0]}


def run_protocol(theta: float = THETA, delta_to: float = DELTA_TO) -> dict:
    """Run principal : graines test, constantes gelées THETA / DELTA_TO."""
    seeds = [run_seed(s, M_PAIRS, theta, delta_to) for s in SEEDS_TEST]

    r_alerts = [d["r_alert"] for d in seeds]
    uniform = [d["uniformity"] for d in seeds]
    hier = [d["hierarchy"] for d in seeds]
    propa_bas = [float(np.mean(d["propa_bas"])) for d in seeds]
    propa_haut = [float(np.mean(d["propa_haut"])) for d in seeds]
    ctrl_ok = all(d["ctrl_mechanical"] for d in seeds)

    n_floor = sum(p < GATE_FLOOR for p in propa_bas)
    n_ceil = sum(p > GATE_CEIL for p in propa_haut)
    gate = (n_floor >= GATE_MIN_SEEDS) or (n_ceil >= GATE_MIN_SEEDS)

    med_r = float(np.median(r_alerts))
    p1 = BAND_R_ALERT[0] <= med_r <= BAND_R_ALERT[1]
    p2 = sum(u <= BAND_UNIFORMITY for u in uniform) >= 4
    p3 = sum(h >= BAND_HIERARCHY for h in hier) >= 4
    null_b = sum(h < BAND_HIERARCHY for h in hier) >= GATE_MIN_SEEDS

    if gate:
        verdict = "NON_CONCLUSIF_INSTRUMENT (porte plancher/plafond)"
    elif null_b:
        verdict = "NON_CONCLUSIF_INSTRUMENT (null b : phasique non-hierarchise)"
    elif p1 and p2 and p3 and ctrl_ok:
        verdict = "SUPPORTED"
    else:
        verdict = "NOT_SUPPORTED"

    return {
        "case": "16-tonic-alertness-vs-phasic-salience",
        "theta": theta, "delta_to": delta_to,
        "seeds": list(SEEDS_TEST), "m_pairs": M_PAIRS,
        "r_alert_by_seed": r_alerts,
        "r_alert_median": med_r,
        "uniformity_by_seed": uniform,
        "hierarchy_by_seed": hier,
        "propa_bas_mean_by_seed": propa_bas,
        "propa_haut_mean_by_seed": propa_haut,
        "gate_floor_seeds": n_floor,
        "gate_ceil_seeds": n_ceil,
        "ctrl_mechanical_ok": ctrl_ok,
        "p1": bool(p1), "p2": bool(p2), "p3": bool(p3),
        "verdict": verdict,
        "bands": {"r_alert": list(BAND_R_ALERT), "uniformity_max": BAND_UNIFORMITY,
                  "hierarchy_min": BAND_HIERARCHY},
    }


def main() -> None:
    ap = argparse.ArgumentParser(description="Case 16 - tonic alertness vs phasic salience")
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
