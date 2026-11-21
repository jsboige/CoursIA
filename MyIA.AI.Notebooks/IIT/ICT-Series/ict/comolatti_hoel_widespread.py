"""Case 26 de la veille ICT (#8182) : l'emergence causale est-elle repandue ?

Banc de mesure preregistre (docs/ict/comolatti-hoel-widespread-pre-enregistrement.md,
scelle au commit 0f3a704b575 AVANT l'ecriture de ce module) pour la source primaire :

    Milan Comolatti, Erik P. Hoel, "Causal emergence is widespread across
    measures of causation", Entropy (prepublication receptive), 7 fevrier 2022.
    Copie archivee au gisement (rayon Probabilistic), identite verifiee p. 1.

These du papier : toute mesure de causation se decompose en primitives causales
(suffisance / necessite, generalisees en determinisme / degenerescence, p. 9) ;
le coarse-graining deplace donc TOUTES les mesures ensemble -- l'emergence
causale n'est pas un artefact du choix d'EI.

Organ-first : toute valeur det/deg/EI et tout coarse-graining vient de l'organe
natif ``ict.causal_emergence`` (``causal_profile`` + ``partition_profile`` avec
``macro_tpm``), INVOQUE jamais reimplimente. Les substrats S1 (systeme calibre
Fig. 4 de Hoel 2013) et S2 (temoin COPY bruitees) reprennent les constructeurs
PUBLICS du banc case 25 (``ict.hoel_causal_emergence``). Ce module apporte ce
que l'organe n'a pas :

  1. le PANEL des mesures de causation sur TPM nue (pp. 5-7) : Eells, Galton,
     Suppes, Suppes II, Lewis, Cheng -- avec les identifications Pearl
     scellees au prereg (PNS = Eells, PN = Lewis, PS = Cheng, p. 7) ;
  2. la double implementation de chaque mesure (formule directe imprimee vs
     substitution des primitives suff/nec) pour la porte G1 ;
  3. l'agregation systeme max-entropie scellee (esperence jointe sous P(c,e),
     support renormalise pour les mesures ratio) ;
  4. la reconstruction bipartite bornee S3 (seize micro-etats en deux groupes,
     cible principale = complement, bruit symetrique vers le groupe cible,
     grille eps scellee ; macro = porte NOT deterministe non degenereree
     independante de eps, pp. 10/14) ;
  5. les hypotheses H1/H1b/H2/H3/H4 et portes G1-G4, verdicts bornes.

Instrument exact : TPM enumerees, aucun Monte-Carlo (``stochastic: false``).
Conventions d'indexation : heritees du banc case 25 (bit de poids fort =
element 0 ; ``groups`` = partition exhaustive de ``range(2**k)``).
"""

from __future__ import annotations

import numpy as np

from ict.causal_emergence import causal_profile, partition_profile, validate_tpm
from ict.hoel_causal_emergence import (
    calibrate_fig4,
    element_pair_groups,
    is_legal_grouping,
    legal_groupings_4ind,
    tpm_from_gates,
)

#: mesures du panel (liste close du prereg §4) : les cinq sensibles a la
#: degenerescence + Cheng (saturee quand la cause est entierement suffisante)
PANEL_SENSITIVE = ("eells", "galton", "suppes", "suppes2", "lewis")
PANEL_ALL = PANEL_SENSITIVE + ("cheng",)

#: grille de bruit S3 scellee (prereg §4) et bruit du temoin S2
EPS_GRID = (0.0, 0.25, 0.5, 0.75, 1.0)
WITNESS_NOISE = 0.1

#: tolerance de la porte G1 (accord direct/primitives)
G1_TOL = 1e-12


# ------------------------------------------------------------------ primitives
def _quantities(tpm: np.ndarray) -> dict:
    """Grandeurs causales sous intervention max-entropie sur les causes.

    suff[c,e] = P(e|c) = tpm[c,e]
    pec[c,e]  = P(e|C\\c) = (somme de colonne - tpm[c,e]) / (n-1)
    nec[c,e]  = 1 - P(e|C\\c)          (primitif "necessite" du papier)
    necd[c,e] = P(e|C) = marginal      (necessite dague, pour Suppes)
    """
    m = validate_tpm(tpm)
    n = m.shape[0]
    colsum = m.sum(axis=0)
    marginal = colsum / n
    pec = (colsum[None, :] - m) / (n - 1)
    return {
        "suff": m,
        "pec": pec,
        "nec": 1.0 - pec,
        "necd": np.broadcast_to(marginal, m.shape),
    }


def cs_direct(tpm: np.ndarray) -> dict:
    """CS(c,e) par formule directe imprimee (pp. 5-7), sous max-entropie.

    P(c) = 1/n et P(C\\c) = (n-1)/n pour toute transition (max-entropie).
    Les mesures ratio valent NaN hors de leur support (denominateur nul).
    """
    q = _quantities(tpm)
    n = validate_tpm(tpm).shape[0]
    diff = q["suff"] - q["pec"]
    with np.errstate(divide="ignore", invalid="ignore"):
        return {
            "eells": diff,
            "galton": (1.0 / n) * ((n - 1.0) / n) * diff,
            "suppes": q["suff"] - q["necd"],
            "suppes2": np.where(q["necd"] > 0, q["suff"] / q["necd"], np.nan),
            "lewis": np.where(q["suff"] > 0, diff / q["suff"], np.nan),
            "cheng": np.where(q["pec"] < 1.0, diff / (1.0 - q["pec"]), np.nan),
        }


def cs_primitives(tpm: np.ndarray) -> dict:
    """CS(c,e) par SUBSTITUTION des primitives (seconde implementation G1).

    Eells = suff + nec - 1 ; Galton = P(c)P(C\\c)(suff + nec - 1) ;
    Suppes = suff - necd ; Suppes II = suff/necd ;
    Lewis (PN) = (suff + nec - 1)/suff ; Cheng (PS) = (suff + nec - 1)/nec.
    """
    q = _quantities(tpm)
    n = validate_tpm(tpm).shape[0]
    base = q["suff"] + q["nec"] - 1.0
    with np.errstate(divide="ignore", invalid="ignore"):
        return {
            "eells": base,
            "galton": (1.0 / n) * ((n - 1.0) / n) * base,
            "suppes": q["suff"] - q["necd"],
            "suppes2": np.where(q["necd"] > 0, q["suff"] / q["necd"], np.nan),
            "lewis": np.where(q["suff"] > 0, base / q["suff"], np.nan),
            "cheng": np.where(q["nec"] > 0, base / q["nec"], np.nan),
        }


def system_values(tpm: np.ndarray) -> dict:
    """Agregation systeme scellee : esperence jointe sous P(c,e) = tpm/n,
    support renormalise pour les mesures ratio (prereg §4, instrument 3)."""
    m = validate_tpm(tpm)
    w = m / m.shape[0]
    direct, prim = cs_direct(m), cs_primitives(m)
    out: dict = {}
    max_dev = 0.0
    for name in PANEL_ALL:
        d, p = direct[name], prim[name]
        mask = ~np.isnan(d) & ~np.isnan(p)
        if mask.any():
            max_dev = max(max_dev, float(np.max(np.abs(d[mask] - p[mask]))))
        ww = w[mask]
        tot = float(ww.sum())
        out[name] = float((ww * d[mask]).sum() / tot) if tot > 0 else None
    out["g1_max_dev"] = max_dev
    return out


# ------------------------------------------------------------------ substrats
def self_copy_tpm(k: int, noise: float) -> np.ndarray:
    """TPM du temoin S2 : k elements COPY d'eux-memes, bruites, independants.

    Construction identique au temoin H4 du banc case 25 (croisee en test).
    """
    n = 2 ** k
    tpm = np.zeros((n, n))
    for s in range(n):
        for t in range(n):
            hamming = bin(s ^ t).count("1")
            tpm[s, t] = (1.0 - noise) ** (k - hamming) * noise ** hamming
    return validate_tpm(tpm)


def bipartite_tpm(eps: float) -> np.ndarray:
    """TPM micro de la reconstruction bipartite bornee S3 (prereg §4).

    Seize micro-etats : groupe A = {0000..0111} (bit de tete 0), groupe B =
    complement. Chaque etat vise sa cible principale m(c) = complement
    (bijection A <-> B, la transition principale 0000->1111 du papier) ;
    bruit symetrique de sortie vers le groupe cible :
    P(c -> m(c)) = 1 - eps + eps/8, P(c -> autre etat du groupe cible) = eps/8.
    """
    n = 16
    tpm = np.zeros((n, n))
    for c in range(n):
        targets = range(8, n) if c < 8 else range(0, 8)
        for e in targets:
            tpm[c, e] = (1.0 - eps + eps / 8.0) if e == 15 - c else eps / 8.0
    return validate_tpm(tpm)


BIPARTITE_GROUPS = [list(range(0, 8)), list(range(8, 16))]


# ------------------------------------------------------------------ mesure commune
def delta_row(micro_tpm: np.ndarray, groups: list) -> dict:
    """Une ligne de mesure : panel micro vs macro + primitives de l'organe.

    Retourne les sys par mesure aux deux echelles, les deltas, le mouvement
    net des primitives (Ddet - Ddeg de l'organe) et l'EI organe.
    """
    micro_prof = causal_profile(micro_tpm)
    macro_prof = partition_profile(micro_tpm, groups)
    micro_sys = system_values(micro_tpm)
    macro_sys = system_values(macro_prof["macro_tpm"])
    deltas = {
        m: (macro_sys[m] - micro_sys[m])
        for m in PANEL_ALL
        if micro_sys[m] is not None and macro_sys[m] is not None
    }
    return {
        "EI_micro": micro_prof["effective_information"],
        "EI_macro": macro_prof["effective_information"],
        "deg_micro": micro_prof["degeneracy"],
        "CE_EI": (macro_prof["effective_information"]
                  - micro_prof["effective_information"]),
        "d_det_minus_d_deg": ((macro_prof["determinism"] - micro_prof["determinism"])
                              - (macro_prof["degeneracy"] - micro_prof["degeneracy"])),
        "micro_sys": micro_sys,
        "macro_sys": macro_sys,
        "deltas": deltas,
        "g1_max_dev": max(micro_sys["g1_max_dev"], macro_sys["g1_max_dev"]),
        # ligne EI = organe : identite EI = log2(n)(det - deg) (p. 9)
        "ei_identity_dev": max(
            abs(micro_prof["effective_information"]
                - np.log2(micro_tpm.shape[0])
                * (micro_prof["determinism"] - micro_prof["degeneracy"])),
            abs(macro_prof["effective_information"]
                - np.log2(len(groups))
                * (macro_prof["determinism"] - macro_prof["degeneracy"])),
        ),
    }


# ------------------------------------------------------------------ Spearman
def _ranks(values: list) -> list:
    """Rangs avec ex aequo moyennes (Spearman aux ties)."""
    order = sorted(range(len(values)), key=lambda i: values[i])
    ranks = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i
        while j + 1 < len(order) and values[order[j + 1]] == values[order[i]]:
            j += 1
        avg = (i + j) / 2.0 + 1.0
        for kk in range(i, j + 1):
            ranks[order[kk]] = avg
        i = j + 1
    return ranks


def spearman(xs: list, ys: list) -> float:
    """Correlation de rang de Spearman (Pearson sur les rangs)."""
    rx, ry = _ranks(xs), _ranks(ys)
    mx, my = sum(rx) / len(rx), sum(ry) / len(ry)
    num = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    den = (sum((a - mx) ** 2 for a in rx) * sum((b - my) ** 2 for b in ry)) ** 0.5
    return num / den if den > 0 else 0.0


# ------------------------------------------------------------------ batterie
def run_all() -> dict:
    """Batterie preregistree complete : portes G1-G4, hypotheses H1/H1b/H2/
    H3/H4, verdict global borne. Sortie = JSON de resultats."""
    gates_out: dict = {}

    # ---- S1 : systeme calibre Fig. 4 (case 25, Hermes-verifie)
    cal4 = calibrate_fig4()
    s1_tpm = tpm_from_gates(6, cal4["gates"], noise=0.0)
    s1_groups = element_pair_groups(6, [(0, 1), (2, 3), (4, 5)])
    s1 = delta_row(s1_tpm, s1_groups)

    # ---- S2 : temoin (COPY bruitees independantes)
    s2_tpm = self_copy_tpm(4, WITNESS_NOISE)
    s2_rows = []
    for label, groups in legal_groupings_4ind():
        s2_rows.append({"label": label, **delta_row(s2_tpm, groups)})

    # ---- S3 : reconstruction bipartite bornee (grille eps)
    s3_rows = []
    for eps in EPS_GRID:
        s3_rows.append({"eps": eps, **delta_row(bipartite_tpm(eps), BIPARTITE_GROUPS)})

    # ---- G1 : accord des deux implementations sur TOUTES les transitions mesurees
    g1_devs = [s1["g1_max_dev"]] + [r["g1_max_dev"] for r in s2_rows + s3_rows]
    gates_out["G1_dual_impl"] = {"ok": bool(max(g1_devs) < G1_TOL),
                                 "max_dev": max(g1_devs)}

    # ---- G2 : cas analytiques (formes fermees scellees au prereg)
    g2_rows = []
    for n in (4, 8):
        cycle = np.zeros((n, n))
        for i in range(n):
            cycle[i, (i + 1) % n] = 1.0
        sys = system_values(cycle)
        expect = {"eells": 1.0, "galton": (n - 1) / n ** 2, "suppes": 1 - 1 / n,
                  "suppes2": float(n), "lewis": 1.0, "cheng": 1.0}
        g2_rows.append({"n": n, "sys": sys,
                        "ok": all(abs(sys[m] - v) < 1e-9 for m, v in expect.items())})
    uniform = np.full((6, 6), 1 / 6)
    sys_u = system_values(uniform)
    uni_expect = {"eells": 0.0, "galton": 0.0, "suppes": 0.0, "suppes2": 1.0,
                  "lewis": 0.0, "cheng": 0.0}
    g2_rows.append({"n": 6, "uniform": True, "sys": sys_u,
                    "ok": all(abs(sys_u[m] - v) < 1e-9 for m, v in uni_expect.items())})
    gates_out["G2_analytic"] = {"ok": all(r["ok"] for r in g2_rows),
                                "rows": g2_rows}

    # ---- G3 : calibrage case 25 (criteres scelles au prereg §5) + ligne EI
    g3_calib = (cal4 is not None
                and abs(s1["EI_micro"] - 2.4338) < 0.001
                and abs(s1["EI_macro"] - 3.0) < 1e-9
                and abs(s1["deg_micro"] - 0.5944) < 0.001)
    ei_devs = [s1["ei_identity_dev"]] + [r["ei_identity_dev"] for r in s2_rows + s3_rows]
    gates_out["G3_calibration"] = {
        "ok": bool(g3_calib and max(ei_devs) < 1e-9),
        "EI_micro": s1["EI_micro"], "EI_macro": s1["EI_macro"],
        "deg_micro": s1["deg_micro"],
        "ei_identity_max_dev": max(ei_devs),
    }

    # ---- G4 : garde de legalite (heritee du banc case 25)
    legal_map = element_pair_groups(4, [(0, 1), (2, 3)])
    illegal = [[0, 1], [2, 3]]
    g4 = (is_legal_grouping(legal_map, [(0, 1), (2, 3)])
          and not is_legal_grouping(illegal, [(0, 1)]))
    gates_out["G4_legality"] = {"ok": bool(g4)}

    gates_ok = all(g["ok"] for g in gates_out.values())

    # ---- H1 : les cinq mesures sensibles a la degenerescence battent le macro
    h1_pos = [m for m in PANEL_SENSITIVE if s1["deltas"][m] > 0]
    h1_missed = len(PANEL_SENSITIVE) - len(h1_pos)
    h1 = ("CONFIRMEE" if h1_missed == 0
          else "PARTIEL" if h1_missed == 1 else "FALSIFIEE")

    # ---- H1b : saturation de Cheng (egalite ponctuelle exacte sur S1)
    h1b = "CONFIRMEE" if abs(s1["deltas"]["cheng"]) < 1e-12 else "FALSIFIEE"

    # ---- H2 : temoin bidirectionnel (median du panel <= 0 la ou CE_EI <= 0)
    def _median(vals):
        s = sorted(vals)
        mid = len(s) // 2
        return s[mid] if len(s) % 2 else (s[mid - 1] + s[mid]) / 2

    # population scellee : uniquement les regroupements ou l'organe donne CE <= 0
    h2_pop = [r for r in s2_rows if r["CE_EI"] <= 1e-9]
    h2_rows = []
    for r in h2_pop:
        med = _median([r["deltas"][m] for m in PANEL_ALL])
        h2_rows.append({"label": r["label"], "CE_EI": r["CE_EI"],
                        "median_dCS": med, "holds": bool(med <= 0)})
    n_hold = sum(1 for r in h2_rows if r["holds"])
    h2 = ("CONFIRMEE" if n_hold == len(h2_rows)
          else "PARTIEL" if n_hold > len(h2_rows) / 2 else "FALSIFIEE")

    # ---- H3 : Spearman(dCS_m, Ddet - Ddeg) > 0 sur tous les points mesures
    points = ([s1] + s2_rows + s3_rows)
    xs = [p["d_det_minus_d_deg"] for p in points]
    h3_rows = []
    for m in PANEL_ALL:
        rho = spearman(xs, [p["deltas"][m] for p in points])
        h3_rows.append({"measure": m, "spearman": rho, "holds": bool(rho > 0)})
    n_h3 = sum(1 for r in h3_rows if r["holds"])
    h3 = ("CONFIRMEE" if n_h3 == len(PANEL_ALL)
          else "PARTIEL" if n_h3 > len(PANEL_ALL) / 2 else "FALSIFIEE")

    # ---- H4 : coin bruite > coin propre, strict, pour chaque mesure
    clean, noisy = s3_rows[0], s3_rows[-1]
    h4_rows = [{"measure": m,
                "clean": clean["deltas"][m], "noisy": noisy["deltas"][m],
                "holds": bool(noisy["deltas"][m] > clean["deltas"][m])}
               for m in PANEL_ALL]
    n_h4 = sum(1 for r in h4_rows if r["holds"])
    h4 = ("CONFIRMEE" if n_h4 == len(PANEL_ALL)
          else "PARTIEL" if n_h4 == len(PANEL_ALL) - 1 else "FALSIFIEE")

    hyps = {
        "H1_widespread": {"verdict": h1, "positive": h1_pos,
                          "deltas": {m: s1["deltas"][m] for m in PANEL_SENSITIVE}},
        "H1b_cheng_saturation": {"verdict": h1b, "delta_cheng": s1["deltas"]["cheng"]},
        "H2_bidirectional": {"verdict": h2, "rows": h2_rows},
        "H3_primitives_explain": {"verdict": h3, "rows": h3_rows, "n_points": len(points)},
        "H4_noise_corners": {"verdict": h4, "rows": h4_rows,
                             "ei_clean": clean["CE_EI"], "ei_noisy": noisy["CE_EI"]},
    }

    verdicts = [h1, h1b, h2, h3, h4]
    if not gates_ok:
        global_verdict = "NON_CONCLUSIF"
    elif any(v == "FALSIFIEE" for v in verdicts):
        global_verdict = "REFUTE"
    elif (h1 == "CONFIRMEE" and h1b == "CONFIRMEE" and h4 == "CONFIRMEE"
          and h2 in ("CONFIRMEE", "PARTIEL") and h3 in ("CONFIRMEE", "PARTIEL")):
        global_verdict = "SOUTENU"
    else:
        global_verdict = "PARTIEL"

    return {
        "case": "26-comolatti-hoel-widespread",
        "source": ("Comolatti & Hoel 2022, Causal emergence is widespread "
                   "across measures of causation, Entropy, 2022-02-07"),
        "prereg": "docs/ict/comolatti-hoel-widespread-pre-enregistrement.md @ 0f3a704b575",
        "organ": "ict.causal_emergence (causal_profile + partition_profile), invoque",
        "stochastic": False,
        "gates": gates_out,
        "substrates": {"S1_fig4": s1, "S2_witness": s2_rows, "S3_bipartite": s3_rows},
        "hypotheses": hyps,
        "global_verdict": global_verdict,
    }


def _json_default(obj):
    if isinstance(obj, np.ndarray):
        return obj.tolist()
    return float(obj)


if __name__ == "__main__":
    import json
    import pathlib

    out = run_all()
    dest = pathlib.Path(__file__).parent / "results" / "comolatti_hoel_widespread_results.json"
    dest.write_text(json.dumps(out, indent=2, default=_json_default), encoding="utf-8")
    print(f"global_verdict: {out['global_verdict']} -> {dest}")
