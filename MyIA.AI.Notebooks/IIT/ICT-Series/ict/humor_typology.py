# -*- coding: utf-8 -*-
"""Typologie des 30 paires minimales humour/unfun (issue #14035, critere 4).

Tranche finale observationnelle : ICT-35b a mesure l'agregat des 30 paires a
la couche 12/24, ICT-35c aux profondeurs early/mid/late -- toutes deux sur le
pairing complet. Le critere 4 du protocole exige la stabilite **inter-formes**
(pun, sociale/non-topical, topical) et le critere d'acceptance des effets
rapportes avec IC et taille d'effet. Ce module porte l'annotation typologique
(figuree AVANT toute mesure par type) et les jambes d'inference additionnelles
(IC bootstrap, d de Cohen, controle familial du max |z|) -- les statistiques
de detection pre-registrees restent celles de ``humor_pairs.measure_humor_differential``.

Regle d'annotation (mecanisme comique PRINCIPAL, la connaissance requise pour
que la blague fonctionne) :

- ``pun``     : double sens lexical, phonetique ou calque de notation
               (Oct 31 == Dec 25, yield, racines, moulu, eyebrows/surprised).
- ``topical`` : la comprehension exige une reference d'ecosysteme ou de fait
               technique (null vs undefined, stack DevOps, BOM UTF-8, logs Git).
- ``sociale`` : situation humaine universelle lisible sans reference technique
               (metiers, pere Noel, cafe du bureau, plongeurs).

Les paires dont le classement se discute ( deux mecanismes reels, un
dominant retenu) sont listees dans :data:`BORDERLINE` ; la robustesse du
verdict au reclassement de ces cas est l'exercice 1 du notebook ICT-35d.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any

import numpy as np

from .humor_pairs import _common_prefix_len, _zone_vec

TYPES = ("pun", "topical", "sociale")

# Annotation figee avant mesure (c. de claim 14035, 2026-09-23).
PAIR_TYPES: dict[str, str] = {
    "joke-p02": "pun",       # Oct 31 == Dec 25 : calque de notation
    "joke-p03": "pun",       # 10 = binaire : calque de notation
    "joke-p04": "topical",   # SQL, tables : reference d'ecosysteme
    "joke-p05": "sociale",   # ingenieurs/ampoule : stereotype de metier
    "joke-p06": "pun",       # racines : double sens math/religion
    "joke-p07": "topical",   # null vs undefined : reference JS
    "joke-p08": "pun",       # UDP/savoir : double sens
    "joke-p09": "sociale",   # pere Noel/piles : situation universelle
    "joke-p10": "pun",       # moulu : double sens moulu/ecrase
    "joke-p11": "pun",       # yield : double sens coroutine/renoncer
    "joke-p12": "topical",   # stack DevOps : reference d'ecosysteme
    "joke-p13": "sociale",   # relation stable/pleurer : comedie de couple
    "joke-p14": "pun",       # palindrome/differencier : double sens
    "joke-p15": "topical",   # regex : reference technique
    "joke-p16": "sociale",   # trois savants : comedie de personnages
    "joke-p18": "topical",   # Objective-C/messages : reference technique
    "joke-p19": "pun",       # doublement : double sens
    "joke-p20": "pun",       # photon/attendre : double sens relativiste
    "joke-p21": "pun",       # matrices/hors de portee : double sens
    "joke-p22": "topical",   # chat roug/serveurs : argot d'incident
    "joke-p23": "sociale",   # plongeurs : absurdite situationnelle
    "joke-p24": "topical",   # HTML pas un langage : debat d'ecosysteme
    "joke-p25": "topical",   # logs Git : reference technique
    "joke-p26": "topical",   # debug d'avion : reference de metier technique
    "joke-p27": "pun",       # git pull/deux tu l'auras : calembour
    "joke-p28": "topical",   # Python/exceptions : reference technique
    "joke-p29": "topical",   # submodules Git : reference technique
    "joke-p30": "topical",   # UTF-8/BOM : reference technique
    "edge-04": "pun",        # eyebrows/surprised : double sens EN
    "edge-05": "pun",        # whiskey diet/lost : double sens EN
}

BORDERLINE = frozenset({
    "joke-p10",  # pun retenu (moulu), lisible aussi comme sociale (cafe boulot)
    "joke-p13",  # sociale retenu (comedie de couple), requiert aussi "compiler"
    "joke-p16",  # sociale retenu (personnages), reference scientifique reelle
    "joke-p20",  # pun retenu (attendre), presuppose aussi la relativite
    "joke-p22",  # topical retenu (argot d'incident), l'absurde animal est aussi sociale
})

MIN_PER_TYPE = 5  # plancher declare : sous 5 paires, la jambe est non concluante


def validate_typology(pairs: list[dict[str, str]]) -> None:
    """Contrat de l'annotation : couverture exacte, types connus, plancher."""
    ids = [p["id"] for p in pairs]
    annotated = set(PAIR_TYPES)
    if annotated != set(ids):
        missing = sorted(set(ids) - annotated)
        extra = sorted(annotated - set(ids))
        raise ValueError(f"annotation incoherente (manquants={missing}, extras={extra})")
    counts = {t: 0 for t in TYPES}
    for p in pairs:
        t = PAIR_TYPES[p["id"]]
        if t not in counts:
            raise ValueError(f"type inconnu {t!r} pour {p['id']}")
        counts[t] += 1
    for t, n in counts.items():
        if n < MIN_PER_TYPE:
            raise ValueError(f"type {t} sous le plancher : {n} < {MIN_PER_TYPE}")


def split_by_type(pairs: list[dict[str, str]]) -> dict[str, list[dict[str, str]]]:
    """Partition des paires par type, ordre stable (celui de ``pairs``)."""
    out: dict[str, list[dict[str, str]]] = {t: [] for t in TYPES}
    for p in pairs:
        out[PAIR_TYPES[p["id"]]].append(p)
    return out


# --------------------------------------------------------------------------- #
# Jambes d'inference additionnelles (critere d'acceptance : IC + taille d'effet)
# --------------------------------------------------------------------------- #

def zone_matrices(
    traces_path: str | Path, pairs: list[dict[str, str]]
) -> dict[str, np.ndarray]:
    """Matrices de zones (n, d_sae) humour / unfun / ctrl_edit pour ``pairs``."""
    from .sae_traces import load_traces

    tr = load_traces(traces_path)
    d_sae = int(tr["meta"]["d_sae"])
    zones = {"humour": [], "unfun": [], "ctrl_edit": []}
    for i in range(len(pairs)):
        eh = tr["prompts"][("humour", i)]
        eu = tr["prompts"][("unfun", i)]
        ec = tr["prompts"][("ctrl_edit", i)]
        k_hu = _common_prefix_len(eh["tokens"], eu["tokens"])
        k_hc = _common_prefix_len(eh["tokens"], ec["tokens"])
        zones["humour"].append(_zone_vec(eh, k_hu, d_sae))
        zones["unfun"].append(_zone_vec(eu, k_hu, d_sae))
        zones["ctrl_edit"].append(_zone_vec(ec, k_hc, d_sae))
    return {k: np.stack(v) for k, v in zones.items()}


def per_pair_deltas(zones: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    """Distances L1 par paire : differentiel humour vs null croise de 35b."""
    return {
        "delta_pair": np.abs(zones["humour"] - zones["unfun"]).sum(axis=1),
        "delta_ctrl": np.abs(zones["humour"] - zones["ctrl_edit"]).sum(axis=1),
    }


def bootstrap_mean_ic(
    x: np.ndarray, *, n_boot: int = 4000, seed: int = 42, alpha: float = 0.05
) -> dict[str, float]:
    """IC percentile bootstrap sur la moyenne + d de Cohen univaries.

    Le d de Cohen univaries (moyenne / ecart-type) repond au critere
    d'acceptance : taille d'effet rapportee avec son IC, pas un seuil binaire.
    """
    x = np.asarray(x, dtype=np.float64)
    rng = np.random.default_rng(seed)
    boots = rng.choice(x, size=(n_boot, x.shape[0]), replace=True).mean(axis=1)
    lo, hi = np.quantile(boots, [alpha / 2, 1 - alpha / 2])
    mean = float(x.mean())
    std = float(x.std(ddof=1))
    return {
        "mean": mean,
        "ic_lo": float(lo),
        "ic_hi": float(hi),
        "cohens_d": mean / std if std > 0 else float("nan"),
    }


def feature_z(
    zones: dict[str, np.ndarray], *, n_draws: int = 2048, seed: int = 42
) -> dict[str, Any]:
    """z features (flip intra-paire, null valide de 35b) + controle familial.

    Controle familial : distribution du max |z| sous le MEME null (max sur les
    d_sae features par tirage). La statistique observee max |z| est compareee a
    cette distribution -- un depassement ne peut plus etre invoque par la
    multiplicité des 32 768 tests.
    """
    diffs = zones["humour"] - zones["unfun"]
    observed = diffs.mean(axis=0)
    rng = np.random.default_rng(seed)
    n = diffs.shape[0]
    null_means = np.empty((n_draws, diffs.shape[1]))
    for d in range(n_draws):
        s = rng.choice(np.array([-1.0, 1.0]), size=(n, 1))
        null_means[d] = (diffs * s).mean(axis=0)
    z = observed / (null_means.std(axis=0) + 1e-12)
    null_z = null_means / (null_means.std(axis=0) + 1e-12)
    null_max = np.abs(null_z).max(axis=1)
    observed_max = float(np.abs(z).max())
    fw_p = float((null_max >= observed_max).mean())
    return {
        "z": z,
        "observed_max_abs_z": observed_max,
        "null_max_p95": float(np.quantile(null_max, 0.95)),
        "familywise_p": fw_p,
        "n_over3": int((np.abs(z) > 3).sum()),
    }


def final_verdict(per_layer_results: list[dict[str, Any]]) -> dict[str, Any]:
    """Verdict final de l'issue #14035 sur les jambes observationnelles.

    ``per_layer_results`` : une entree par trace mesuree (couche x variant x
    type), chacune portant au minimum ``verdict`` (la statistique
    pre-registree de ``measure_humor_differential``) et un identifiant lisible.
    """
    candidates = [r for r in per_layer_results if r.get("verdict") == "FEATURE_CANDIDATE"]
    if not candidates:
        verdict = "AUCUNE_FEATURE_STABLE"
    else:
        verdict = "CANDIDATS_PAR_TYPE"
    return {
        "verdict": verdict,
        "n_legs": len(per_layer_results),
        "n_candidate_legs": len(candidates),
        "candidate_legs": [r.get("leg", "?") for r in candidates],
    }
