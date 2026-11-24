"""ICT-23 -- banc d'anticipation, pilote et etude (tranche T2 de #26945).

Le protocole est **scelle** dans ``docs/ict/ict23-anticipation-pre-enregistrement.md``,
commite avant ce script (41de776c10). Ce banc ne fait qu'executer le
protocole : il ne choisit ni bande, ni graine, ni seuil, et n'amende rien
apres lecture d'un resultat.

Deux roles :

* ``--role pilot`` -- la graine 1000 **seule**, pour la faisabilite : le saut
  tombe-t-il dans la course ? reste-t-il assez de fenetres avant ``t_cut`` ?
  Le lacet rend-il deux sauts ? Aucune bande de substitution n'est calculee :
  le pilote ne sert jamais a choisir une bande, et ses nombres ne comptent
  dans aucun verdict.
* ``--role study`` -- les **controles d'abord** (C+var, C0, C+ar1, C-lacet,
  cinq graines), puis les cinq graines scellees sur les deux bras, puis le
  lacet. Les verdicts sont calcules ici, a partir des seules regles du
  document scelle.

Note d'instrument : le tau de Kendall est evalue par identite,
``tau_a = tau_b * sqrt((C2 - T) / C2)`` ou ``T`` compte les paires ex aequo,
au lieu de la boucle O(n^2) de :func:`ict.early_warning.kendall_tau`. La
valeur est la meme (l'egalite est **verifiee a l'execution** sur la premiere
serie de chaque bande, l'ecart est consigne dans le JSON), mais l'appel passe
de ~300 ms a ~3 ms a n = 4 827, ce qui rend les 3 000 series de substitution
du protocole executables en quelques minutes au lieu de trois quarts d'heure.
Sans scipy, le script retombe sur la boucle numpy de reference.

Usage :
    python scripts/ict23_anticipation.py --role pilot
    python scripts/ict23_anticipation.py --role study
    python scripts/ict23_anticipation.py --role study --no-band   # diagnostic
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional

import numpy as np

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from ict import early_warning as ews
from ict.persona_cusp import (
    RAMP_T2,
    aaft_surrogate,
    loop_tipping_points,
    persona_a_factor,
    persona_branch_along,
    persona_fold_b,
    persona_ramp_sde,
    persona_stable_branch,
    ramp_ews_segment,
)

try:  # accelere le tau ; le repli numpy reste exact, seulement plus lent
    from scipy.stats import kendalltau as _scipy_kendalltau
except Exception:  # pragma: no cover - environnement sans scipy
    _scipy_kendalltau = None

# Le nul N1 est un PAYSAGE, pas une persona : a = +0.4 s'obtient par
# -transgression * charge avec (-2.0, 0.2). La semantique de la persona n'a
# aucun role ici ; seul compte le fait que le cubique soit strictement
# croissant, donc sans pli.
NULL_TRANSGRESSION = -2.0
NULL_CHARGE = 0.2

PROTOCOL_DOC = "docs/ict/ict23-anticipation-pre-enregistrement.md"
PROTOCOL_COMMIT = "41de776c10"


# --------------------------------------------------------------------------- #
#  Instrument : tau de Kendall par identite                                    #
# --------------------------------------------------------------------------- #


def tau_a(y) -> float:
    """tau-a de Kendall de ``y`` contre son indice, egal a ``ews.kendall_tau``.

    ``tau_a = tau_b * sqrt((C2 - T) / C2)`` : scipy rend ``tau_b`` en
    O(n log n), ``T`` (paires ex aequo) se compte en O(n log n) par
    ``np.unique``, et le facteur les ramene a la definition tau-a du module
    (les ex aequo ne comptent ni comme concordants ni comme discordants,
    denominateur ``n(n-1)/2``).
    """
    y = np.asarray(y, dtype=float)
    n = y.shape[0]
    if n < 3:
        return float("nan")
    c2 = 0.5 * n * (n - 1)
    if _scipy_kendalltau is None:
        tau, _ = ews.kendall_tau(np.arange(n, dtype=float), y)
        return float(tau)
    _, counts = np.unique(y, return_counts=True)
    tied = float(np.sum(counts * (counts - 1) / 2.0))
    tb = float(_scipy_kendalltau(y, np.arange(n, dtype=float), variant="b")[0])
    return tb * float(np.sqrt((c2 - tied) / c2))


def series_taus(x, window: int, thin_factor: int) -> Dict[str, object]:
    """``tau_var`` / ``tau_ar1`` d'une serie, memes fenetres que le protocole."""
    seg = np.asarray(x, dtype=float)[:: int(thin_factor)]
    var = ews.rolling_variance(seg, int(window))
    ar1 = ews.rolling_lag1_autocorr(seg, int(window))
    ok = np.isfinite(var) & np.isfinite(ar1)
    return {
        "tau_var": tau_a(var[ok]),
        "tau_ar1": tau_a(ar1[ok]),
        "n_windows": int(ok.sum()),
    }


def surrogate_band(
    x,
    window: int,
    thin_factor: int,
    n_surrogates: int,
    seed: int,
    percentile: float,
) -> Dict[str, object]:
    """Bande AAFT (nul N2), identique a ``surrogate_tau_band`` mais plus vite.

    L'egalite avec :func:`ict.early_warning.kendall_tau` est **verifiee** sur
    le premier surrogate ; l'ecart mesure est rendu dans ``tau_check_dev``.
    """
    x = np.asarray(x, dtype=float)
    surr = aaft_surrogate(x, n_surrogates, seed)
    taus_var = np.empty(surr.shape[0], dtype=float)
    taus_ar1 = np.empty(surr.shape[0], dtype=float)
    dev = 0.0
    for k in range(surr.shape[0]):
        seg = surr[k][:: int(thin_factor)]
        var = ews.rolling_variance(seg, int(window))
        ar1 = ews.rolling_lag1_autocorr(seg, int(window))
        ok = np.isfinite(var) & np.isfinite(ar1)
        taus_var[k] = tau_a(var[ok])
        taus_ar1[k] = tau_a(ar1[ok])
        if k == 0:
            idx = np.arange(int(ok.sum()), dtype=float)
            ref_v, _ = ews.kendall_tau(idx, var[ok])
            ref_a, _ = ews.kendall_tau(idx, ar1[ok])
            dev = max(abs(ref_v - taus_var[k]), abs(ref_a - taus_ar1[k]))
    med_abs = float(np.nanmedian(np.abs(taus_var)))
    return {
        "band_var": float(np.nanpercentile(taus_var, float(percentile))),
        "band_ar1": float(np.nanpercentile(taus_ar1, float(percentile))),
        "median_abs_tau_var": med_abs,
        "informative": bool(med_abs <= 0.5),
        "tau_check_dev": float(dev),
    }


def control_series(kind: str, n: int, seed: int) -> np.ndarray:
    """Les series construites des controles, telles que le document les decrit."""
    g = np.random.default_rng(int(seed))
    if kind == "C0":
        return g.standard_normal(n)
    if kind == "C+var":
        return g.standard_normal(n) * np.linspace(1.0, 3.0, n)
    if kind == "C+ar1":
        phi = np.linspace(0.5, 0.95, n)
        e = g.standard_normal(n)
        z = np.empty(n, dtype=float)
        z[0] = e[0]
        for i in range(1, n):
            z[i] = phi[i] * z[i - 1] + np.sqrt(1.0 - phi[i] ** 2) * e[i]
        return z
    raise ValueError(f"controle inconnu : {kind}")


def run_control(
    kind: str, n_raw: int, seeds, cfg: Dict[str, object], with_band: bool = True
) -> Dict[str, object]:
    thin = int(cfg["thin_factor"])
    window = int(cfg["window"])
    rows: List[Dict[str, object]] = []
    for s in seeds:
        x = control_series(kind, n_raw, int(s))
        stat = series_taus(x, window, thin)
        row: Dict[str, object] = {"seed": int(s), **stat}
        if with_band:
            band = surrogate_band(
                x, window, thin, int(cfg["n_surrogates"]), int(s),
                float(cfg["band_percentile"]),
            )
            row.update(
                band_var=band["band_var"],
                band_ar1=band["band_ar1"],
                informative=band["informative"],
                tau_check_dev=band["tau_check_dev"],
                above_var=bool(stat["tau_var"] > band["band_var"]),
                above_ar1=bool(stat["tau_ar1"] > band["band_ar1"]),
            )
        rows.append(row)

    out: Dict[str, object] = {"kind": kind, "n_raw": int(n_raw), "rows": rows}
    if kind == "C0":
        green = all(not r["above_var"] for r in rows)
        out["expected"] = "tau_var sous la bande sur 5/5"
    elif kind == "C+var":
        green = all(r["tau_var"] > 0.0 and r["above_var"] for r in rows)
        out["expected"] = "tau_var > 0 et au-dessus de la bande sur 5/5"
    elif kind == "C+ar1":
        green = all(r["tau_ar1"] > 0.0 and r["above_ar1"] for r in rows)
        out["expected"] = "tau_ar1 > 0 et au-dessus de la bande sur 5/5"
    else:  # pragma: no cover - garde
        green = False
        out["expected"] = "?"
    out["green"] = bool(green) if with_band else None
    out["all_informative"] = bool(all(r.get("informative", True) for r in rows))
    return out


# --------------------------------------------------------------------------- #
#  Les deux bras                                                               #
# --------------------------------------------------------------------------- #


def arm_factors(cfg: Dict[str, object], arm: str):
    """(transgression, charge, b_start, b_end) du bras."""
    if arm == "pli":
        return (
            float(cfg["transgression"]),
            float(cfg["charge"]),
            float(cfg["b_start"]),
            float(cfg["b_end"]),
        )
    return (
        NULL_TRANSGRESSION,
        NULL_CHARGE,
        float(cfg["null_b_start"]),
        float(cfg["null_b_end"]),
    )


def run_arm(
    cfg: Dict[str, object],
    seed: int,
    arm: str,
    with_band: bool = True,
    t_cut_override: Optional[int] = None,
) -> Dict[str, object]:
    """Une graine d'un bras : rampe, segment, et bande de substitution."""
    tr, ch, b0, b1 = arm_factors(cfg, arm)
    a = persona_a_factor(tr, ch)
    p0 = persona_stable_branch(a, b0)

    t0 = time.time()
    ps, bs = persona_ramp_sde(
        tr, ch, b0, b1, p0,
        float(cfg["sigma"]), float(cfg["dt"]), int(cfg["steps"]), int(seed),
    )
    seg = ramp_ews_segment(
        ps, bs, tr, ch,
        window=int(cfg["window"]),
        thin_factor=int(cfg["thin_factor"]),
        lead_steps=int(cfg["lead_steps"]),
        min_steps=int(cfg["min_steps"]),
        jump_threshold=float(cfg["jump_threshold"]),
        jump_hold=int(cfg["jump_hold"]),
        t_cut_override=t_cut_override,
    )
    elapsed = time.time() - t0

    out: Dict[str, object] = {
        "arm": arm,
        "seed": int(seed),
        "a": float(a),
        "p0": float(p0),
        "t_cross": seg["t_cross"],
        "t_jump": seg["t_jump"],
        "t_cut": seg["t_cut"],
        "t_cut_override": None if t_cut_override is None else int(t_cut_override),
        "jumped_before_fold": seg["jumped_before_fold"],
        "excluded": seg["excluded"],
        "lambda_start": seg["lambda_start"],
        "lambda_end": seg["lambda_end"],
        "branch_start": seg["branch_start"],
        "tau_var": seg["tau_var"],
        "tau_ar1": seg["tau_ar1"],
        "amp": seg["amp"],
        "n_windows": seg["n_windows"],
        "elapsed_s": round(elapsed, 2),
    }
    if with_band and not seg["excluded"]:
        t_cut = int(seg["t_cut"])
        branch = persona_branch_along(bs[:t_cut], a)
        resid = ps[:t_cut] - branch
        band = surrogate_band(
            resid, int(cfg["window"]), int(cfg["thin_factor"]),
            int(cfg["n_surrogates"]), int(seed), float(cfg["band_percentile"]),
        )
        out.update(
            band_var=band["band_var"],
            band_ar1=band["band_ar1"],
            median_abs_tau_var=band["median_abs_tau_var"],
            informative=band["informative"],
            tau_check_dev=band["tau_check_dev"],
            above_var=bool(seg["tau_var"] > band["band_var"]),
            above_ar1=bool(seg["tau_ar1"] > band["band_ar1"]),
        )
    return out


# --------------------------------------------------------------------------- #
#  Lacet deterministe (P-B)                                                    #
# --------------------------------------------------------------------------- #


def run_loop(cfg: Dict[str, object]) -> Dict[str, object]:
    b_c = persona_fold_b(float(cfg["transgression"]), float(cfg["charge"]))
    t0 = time.time()
    loop = loop_tipping_points(
        float(cfg["transgression"]), float(cfg["charge"]),
        n_points=int(cfg["loop_points"]),
        b_min=float(cfg["loop_b_min"]),
        b_max=float(cfg["loop_b_max"]),
        dt=float(cfg["dt"]),
        relax_steps=int(cfg["loop_relax_steps"]),
    )
    out = {
        "b_c": None if b_c is None else float(b_c),
        "two_bc": None if b_c is None else float(2.0 * b_c),
        "ok": bool(loop["ok"]),
        "b_up": loop["b_up"],
        "b_down": loop["b_down"],
        "width": loop["width"],
        "jumps": loop["jumps"],
        "elapsed_s": round(time.time() - t0, 2),
    }
    if out["ok"] and b_c is not None:
        out["rel_error_vs_2bc"] = float(abs(loop["width"] - 2.0 * b_c) / (2.0 * b_c))
        out["p_b_within_15pct"] = bool(out["rel_error_vs_2bc"] <= 0.15)
        # Clause d'affaiblissement (B) scellee : « les points coincident » tombe
        # des que la largeur atteint 5 % de 2 b_c (0.0506). Un lacet reel (~1.0)
        # la fait tomber ; seule une largeur de l'ordre du pas de grille la
        # laisse vivante. Le sens du drapeau suit le texte scelle, pas l'usage
        # qu'en fait le verdict d'hysteresis.
        out["clause_b_fallen"] = bool(float(loop["width"]) >= 0.0506)
        out["hysteresis_refuted"] = bool(not out["clause_b_fallen"])
    else:
        out["rel_error_vs_2bc"] = None
        out["p_b_within_15pct"] = False
        out["clause_b_fallen"] = None
        out["hysteresis_refuted"] = None
    return out


def run_c_lacet(cfg: Dict[str, object]) -> Dict[str, object]:
    """Nul du lacet : ``charge = 0`` doit rendre **zero** saut."""
    loop = loop_tipping_points(
        float(cfg["transgression"]), 0.0,
        n_points=int(cfg["loop_points"]),
        b_min=float(cfg["loop_b_min"]),
        b_max=float(cfg["loop_b_max"]),
        dt=float(cfg["dt"]),
        relax_steps=int(cfg["loop_relax_steps"]),
    )
    return {
        "kind": "C-lacet",
        "expected": "0 saut sous charge = 0",
        "n_jumps": len(loop["jumps"]),
        "ok_flag": bool(loop["ok"]),
        "green": bool(len(loop["jumps"]) == 0),
    }


# --------------------------------------------------------------------------- #
#  Verdicts (regles du document scelle, rien de plus)                          #
# --------------------------------------------------------------------------- #


def _clause(values_fold, values_null, threshold_zero=None,
            threshold_min=None, above_flags=None) -> Dict[str, object]:
    f = np.asarray(values_fold, dtype=float)
    n = np.asarray(values_null, dtype=float)
    out: Dict[str, object] = {
        "n_fold": int(f.shape[0]),
        "n_null": int(n.shape[0]),
        "min_fold": float(f.min()) if f.size else None,
        "max_null": float(n.max()) if n.size else None,
    }
    clauses = []
    if threshold_zero is not None:
        k = int(np.sum(f > threshold_zero))
        out["n_above_zero"] = k
        clauses.append(bool(k >= min(4, len(f))) if f.size else False)
    if threshold_min is not None:
        k = int(np.sum(f >= threshold_min))
        out["n_above_min"] = k
        clauses.append(bool(k >= min(4, len(f))) if f.size else False)
    if above_flags is not None:
        k = int(np.sum(np.asarray(above_flags, dtype=bool)))
        out["n_above_band"] = k
        clauses.append(bool(k >= min(4, len(above_flags))) if len(above_flags) else False)
    if f.size and n.size:
        out["separation_min_fold_gt_max_null"] = bool(f.min() > n.max())
        clauses.append(out["separation_min_fold_gt_max_null"])
    out["held"] = bool(all(clauses))
    return out


def compute_predictions(
    fold: List[Dict[str, object]], null: List[Dict[str, object]], loop: Dict[str, object]
) -> Dict[str, object]:
    fv = [r for r in fold if not r.get("excluded")]
    nv = [r for r in null if not r.get("excluded")]
    p_a1 = _clause(
        [r["tau_var"] for r in fv], [r["tau_var"] for r in nv],
        threshold_zero=0.0,
        above_flags=[r.get("above_var") for r in fv],
    )
    p_a2 = _clause(
        [r["tau_ar1"] for r in fv], [r["tau_ar1"] for r in nv],
        threshold_zero=0.0,
        above_flags=[r.get("above_ar1") for r in fv],
    )
    p_a3 = _clause(
        [r["amp"] for r in fv], [r["amp"] for r in nv],
        threshold_min=1.5,
    )
    p_b = {
        "width": loop.get("width"),
        "two_bc": loop.get("two_bc"),
        "rel_error": loop.get("rel_error_vs_2bc"),
        "within_15pct": bool(loop.get("p_b_within_15pct")),
        "clause_B_fallen": loop.get("clause_b_fallen"),
    }
    return {"P_A1": p_a1, "P_A2": p_a2, "P_A3": p_a3, "P_B": p_b}


def compute_verdict(
    controls: Dict[str, Dict[str, object]],
    fold: List[Dict[str, object]],
    preds: Dict[str, object],
) -> Dict[str, object]:
    controls_green = all(c.get("green") for c in controls.values() if c.get("green") is not None)
    informative = all(
        c.get("all_informative", True) for c in controls.values()
    ) and all(
        r.get("informative", True) for r in fold
    )
    n_excluded = int(sum(1 for r in fold if r.get("excluded")))
    excluded_gate = n_excluded >= 2 and len(fold) > 0
    p1 = bool(preds["P_A1"]["held"])
    p2 = bool(preds["P_A2"]["held"])
    p3 = bool(preds["P_A3"]["held"])
    _b_raw = preds["P_B"]["clause_B_fallen"]
    b_fallen = None if _b_raw is None else bool(_b_raw)

    if not controls_green or not informative or excluded_gate:
        verdict = "INSTRUMENT NON INFORMATIF"
        reason = {
            "controls_green": bool(controls_green),
            "band_informative": bool(informative),
            "excluded_gate": bool(excluded_gate),
            "n_excluded": n_excluded,
        }
    elif p1 and p2 and p3 and b_fallen:
        verdict, reason = "ANTICIPATION CONFIRMEE", None
    elif p1 and p3 and not p2:
        verdict, reason = "ANTICIPATION PARTIELLE -- variance seule", None
    elif p2 and (not p1 or not p3):
        verdict, reason = "ANTICIPATION PARTIELLE -- memoire seule", None
    elif not p1 and not p2:
        verdict, reason = "ANTICIPATION REFUTEE", None
    else:  # P_A1 tenue sans P_A3, ou P_A3 seule : hors des cases scellees
        verdict, reason = "HORS DES CASES SCELLEES", {
            "P_A1": p1, "P_A2": p2, "P_A3": p3, "clause_B_fallen": b_fallen,
        }

    if b_fallen is None:
        hyst = "HORS DES CASES SCELLEES (lacet sans deux sauts)"
    else:
        hyst = "HYSTERESIS CONFIRMEE" if b_fallen else "HYSTERESIS REFUTEE"
    return {
        "anticipation": verdict,
        "hysteresis": hyst,
        "reason": reason,
        "P_A1": p1, "P_A2": p2, "P_A3": p3,
        "clause_B_fallen": b_fallen,
    }


# --------------------------------------------------------------------------- #
#  Roles                                                                       #
# --------------------------------------------------------------------------- #


def _now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _write(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"ecrit : {path}  ({path.stat().st_size / 1024:.1f} Ko)")


def run_pilot(cfg: Dict[str, object]) -> Dict[str, object]:
    seed = int(cfg["pilot_seed"])
    print(f"[pilote] graine {seed} -- faisabilite seule, aucune bande")
    t0 = time.time()
    fold = run_arm(cfg, seed, "pli", with_band=False)
    print(f"  pli  t_cross={fold['t_cross']} t_jump={fold['t_jump']} "
          f"t_cut={fold['t_cut']} n_windows={fold['n_windows']} "
          f"exclu={fold['excluded']}")
    null = run_arm(cfg, seed, "nul_n1", with_band=False, t_cut_override=int(fold["t_cut"]))
    print(f"  nul  t_cut={null['t_cut']} n_windows={null['n_windows']} "
          f"exclu={null['excluded']}")
    loop = run_loop(cfg)
    print(f"  lacet ok={loop['ok']} width={loop['width']} 2b_c={loop['two_bc']}")
    c_lacet = run_c_lacet(cfg)
    print(f"  C-lacet sauts={c_lacet['n_jumps']} vert={c_lacet['green']}")
    elapsed = time.time() - t0

    feasibility = {
        "jump_falls_in_course": bool(fold["t_jump"] is not None),
        "t_cut_at_least_min_steps": bool(int(fold["t_cut"]) >= int(cfg["min_steps"])),
        "at_least_30_windows": bool(int(fold["n_windows"]) >= 30),
        "null_shares_t_cut": bool(int(null["t_cut"]) == int(fold["t_cut"])),
        "null_monotone_landscape": True,
        "loop_two_jumps": bool(loop["ok"]),
        "c_lacet_zero_jumps": bool(c_lacet["green"]),
    }
    feasibility["all_green"] = bool(all(feasibility.values()))
    payload = {
        "protocol": PROTOCOL_DOC,
        "protocol_commit": PROTOCOL_COMMIT,
        "role": "pilot",
        "note": ("Graine 1000 seule. Faisabilite seulement : aucune bande de "
                 "substitution n'est calculee et aucun nombre de ce fichier "
                 "n'entre dans un verdict."),
        "generated_utc": _now(),
        "config": {k: (list(v) if isinstance(v, tuple) else v) for k, v in cfg.items()},
        "feasibility": feasibility,
        "fold_arm_seed1000": fold,
        "null_arm_seed1000": null,
        "loop": loop,
        "c_lacet": c_lacet,
        "elapsed_s": round(elapsed, 2),
    }
    return payload


def run_study(cfg: Dict[str, object], with_band: bool = True) -> Dict[str, object]:
    seeds = [int(s) for s in cfg["seeds"]]
    n_raw = int(cfg["steps"])
    b_c = persona_fold_b(float(cfg["transgression"]), float(cfg["charge"]))
    t_cross_analytic = None
    b0 = float(cfg["b_start"])
    b1 = float(cfg["b_end"])
    if b_c is not None:
        bs_grid = np.linspace(b0, b1, n_raw, endpoint=False)
        hit = np.where(bs_grid >= b_c)[0]
        t_cross_analytic = int(hit[0]) if hit.size else n_raw
    n_ctrl = (t_cross_analytic if t_cross_analytic is not None else n_raw) - int(cfg["lead_steps"])

    t0 = time.time()
    print(f"[etude] controles d'abord, n_raw={n_ctrl} (= t_cross analytique - lead)")
    controls: Dict[str, Dict[str, object]] = {}
    for kind in ("C+var", "C0", "C+ar1"):
        c = run_control(kind, n_ctrl, seeds, cfg, with_band=with_band)
        controls[kind] = c
        if with_band:
            print(f"  {kind:6s} vert={c['green']} "
                  f"tau_var={[round(r['tau_var'], 3) for r in c['rows']]}")
        else:
            print(f"  {kind:6s} (sans bande)")
    controls["C-lacet"] = run_c_lacet(cfg)
    print(f"  C-lacet vert={controls['C-lacet']['green']}")

    print(f"[etude] bras pli, graines {seeds}")
    fold: List[Dict[str, object]] = []
    for s in seeds:
        r = run_arm(cfg, s, "pli", with_band=with_band)
        fold.append(r)
        print(f"  seed {s:>4}: t_cut={r['t_cut']} n={r['n_windows']} "
              f"tau_var={r['tau_var']:+.3f} tau_ar1={r['tau_ar1']:+.3f} "
              f"amp={r['amp']:.3f} exclu={r['excluded']}")

    print("[etude] nul N1 apparie au t_cut de chaque graine")
    null: List[Dict[str, object]] = []
    for s, r in zip(seeds, fold):
        n = run_arm(cfg, s, "nul_n1", with_band=with_band,
                    t_cut_override=int(r["t_cut"]))
        null.append(n)
        print(f"  seed {s:>4}: t_cut={n['t_cut']} n={n['n_windows']} "
              f"tau_var={n['tau_var']:+.3f} tau_ar1={n['tau_ar1']:+.3f} "
              f"amp={n['amp']:.3f}")

    print("[etude] lacet deterministe")
    loop = run_loop(cfg)
    print(f"  ok={loop['ok']} b_up={loop['b_up']} b_down={loop['b_down']} "
          f"width={loop['width']} 2b_c={loop['two_bc']}")

    preds = compute_predictions(fold, null, loop)
    verdict = compute_verdict(controls, fold, preds)

    payload = {
        "protocol": PROTOCOL_DOC,
        "protocol_commit": PROTOCOL_COMMIT,
        "role": "study",
        "generated_utc": _now(),
        "config": {k: (list(v) if isinstance(v, tuple) else v) for k, v in cfg.items()},
        "n_control_raw": int(n_ctrl),
        "t_cross_analytic": t_cross_analytic,
        "controls": controls,
        "fold_arm": fold,
        "null_arm": null,
        "loop": loop,
        "predictions": preds,
        "verdict": verdict,
        "elapsed_s": round(time.time() - t0, 2),
    }
    return payload


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--role", choices=("pilot", "study"), required=True)
    parser.add_argument("--no-band", action="store_true",
                        help="diagnostic : saute les bandes de substitution")
    parser.add_argument("--out", default=None, help="chemin du JSON de sortie")
    args = parser.parse_args(argv)

    cfg = dict(RAMP_T2)
    if args.role == "pilot":
        out = Path(args.out) if args.out else (
            _ROOT / "ict" / "results" / f"ict23_anticipation_pilot_v1_seed{int(cfg['pilot_seed'])}.json"
        )
        payload = run_pilot(cfg)
    else:
        out = Path(args.out) if args.out else (
            _ROOT / "ict" / "results" / "ict23_anticipation_study.json"
        )
        payload = run_study(cfg, with_band=not args.no_band)
        v = payload["verdict"]
        print()
        print(f"VERDICT anticipation : {v['anticipation']}")
        print(f"VERDICT hysteresis   : {v['hysteresis']}")
        print(f"  P_A1={v['P_A1']}  P_A2={v['P_A2']}  P_A3={v['P_A3']}  "
              f"clause_B_tombee={v['clause_B_fallen']}")
        if v.get("reason"):
            print(f"  motif : {v['reason']}")
        print(f"duree : {payload['elapsed_s']} s")

    _write(out, payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())