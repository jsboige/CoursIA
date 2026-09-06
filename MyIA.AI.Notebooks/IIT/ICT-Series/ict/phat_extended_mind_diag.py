"""Diagnostic borne du miss P2 de la case « Parite esprit etendu » (Otto/Inga, #8182).

Pre-enregistrement : issuecomment-5558855068 (poste AVANT tout run de
diagnostic). Le run historique (2026-08-25, ``ict/results/
extended_mind_store_results.json``, seeds 0-4, k=6/24) donne P1 ok,
P3 ok, P2 miss 0/5 : rho_O = 2.244 / 2.381 / 2.464 / 2.621 / 2.967
(mediane 2.464, seuil >= 3). La matrice lit « zone grise [2, 3) ».

Ce module decompose le miss en quatre causes mesurables, chacune avec
une bande predite AVANT run (H1-H4), et applique l'arbre de decision
pre-enregistre (ordre H3 -> H4 -> H1 et H2 -> sinon) :

  H1 absorption adaptative : epinglage neutralise (LRU pur) ->
     rho_O median dans [3.3, 4.5], >= 4/5 seeds >= 3 ;
  H2 capacite bornante k/n : scan k in {3, 6, 12, 18}, mediane de rho_O
     non-decroissante, croisement de 3 entre k=12 et k=18 (>= 3/5 seeds
     >= 3 a k=18) ; gate de mesurabilite : n_consult_shift >= 30/seed ;
  H3 puissance statistique : 20 seeds au nominal, mediane dans
     [2.3, 2.7] et IQR <= 0.5 -> miss systematique ;
  H4 denominateur contamine : num = c_after/c_before et
     den = h_after/h_before par seed ; num_median >= 3 ET den_median
     > 1.10 -> le bras cache_hit porte lui-meme de la degradation.

Verdicts (trois issues, patron case 3 / #14880) :
  ARTEFACT_PUISSANCE | ARTEFACT_DE_MESURE | REGIME_DE_PARAMETRES |
  DISSOCIATION_GRADUEE_REELLE.

Reutilise ``ict.extended_mind_store`` (FactWorld, ExtendedAgent,
_run_arm) -- aucune duplication du simulateur. CPU, numpy pur.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from ict.extended_mind_store import ExtendedAgent, FactWorld, _run_arm

__all__ = ["NoPinOtto", "otto_arm_metrics", "run_diag", "PREREG_REF"]

PREREG_REF = "issuecomment-5558855068"
HISTORICAL_RHO_OTTO = [2.463951753357483, 2.6208508980336176,
                       2.3806803382395927, 2.967212504627946,
                       2.243661878848318]
SEEDS_DIAG = [0, 1, 2, 3, 4]


class NoPinOtto(ExtendedAgent):
    """Otto sans pression d'epinglage : eviction LRU pure.

    Le comportement est inchange (lecture gatee p_read, bruit
    sigma_e, ecriture libre) sauf que la pression d'internalisation
    adaptative est neutralisee : apres chaque reponse, ``pins`` est
    vide, donc l'eviction dans ``observe`` trie par recence seule.
    """

    name = "otto_nopin"

    def answer(self, key: int) -> float:
        val = super().answer(key)
        self.pins.clear()
        return val


def otto_arm_metrics(seed: int, cache_k: int = 6,
                     agent_cls: type[ExtendedAgent] = ExtendedAgent,
                     *, n_keys: int = 24, t_base: int = 300,
                     t_shift: int = 600, t_end: int = 900,
                     p_read_shift: float = 0.1) -> dict:
    """Un bras Otto (deterministe par seed) + composantes de rho_O.

    Retourne num (c_after/c_before), den (h_after/h_before), rho
    (num/den), n_consult_shift et n_consult_base -- les memes
    grandeurs que ``run_case9``, calculees depuis les rows bruts.
    """

    world = FactWorld(n_keys=n_keys, seed=seed)
    agent = agent_cls(n_keys=n_keys, cache_k=cache_k, seed=seed)

    def shift(a: ExtendedAgent) -> None:
        a.p_read = p_read_shift

    rows = _run_arm(agent, world, t_base=t_base, t_shift=t_shift,
                    t_end=t_end, on_shift=shift)

    def _mean(phase: str, qclass: str | None = None) -> float:
        sel = [r["err"] for r in rows
               if r["phase"] == phase and (qclass is None
                                           or r["qclass"] == qclass)]
        return float(np.mean(sel)) if sel else float("nan")

    c_b, c_a = _mean("base", "store_consult"), _mean("shift", "store_consult")
    h_b, h_a = _mean("base", "cache_hit"), _mean("shift", "cache_hit")
    num, den = c_a / c_b, h_a / h_b
    return {
        "seed": seed,
        "k": cache_k,
        "num": float(num),
        "den": float(den),
        "rho": float(num / den),
        "n_consult_base": sum(1 for r in rows if r["phase"] == "base"
                              and r["qclass"] == "store_consult"),
        "n_consult_shift": sum(1 for r in rows if r["phase"] == "shift"
                               and r["qclass"] == "store_consult"),
    }


def _median(values: list[float]) -> float:
    return float(np.median(values))


def run_diag() -> dict:
    """Protocole pre-enregistre complet ; deterministe.

    Gate P0 (reproduction) : les rho_O par seed du bras nominal
    reproduisent le run historique a 1e-6 pres. Puis H1-H4 dans
    l'ordre de l'arbre pre-enregistre.
    """
    # --- gate P0 : reproduction exacte du run historique ---
    repro = [otto_arm_metrics(s) for s in SEEDS_DIAG]
    repro_ok = all(abs(r["rho"] - h) < 1e-6
                   for r, h in zip(repro, HISTORICAL_RHO_OTTO))

    # --- H4 : decomposition num/den au nominal ---
    num_median = _median([r["num"] for r in repro])
    den_median = _median([r["den"] for r in repro])

    # --- H1 : epinglage neutralise ---
    nopin = [otto_arm_metrics(s, agent_cls=NoPinOtto) for s in SEEDS_DIAG]
    nopin_median = _median([r["rho"] for r in nopin])
    nopin_ge3 = sum(r["rho"] >= 3.0 for r in nopin)

    # --- H2 : scan capacite k in {3, 6, 12, 18} ---
    scan = {}
    for k in (3, 6, 12, 18):
        rows_k = [otto_arm_metrics(s, cache_k=k) for s in SEEDS_DIAG]
        measurable = all(r["n_consult_shift"] >= 30 for r in rows_k)
        scan[k] = {
            "rho_median": _median([r["rho"] for r in rows_k]),
            "ge3_count": sum(r["rho"] >= 3.0 for r in rows_k),
            "n_consult_shift_min": min(r["n_consult_shift"] for r in rows_k),
            "measurable": bool(measurable),
        }
    medians_k = [scan[k]["rho_median"] for k in (3, 6, 12, 18)]
    monotone = all(b >= a - 0.05 for a, b in zip(medians_k, medians_k[1:])) \
        and medians_k[-1] > medians_k[0]
    k18_crossing = scan[18]["measurable"] and scan[18]["ge3_count"] >= 3

    # --- H3 : puissance, 20 seeds au nominal k=6 ---
    power = [otto_arm_metrics(s)["rho"] for s in range(20)]
    power_median = _median(power)
    power_iqr = float(np.percentile(power, 75) - np.percentile(power, 25))

    hypotheses = {
        "H1_nopin": {
            "median": nopin_median, "ge3_count": int(nopin_ge3),
            "held": bool(3.3 <= nopin_median <= 4.5 and nopin_ge3 >= 4),
        },
        "H2_scan_k": {
            "medians": medians_k, "monotone": bool(monotone),
            "k18_ge3_count": scan[18]["ge3_count"],
            "k18_measurable": scan[18]["measurable"],
            "held": bool(monotone and k18_crossing),
        },
        "H3_power": {
            "median": power_median, "iqr": power_iqr,
            "systematic_miss": bool(2.3 <= power_median <= 2.7
                                    and power_iqr <= 0.5),
            "power_artifact": bool(power_median >= 3.0),
        },
        "H4_decomposition": {
            "num_median": num_median, "den_median": den_median,
            "held": bool(num_median >= 3.0 and den_median > 1.10),
        },
    }

    # --- arbre pre-enregistre : H3 -> H4 -> (H1 et H2) -> sinon ---
    h = hypotheses
    if h["H3_power"]["power_artifact"]:
        verdict = "ARTEFACT_PUISSANCE"
    elif h["H4_decomposition"]["held"]:
        verdict = "ARTEFACT_DE_MESURE"
    elif h["H1_nopin"]["held"] and h["H2_scan_k"]["held"]:
        verdict = "REGIME_DE_PARAMETRES"
    else:
        verdict = "DISSOCIATION_GRADUEE_REELLE"

    return {
        "prereg_ref": PREREG_REF,
        "gate_P0_reproduction": bool(repro_ok),
        "repro_rows": repro,
        "nopin_rows": nopin,
        "scan_k": scan,
        "power_rhos": power,
        "hypotheses": hypotheses,
        "verdict": verdict,
    }


if __name__ == "__main__":
    out = run_diag()
    print(f"gate P0 reproduction: {out['gate_P0_reproduction']}")
    h = out["hypotheses"]
    print(f"H1 nopin    : median={h['H1_nopin']['median']:.3f} "
          f"ge3={h['H1_nopin']['ge3_count']}/5 held={h['H1_nopin']['held']}")
    print(f"H2 scan_k   : medians="
          f"{[round(m, 2) for m in h['H2_scan_k']['medians']]} "
          f"monotone={h['H2_scan_k']['monotone']} "
          f"k18_ge3={h['H2_scan_k']['k18_ge3_count']}/5 "
          f"held={h['H2_scan_k']['held']}")
    print(f"H3 power    : median={h['H3_power']['median']:.3f} "
          f"iqr={h['H3_power']['iqr']:.3f} "
          f"systematic={h['H3_power']['systematic_miss']}")
    print(f"H4 decomp   : num={h['H4_decomposition']['num_median']:.3f} "
          f"den={h['H4_decomposition']['den_median']:.3f} "
          f"held={h['H4_decomposition']['held']}")
    print(f"VERDICT: {out['verdict']}")
    dest = Path(__file__).parent / "results" / "phat_extended_mind_diag_results.json"
    dest.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n",
                    encoding="utf-8")
    print(f"results -> {dest.name}")
