"""Verdict du carnet QC-Py-45 rejoue sur l'ablation LEAN a entrees aleatoires.

Lit les traces ``shadow`` des backtests QC Cloud (``main.py``, parametres
``entries=random``, ``seed=<graine>``, ``stop_handling=keep``), une par graine et par
variante, rangees hors depot sous la forme ``<traces>/<variante>_s<graine>/chart.json``.
Applique ensuite la regle de la cellule « Verdict » du carnet, sans rien y changer, a deux
paires : ``kernel`` contre ``nokernel``, et ``kernel`` contre ``exposure90``.

- **A** : dMaxDD moyen >= 2 sigma inter-graines, et dMaxDD > 0 sur au moins 45 graines ;
- **B** : Diebold-Mariano sur la profondeur de drawdown (``dm_test.py``, perte mse,
  lag 21) : p median < 0,05 et ecart de perte median < 0 ;
- **C** : dSharpe median >= -0,05 ;
- BEATS si A, B et C ; NO BEATS si le dMaxDD median est <= 0 ou si le dSharpe est < 0 sur
  au moins 48 graines ; INCONCLUSIVE sinon. Les seuils supposent 50 graines : sur un jeu
  incomplet, le script mesure mais ne rend pas de verdict.

Controle hors verdict (``--carnet``) : le moteur du carnet (copie declaree de
``mesure_ecart_carnet.py``), sur la meme fenetre et avec les memes tirages, graine par
graine, compare a LEAN a titre descriptif.

Lancer : ``python ablation_lean.py --traces <dossier> [--carnet] [--out resultats.json]``.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd

ICI = Path(__file__).resolve().parent
sys.path.insert(0, str(ICI))
sys.path.insert(0, str(ICI.parents[1] / "ML-Training-Pipeline" / "scripts"))
from dm_test import diebold_mariano_test  # noqa: E402
from shadow_replay import qc_daily_equity  # noqa: E402

import mesure_ecart_carnet as carnet  # noqa: E402

VARIANTES = ("kernel", "nokernel", "exposure90")
PAIRES = (("kernel", "nokernel"), ("kernel", "exposure90"))
GRAINES = range(50)


def mesures(valeur: np.ndarray) -> tuple[dict, np.ndarray]:
    """Definitions du carnet : CAGR, Sharpe a taux nul, drawdown maximal, profondeur."""
    r = np.diff(valeur) / valeur[:-1]
    dd = valeur / np.maximum.accumulate(valeur) - 1
    return dict(CAGR=valeur[-1] ** (252 / len(valeur)) - 1,
                Sharpe=r.mean() / r.std() * np.sqrt(252),
                MaxDD=dd.min()), dd


def charger_lean(traces: Path) -> tuple[pd.DataFrame, dict, dict]:
    """Une ligne par (graine, variante) dont la trace existe ; profondeurs de drawdown."""
    lignes, dd, dates = [], {}, {}
    for g in GRAINES:
        for v in VARIANTES:
            f = traces / f"{v}_s{g}" / "chart.json"
            if not f.exists():
                continue
            jours, valeurs = qc_daily_equity(json.loads(f.read_text(encoding="utf-8")),
                                             window_start=carnet.DEBUT)
            valeur = np.asarray(valeurs, float)
            m, profondeur = mesures(valeur / valeur[0])   # base 1, comme le carnet
            lignes.append(dict(graine=g, variante=v, seances=len(jours), **m))
            dd[(g, v)] = profondeur
            dates[(g, v)] = (jours[0], jours[-1], len(jours))
    return pd.DataFrame(lignes), dd, dates


def paire(table: pd.DataFrame, dd: dict, a: str, b: str) -> dict:
    """Regle de la cellule « Verdict » du carnet, sur les graines ou a et b existent."""
    pa = table[table.variante == a].set_index("graine")
    pb = table[table.variante == b].set_index("graine")
    graines = sorted(set(pa.index) & set(pb.index))
    pa, pb = pa.loc[graines], pb.loc[graines]
    d_dd = 100 * (pa.MaxDD - pb.MaxDD)      # en points ; positif = drawdown moindre pour a
    d_sh = pa.Sharpe - pb.Sharpe
    d_cagr = 100 * (pa.CAGR - pb.CAGR)
    for g in graines:
        if len(dd[(g, a)]) != len(dd[(g, b)]):
            raise ValueError(f"graine {g} : traces de longueurs differentes ({a}, {b})")
    dm = [diebold_mariano_test(dd[(g, a)], dd[(g, b)], loss_fn="mse", max_lag=21) for g in graines]
    p = np.array([r.p_value for r in dm])
    s = np.array([r.mean_loss_diff for r in dm])
    A = bool((d_dd.mean() >= 2 * d_dd.std()) and (d_dd > 0).sum() >= 45)
    B = bool((np.median(p) < 0.05) and (np.median(s) < 0))
    C = bool(d_sh.median() >= -0.05)
    if len(graines) < 50:
        verdict = f"PARTIEL ({len(graines)}/50 graines, pas de verdict)"
    elif A and B and C:
        verdict = "BEATS"
    elif d_dd.median() <= 0 or (d_sh < 0).sum() >= 48:
        verdict = "NO BEATS"
    else:
        verdict = "INCONCLUSIVE"
    p252 = float(np.median([diebold_mariano_test(dd[(g, a)], dd[(g, b)], loss_fn="mse",
                                                 max_lag=252).p_value for g in graines]))
    return dict(
        a=a, b=b, graines=len(graines),
        dMaxDD_moyen=float(d_dd.mean()), dMaxDD_sigma=float(d_dd.std()),
        dMaxDD_median=float(d_dd.median()), dMaxDD_positif=int((d_dd > 0).sum()),
        dm_p_median=float(np.median(p)), dm_ecart_median=float(np.median(s)),
        dSharpe_median=float(d_sh.median()), dSharpe_q05=float(d_sh.quantile(0.05)),
        dSharpe_q95=float(d_sh.quantile(0.95)), dSharpe_negatif=int((d_sh < 0).sum()),
        dCAGR_median=float(d_cagr.median()), dCAGR_q05=float(d_cagr.quantile(0.05)),
        dCAGR_q95=float(d_cagr.quantile(0.95)),
        A=A, B=B, C=C, verdict=verdict, dm_p_median_lag252=p252,
    )


def afficher(r: dict) -> None:
    ratio = r["dMaxDD_moyen"] / r["dMaxDD_sigma"] if r["dMaxDD_sigma"] > 0 else float("nan")
    oui = {True: "oui", False: "non"}
    print(f"{r['a']} contre {r['b']} ({r['graines']} graines)")
    print(f"  A  dMaxDD = {r['dMaxDD_moyen']:+.2f} pt, sigma inter-graines {r['dMaxDD_sigma']:.2f} "
          f"(ratio {ratio:.1f}), positif sur {r['dMaxDD_positif']}/{r['graines']} -> {oui[r['A']]}")
    print(f"  B  DM (perte mse sur la profondeur de drawdown, lag 21) : p median = "
          f"{r['dm_p_median']:.2g}, ecart de perte median {r['dm_ecart_median']:+.2e} -> {oui[r['B']]}")
    print(f"  C  dSharpe median = {r['dSharpe_median']:+.3f} [{r['dSharpe_q05']:+.3f} ; "
          f"{r['dSharpe_q95']:+.3f}] -> {oui[r['C']]}")
    print(f"  cout : dCAGR median = {r['dCAGR_median']:+.2f} pt [{r['dCAGR_q05']:+.2f} ; "
          f"{r['dCAGR_q95']:+.2f}]")
    print(f"  verdict : {r['verdict']}")
    print(f"  sensibilite, hors verdict : p median avec un lag HAC de 252 = "
          f"{r['dm_p_median_lag252']:.2g}")


def moteur_carnet(graines: list[int]) -> tuple[pd.DataFrame, dict]:
    """Moteur du carnet, memes tirages que LEAN, sur la fenetre des backtests."""
    d = carnet.charger()
    reglages = {"kernel": ("kernel", "carnet", False), "nokernel": ("nokernel", "carnet", False),
                "exposure90": ("exposure90", "carnet", False),
                # reglage du moteur du carnet qui prevoit le mode keep (README, ecart au carnet)
                "kernel_lean": ("kernel", "ouvertes", True)}
    lignes, dd = [], {}
    for g in graines:
        for nom, (variante, mode_stop, ccl) in reglages.items():
            valeur, jrn = carnet.simuler(d, variante, mode_stop, ccl,
                                         choix=carnet.entrees_aleatoires(g))
            m, profondeur = mesures(valeur)
            lignes.append(dict(graine=g, variante=nom, stops=jrn["stops"],
                               coupures=len(jrn["coupures"]), **m))
            dd[(g, nom)] = profondeur
    rebal = int(d["rebal"].sum())
    print(f"moteur du carnet : {len(d['dates'])} seances du {d['dates'][0].date()} au "
          f"{d['dates'][-1].date()}, {rebal} rebalancements (tirages)")
    return pd.DataFrame(lignes), dd


def ecarts(lean: pd.DataFrame, nb: pd.DataFrame, v_lean: str, v_nb: str) -> dict:
    """Ecart LEAN moins carnet, graine par graine, sur une variante."""
    a = lean[lean.variante == v_lean].set_index("graine")
    b = nb[nb.variante == v_nb].set_index("graine")
    g = sorted(set(a.index) & set(b.index))
    out = {"lean": v_lean, "carnet": v_nb, "graines": len(g)}
    for k, f in (("CAGR", 100), ("MaxDD", 100), ("Sharpe", 1)):
        e = f * (a.loc[g, k] - b.loc[g, k])
        out[k] = dict(median=float(e.median()), q05=float(e.quantile(0.05)),
                      q95=float(e.quantile(0.95)),
                      correlation=float(np.corrcoef(a.loc[g, k], b.loc[g, k])[0, 1]))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--traces", type=Path, required=True)
    ap.add_argument("--carnet", action="store_true")
    ap.add_argument("--out", type=Path)
    a = ap.parse_args()
    lean, dd, dates = charger_lean(a.traces)
    if lean.empty:
        sys.exit(f"aucune trace sous {a.traces}")
    bornes = sorted(set(dates.values()))
    print(f"traces LEAN : {len(lean)} ; bornes (premiere, derniere, seances) : {bornes}")
    res = {"lean": [paire(lean, dd, x, y) for x, y in PAIRES]}
    for r in res["lean"]:
        afficher(r)
        print()
    resume = lean.groupby("variante")[["CAGR", "Sharpe", "MaxDD"]].median()
    print("medianes inter-graines (LEAN)")
    print(resume.to_string(float_format=lambda x: f"{x:+.4f}"))
    res["medianes_lean"] = resume.to_dict()
    if a.carnet:
        print()
        nb, dd_nb = moteur_carnet(sorted(lean.graine.unique()))
        res["carnet"] = [paire(nb, dd_nb, x, y) for x, y in PAIRES]
        print("verdict du carnet sur la meme fenetre, hors verdict LEAN (descriptif)")
        for r in res["carnet"]:
            afficher(r)
            print()
        res["ecarts"] = [ecarts(lean, nb, v, v) for v in VARIANTES] \
            + [ecarts(lean, nb, "kernel", "kernel_lean")]
        print("ecart LEAN moins carnet, graine par graine : median [q05 ; q95], correlation")
        for e in res["ecarts"]:
            txt = "  ".join(f"{k} {e[k]['median']:+.2f} [{e[k]['q05']:+.2f} ; {e[k]['q95']:+.2f}] "
                            f"r={e[k]['correlation']:.2f}" for k in ("CAGR", "MaxDD", "Sharpe"))
            print(f"  {e['lean']:10s} vs {e['carnet']:12s} {txt}")
        res["medianes_carnet"] = nb.groupby("variante")[["CAGR", "Sharpe", "MaxDD", "stops",
                                                         "coupures"]].median().to_dict()
    if a.out:
        a.out.write_text(json.dumps(res, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"\nresultats ecrits : {a.out}")


if __name__ == "__main__":
    main()
