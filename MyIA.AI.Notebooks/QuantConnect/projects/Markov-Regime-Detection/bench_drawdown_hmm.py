"""Statistiques des bras « couverture or par régime de drawdown » de Markov-Regime-Detection v1.3 (issue #17589).

Trois étapes, séparées pour que les chiffres du README se recalculent sans accès QC :

  fetch     lit, pour chaque backtest de measures/backtests.json, les statistiques de la plateforme,
            les statistiques d'exécution (ajustements, échecs, accord des étiquettes) et le graphique
            « Monthly » tracé par main.py, puis écrit measures/monthly_returns.csv et measures/qc_statistics.json.
            Identifiants : variables d'environnement QC_API_USER_ID et QC_API_ACCESS_TOKEN (jamais dans le code).
  stats     relit ces fichiers, télécharge le taux sans risque TB3MS (FRED) et écrit measures/arms_summary.json.
  markdown  imprime les tables du README à partir de measures/ : aucun chiffre n'est recopié à la main.

Les fonctions d'appel QC et les tests (Newey-West, différence de Sharpe HAC de Ledoit et Wolf 2008,
TB3MS) sont ceux de LowBeta-Industries-QC/analyze_arms.py, importés et non recopiés.

Usage :
  python bench_drawdown_hmm.py fetch
  python bench_drawdown_hmm.py stats
  python bench_drawdown_hmm.py markdown
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "LowBeta-Industries-QC"))
from analyze_arms import _call, _fr, _month_label, _points, _tb3ms, ols_nw, sharpe, sharpe_diff_hac  # noqa: E402

DATA = HERE / "measures"  # pas data/ : ignoré par le .gitignore QC (données de marché LEAN)
SERIES = ("ret", "spy", "gld", "netexp", "gldw")
SEEDS = (0, 1, 7, 42, 99)
FAMILIES = ("article", "fixed")
# Témoin statique de chaque famille : même calendrier hebdomadaire, poids GLD constant égal au poids
# GLD moyen réalisé par la famille (5 graines, fenêtre complète), soit 0,545 pour article et 0,450 pour fixed.
STATIC = {"article": "static_article", "fixed": "static_fixed"}
STAT_KEYS = (
    "Sharpe Ratio", "Compounding Annual Return", "Drawdown", "Net Profit", "Total Orders",
    "Total Fees", "Portfolio Turnover", "Probabilistic Sharpe Ratio",
)

# Fenêtres fixées par les sources, pas par les résultats : l'article teste 2019-2024 et y choisit
# ses deux paramètres sur une grille ; tout ce qui précède 2019 et tout ce qui suit 2024 est hors échantillon.
WINDOWS = {
    "full": ("2008-01", "2026-08"),
    "oos_before": ("2008-01", "2018-12"),
    "article_is": ("2019-01", "2024-12"),
    "oos_after": ("2025-01", "2026-08"),
}
WINDOW_LABELS = {
    "full": "2008-01 → 2026-08 (tout)",
    "oos_before": "2008-01 → 2018-12 (hors échantillon, avant l'article)",
    "article_is": "2019-01 → 2024-12 (fenêtre de l'article, in-sample)",
    "oos_after": "2025-01 → 2026-08 (hors échantillon, après l'article)",
}


# ---------------------------------------------------------------------------- fetch

def _chart(project: int, backtest: str, name: str) -> dict:
    start = int(datetime(2007, 12, 1, tzinfo=timezone.utc).timestamp())
    end = int(datetime(2026, 10, 1, tzinfo=timezone.utc).timestamp())
    for _ in range(20):
        # count largement au-dessus du nombre de points : en dessous, l'API rééchantillonne la série.
        payload = _call("/backtests/chart/read", {
            "projectId": project, "backtestId": backtest, "name": name, "count": 5000, "start": start, "end": end,
        })
        if payload.get("chart"):
            return payload["chart"]
        time.sleep(10)  # le graphique est encore en cours de préparation côté QC
    raise RuntimeError(f"graphique {name} indisponible pour {backtest}")


def fetch() -> None:
    reg = json.loads((DATA / "backtests.json").read_text(encoding="utf-8"))
    project = reg["projectId"]
    rows: dict[str, dict[str, float]] = {}
    stats: dict[str, dict] = {}
    for label, bid in reg["backtests"].items():
        bt = _call("/backtests/read", {"projectId": project, "backtestId": bid})["backtest"]
        stats[label] = {
            "backtestId": bid,
            "parameterSet": bt.get("parameterSet"),
            "statistics": {k: (bt.get("statistics") or {}).get(k) for k in STAT_KEYS},
            "runtimeStatistics": {k: (bt.get("runtimeStatistics") or {}).get(k)
                                  for k in ("Fits", "Fit failures", "Label agreement")},
        }
        if label.startswith("repro"):
            continue  # la reproduction n'entre que par ses statistiques QC
        chart = _chart(project, bid, "Monthly")
        for name in SERIES:
            points = _points(chart["series"].get(name, {}))
            labels = [_month_label(t) for t, _ in points]
            # main.py trace au premier jour de bourse du mois : un point daté après le 5 du mois,
            # ou deux points pour un même mois, signalent une série rééchantillonnée par l'API.
            late = [t for t, _ in points if datetime.fromtimestamp(t, tz=timezone.utc).day > 5]
            if late or len(set(labels)) != len(labels):
                raise RuntimeError(f"{label}/{name} : série rééchantillonnée ({len(late)} points hors début de mois)")
            for month, (_, v) in zip(labels, points):
                rows.setdefault(month, {})[f"{label}_{name}"] = v
    (DATA / "qc_statistics.json").write_text(json.dumps({"projectId": project, "backtests": stats}, indent=1),
                                             encoding="utf-8")
    cols = sorted({c for r in rows.values() for c in r})
    with open(DATA / "monthly_returns.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(["month"] + cols)
        for month in sorted(rows):
            w.writerow([month] + [("" if c not in rows[month] else f"{rows[month][c]:.10g}") for c in cols])
    print(f"{len(rows)} mois, {len(cols)} colonnes")


# ---------------------------------------------------------------------------- stats

def _cagr(r: np.ndarray) -> float:
    return float(np.prod(1 + r) ** (12 / len(r)) - 1)


def _maxdd(r: np.ndarray) -> float:
    equity = np.cumprod(1 + r)
    return float(np.max(1 - equity / np.maximum.accumulate(equity)))


def stats() -> dict:
    with open(DATA / "monthly_returns.csv", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    labels = sorted({c[: -len("_ret")] for c in rows[0] if c.endswith("_ret")})
    rf = _tb3ms()
    need = [f"{a}_{s}" for a in labels for s in ("ret", "netexp")] + ["spy_spy", "spy_gld"]
    rows = [r for r in rows if all(r.get(c) for c in need) and r["month"] in rf]
    months = [r["month"] for r in rows]
    col = lambda c: np.array([float(r[c]) for r in rows])  # noqa: E731
    r_f = np.array([rf[m] for m in months])

    # Rendement en excès d'un compte LEAN (le cash n'y porte pas d'intérêt) : R - exposition nette x rf.
    ex = {a: col(f"{a}_ret") - col(f"{a}_netexp") * r_f for a in labels}
    raw = {a: col(f"{a}_ret") for a in labels}
    mkt = col("spy_spy") - r_f
    gld = col("spy_gld")
    hmm_labels = [f"{fam}_s{s}" for fam in FAMILIES for s in SEEDS if f"{fam}_s{s}" in ex]

    out: dict = {"months": [months[0], months[-1], len(months)], "labels": labels, "windows": {}}
    for name, (lo, hi) in WINDOWS.items():
        m = np.array([lo <= x <= hi for x in months])
        if m.sum() < 12:
            continue
        w: dict = {
            "n": int(m.sum()),
            "corr_spy_gld": float(np.corrcoef(col("spy_spy")[m], gld[m])[0, 1]),
            "arms": {},
        }
        for a in labels:
            w["arms"][a] = {
                "sharpe": sharpe(ex[a][m]),
                "cagr": _cagr(raw[a][m]),
                "maxdd_monthly": _maxdd(raw[a][m]),
                "mean_gldw": float(np.mean(col(f"{a}_gldw")[m])) if rows[0].get(f"{a}_gldw") is not None else None,
                "capm": ols_nw(ex[a][m], mkt[m]),
            }
            if a != "spy":
                w["arms"][a]["vs_spy"] = sharpe_diff_hac(ex[a][m], ex["spy"][m])
            fam = a.split("_s")[0]
            if a in hmm_labels and STATIC[fam] in ex:
                w["arms"][a]["vs_static"] = sharpe_diff_hac(ex[a][m], ex[STATIC[fam]][m])
        # Dispersion entre graines : l'écart au témoin est-il plus grand que 2 sigma inter-graines ?
        w["families"] = {}
        for fam in FAMILIES:
            members = [f"{fam}_s{s}" for s in SEEDS if f"{fam}_s{s}" in ex]
            if not members:
                continue
            fam_out = {"seeds": len(members)}
            for ref in ("spy", "static"):
                key = f"vs_{ref}"
                if not all(key in w["arms"][a] for a in members):
                    continue
                d = np.array([w["arms"][a][key]["sharpe_diff_annual"] for a in members])
                p = np.array([w["arms"][a][key]["p"] for a in members])
                sd = float(np.std(d, ddof=1)) if len(d) > 1 else float("nan")
                fam_out[key] = {
                    "mean_diff": float(np.mean(d)), "sd_diff": sd,
                    "edge_over_2sd": bool(np.mean(d) > 2 * sd) if len(d) > 1 else False,
                    "min_diff": float(np.min(d)), "max_diff": float(np.max(d)),
                    "seeds_p05_positive": int(np.sum((p < 0.05) & (d > 0))),
                }
            fam_out["sharpe_mean"] = float(np.mean([w["arms"][a]["sharpe"] for a in members]))
            fam_out["gldw_mean"] = float(np.mean([w["arms"][a]["mean_gldw"] for a in members]))
            w["families"][fam] = fam_out
        out["windows"][name] = w

    # Tranches chronologiques égales (walk-forward descriptif) : l'écart de Sharpe moyen entre graines.
    out["folds"] = []
    for idx in np.array_split(np.arange(len(months)), 5):
        m = np.zeros(len(months), bool)
        m[idx] = True
        fold = {"from": months[idx[0]], "to": months[idx[-1]], "spy": sharpe(ex["spy"][m])}
        for ref in STATIC.values():
            if ref in ex:
                fold[ref] = sharpe(ex[ref][m])
        for fam in FAMILIES:
            members = [f"{fam}_s{s}" for s in SEEDS if f"{fam}_s{s}" in ex]
            if members:
                fold[fam] = float(np.mean([sharpe(ex[a][m]) for a in members]))
        out["folds"].append(fold)

    q = json.loads((DATA / "qc_statistics.json").read_text(encoding="utf-8"))["backtests"]
    out["regime_model"] = {}
    for a in hmm_labels:
        rt = q[a]["runtimeStatistics"]
        fits, fails, agree = (int(rt.get(k) or 0) for k in ("Fits", "Fit failures", "Label agreement"))
        out["regime_model"][a] = {"fits": fits, "failures": fails,
                                  "label_agreement": agree / fits if fits else float("nan")}
    (DATA / "arms_summary.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
    return out


# ---------------------------------------------------------------------------- markdown

def _pct(x: float, nd: int = 1) -> str:
    return _fr(100 * x, nd) + " %"


def _fx(x: float | None) -> str:
    """Un nombre au format du README, ou un tiret quand le bras n'a pas été mesuré."""
    return "—" if x is None or (isinstance(x, float) and math.isnan(x)) else _fr(x)


def markdown() -> None:
    q = json.loads((DATA / "qc_statistics.json").read_text(encoding="utf-8"))["backtests"]
    s = json.loads((DATA / "arms_summary.json").read_text(encoding="utf-8"))
    print("| Backtest QC | paramètres | Sharpe | CAGR | MaxDD | ordres | frais |")
    print("|---|---|---:|---:|---:|---:|---:|")
    for label, b in q.items():
        st = b["statistics"]
        params = ", ".join(f"{k}={v}" for k, v in sorted((b.get("parameterSet") or {}).items()))
        print(f"| `{label}` | {params} | {st['Sharpe Ratio']} | {st['Compounding Annual Return']} "
              f"| {st['Drawdown']} | {st['Total Orders']} | {st['Total Fees']} |")
    print()
    print("| Fenêtre | mois | corr. SPY/GLD | spy | static 0,545 | static 0,450 | article (moy. 5 graines) "
          "| fixed (moy. 5 graines) | Δ article − spy (moy. ± σ graines) | Δ article − static 0,545 (moy. ± σ) "
          "| Δ fixed − static 0,450 (moy. ± σ) |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---|---|---|")
    for name, w in s["windows"].items():
        fa, ff = w["families"].get("article", {}), w["families"].get("fixed", {})
        def d(fam: dict, key: str) -> str:
            v = fam.get(key)
            return "—" if not v else f"{_fr(v['mean_diff'])} ± {_fr(v['sd_diff'])} ({v['seeds_p05_positive']}/5 p<0,05)"
        st_a = w["arms"].get(STATIC["article"], {}).get("sharpe")
        st_f = w["arms"].get(STATIC["fixed"], {}).get("sharpe")
        print(f"| {WINDOW_LABELS[name]} | {w['n']} | {_fr(w['corr_spy_gld'])} "
              f"| {_fx(w['arms']['spy']['sharpe'])} | {_fx(st_a)} | {_fx(st_f)} "
              f"| {_fx(fa.get('sharpe_mean'))} | {_fx(ff.get('sharpe_mean'))} "
              f"| {d(fa, 'vs_spy')} | {d(fa, 'vs_static')} | {d(ff, 'vs_static')} |")
    print()
    print("| Tranche | spy | static 0,545 | static 0,450 | article | fixed |")
    print("|---|---:|---:|---:|---:|---:|")
    for f in s["folds"]:
        print(f"| {f['from']} → {f['to']} | {_fx(f['spy'])} | {_fx(f.get(STATIC['article']))} "
              f"| {_fx(f.get(STATIC['fixed']))} | {_fx(f.get('article'))} | {_fx(f.get('fixed'))} |")
    print()
    # Exposition et alpha CAPM (Newey-West) sur la fenêtre complète : d'où vient le rendement de chaque bras.
    print("| Bras (fenêtre complète) | poids GLD moyen | CAGR | MaxDD mensuel | alpha CAPM annualisé (t NW) | bêta SPY |")
    print("|---|---:|---:|---:|---:|---:|")
    for a, r in s["windows"]["full"]["arms"].items():
        c = r["capm"]
        print(f"| `{a}` | {_fx(r['mean_gldw'])} | {_pct(r['cagr'])} | {_pct(r['maxdd_monthly'])} "
              f"| {_pct(12 * c['coef'][0])} ({_fr(c['t'][0])}) | {_fx(c['coef'][1])} |")
    print()
    # Les bras article et fixed ajustent le même modèle avec la même graine : leurs diagnostics sont identiques.
    print("| Graine | ajustements | échecs avalés | étiquette de l'article = état à drawdown profond |")
    print("|---|---:|---:|---:|")
    for a, r in s["regime_model"].items():
        if a.startswith("article_"):
            print(f"| {a.split('_s')[1]} | {r['fits']} | {r['failures']} | {_pct(r['label_agreement'])} |")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=("fetch", "stats", "markdown"))
    args = ap.parse_args()
    DATA.mkdir(exist_ok=True)
    if args.cmd == "fetch":
        fetch()
    elif args.cmd == "stats":
        out = stats()
        for name, w in out["windows"].items():
            print(name, w["n"], {fam: {k: v for k, v in f.items() if k.startswith("vs_") or k == "sharpe_mean"}
                                  for fam, f in w["families"].items()})
    else:
        markdown()


if __name__ == "__main__":
    main()
