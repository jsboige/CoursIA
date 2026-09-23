"""Statistiques des trois bras de LowBeta-Industries-QC (issue #17500).

Deux etapes, separees pour que les chiffres du README se recalculent sans acces QC :

  fetch  lit, pour chaque backtest QC Cloud, les statistiques de la plateforme et le graphique
         "Monthly" trace par main.py, puis ecrit measures/monthly_returns.csv et measures/qc_statistics.json.
         Identifiants : variables d'environnement QC_API_USER_ID et QC_API_ACCESS_TOKEN (jamais dans le code).
  stats  relit ces fichiers, telecharge le taux sans risque TB3MS (FRED) et ecrit measures/arms_summary.json.

Usage :
  python analyze_arms.py fetch --project 36854709 --backtest article=<id> --backtest bab=<id> --backtest spy=<id>
  python analyze_arms.py stats
  python analyze_arms.py markdown   # tables du README
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
import os
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path

import numpy as np
import requests

HERE = Path(__file__).resolve().parent
DATA = HERE / "measures"  # pas data/ : ignore par le .gitignore QC (donnees de marche LEAN)
API = "https://www.quantconnect.com/api/v2"
FRED_TB3MS = "https://fred.stlouisfed.org/graph/fredgraph.csv?id=TB3MS"
SERIES = ("ret", "spy", "netexp", "gross")
STAT_KEYS = (
    "Sharpe Ratio", "Probabilistic Sharpe Ratio", "Compounding Annual Return", "Drawdown",
    "Annual Standard Deviation", "Alpha", "Beta", "Total Fees", "Total Orders", "Portfolio Turnover",
    "Net Profit", "End Equity",
)

# Fenetres d'analyse. Les bornes sont fixees par les sources, pas par les resultats :
# l'echantillon US d'AFP 2014 s'arrete en 2012 ; l'article #18469 a ete publie fin 2024.
WINDOWS = {
    "full": ("2010-01", "2026-08"),
    "afp_overlap": ("2010-01", "2012-12"),
    "afp_oos": ("2013-01", "2026-08"),
    "article_is": ("2010-01", "2024-12"),
    "article_oos": ("2025-01", "2026-08"),
}


# ---------------------------------------------------------------------------- fetch

def _call(path: str, data: dict) -> dict:
    user = os.environ["QC_API_USER_ID"]
    token = os.environ["QC_API_ACCESS_TOKEN"]
    ts = str(int(time.time()))
    hashed = hashlib.sha256(f"{token}:{ts}".encode()).hexdigest()
    resp = requests.post(API + path, auth=(user, hashed), headers={"Timestamp": ts}, json=data, timeout=180)
    resp.raise_for_status()
    payload = resp.json()
    if payload.get("success") is False:
        raise RuntimeError(f"{path}: {payload.get('errors')}")
    time.sleep(7)  # plafond de flotte : 10 appels QC par minute
    return payload


def _points(series: dict) -> list[tuple[int, float]]:
    """Les points d'une serie QC, qu'ils soient serialises en [t, v] ou en {x, y}."""
    out = []
    for p in series.get("values") or []:
        if isinstance(p, dict):
            t, v = p.get("x"), p.get("y")
        else:
            t, v = p[0], p[-1]
        if t is not None and v is not None:
            out.append((int(t), float(v)))
    return out


def _chart(project: int, backtest: str, name: str) -> dict:
    start = int(datetime(2009, 12, 1, tzinfo=timezone.utc).timestamp())
    end = int(datetime(2026, 10, 1, tzinfo=timezone.utc).timestamp())
    for _ in range(20):
        # count largement au-dessus du nombre de points : en dessous, l'API reechantillonne la serie
        # sur une grille reguliere et interpole (valeurs non entieres mesurees sur un compteur de noms).
        payload = _call("/backtests/chart/read", {
            "projectId": project, "backtestId": backtest, "name": name, "count": 5000, "start": start, "end": end,
        })
        if payload.get("chart"):
            return payload["chart"]
        time.sleep(10)  # le graphique est encore en cours de preparation cote QC
    raise RuntimeError(f"graphique {name} indisponible pour {backtest}")


def _month_label(unix: int) -> str:
    # main.py trace le bilan du mois m au premier jour de bourse du mois m+1 : on recule d'une semaine.
    return (datetime.fromtimestamp(unix, tz=timezone.utc) - timedelta(days=7)).strftime("%Y-%m")


def fetch(project: int, backtests: dict[str, str]) -> None:
    DATA.mkdir(exist_ok=True)
    rows: dict[str, dict[str, float]] = {}
    stats: dict[str, dict] = {}
    for arm, bid in backtests.items():
        bt = _call("/backtests/read", {"projectId": project, "backtestId": bid})["backtest"]
        stats[arm] = {
            "backtestId": bid,
            "parameterSet": bt.get("parameterSet"),
            "statistics": {k: (bt.get("statistics") or {}).get(k) for k in STAT_KEYS},
        }
        chart = _chart(project, bid, "Monthly")
        for name in SERIES:
            points = _points(chart["series"].get(name, {}))
            labels = [_month_label(t) for t, _ in points]
            # main.py trace au premier jour de bourse du mois : un point date apres le 5 du mois,
            # ou deux points pour un meme mois, signalent une serie reechantillonnee par l'API.
            late = [t for t, _ in points if datetime.fromtimestamp(t, tz=timezone.utc).day > 5]
            if late or len(set(labels)) != len(labels):
                raise RuntimeError(f"{arm}/{name} : serie reechantillonnee ({len(late)} points hors debut de mois)")
            for label, (_, v) in zip(labels, points):
                rows.setdefault(label, {})[f"{arm}_{name}"] = v
        if arm == "bab":  # composition du BAB a chaque selection : industries, noms, beta moyen des deux jambes
            legs = _chart(project, bid, "BAB")["series"]
            cols_bab = ("industries", "names", "beta_low", "beta_high")
            by_date: dict[str, dict[str, float]] = {}
            for name in cols_bab:
                for t, v in _points(legs.get(name, {})):
                    by_date.setdefault(datetime.fromtimestamp(t, tz=timezone.utc).strftime("%Y-%m-%d"), {})[name] = v
            with open(DATA / "bab_legs.csv", "w", newline="", encoding="utf-8") as f:
                w = csv.writer(f, lineterminator="\n")
                w.writerow(["date", *cols_bab])
                for date in sorted(by_date):
                    w.writerow([date] + [f"{by_date[date].get(c, float('nan')):.6g}" for c in cols_bab])
    (DATA / "qc_statistics.json").write_text(json.dumps({"projectId": project, "arms": stats}, indent=1), encoding="utf-8")
    cols = sorted({c for r in rows.values() for c in r})
    with open(DATA / "monthly_returns.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(["month"] + cols)
        for month in sorted(rows):
            w.writerow([month] + [("" if c not in rows[month] else f"{rows[month][c]:.10g}") for c in cols])
    print(f"{len(rows)} mois, colonnes : {cols}")


# ---------------------------------------------------------------------------- stats

def _p_normal(t: float) -> float:
    return math.erfc(abs(t) / math.sqrt(2))


def _nw_lags(n: int) -> int:
    return int(math.floor(4 * (n / 100) ** (2 / 9)))


def ols_nw(y: np.ndarray, x: np.ndarray | None) -> dict:
    """OLS avec ecarts-types de Newey-West (noyau de Bartlett)."""
    n = len(y)
    X = np.ones((n, 1)) if x is None else np.column_stack([np.ones(n), x])
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    e = y - X @ coef
    lags = _nw_lags(n)
    xe = X * e[:, None]
    S = xe.T @ xe
    for lag in range(1, lags + 1):
        g = xe[lag:].T @ xe[:-lag]
        S += (1 - lag / (lags + 1)) * (g + g.T)
    inv = np.linalg.inv(X.T @ X)
    se = np.sqrt(np.diag(inv @ S @ inv))
    t = coef / se
    return {"coef": coef.tolist(), "t": t.tolist(), "p": [_p_normal(v) for v in t], "n": n, "lags": lags}


def sharpe(x: np.ndarray) -> float:
    return float(np.mean(x) / np.std(x, ddof=1) * math.sqrt(12))


def sharpe_diff_hac(a: np.ndarray, b: np.ndarray) -> dict:
    """Difference de Sharpe a - b, erreur-type HAC (Ledoit et Wolf 2008, section 3.1 ; noyau de Bartlett).

    Le test de Jobson-Korkie-Memmel suppose des rendements normaux et independants ; celui-ci
    reste valide sous queues epaisses et autocorrelation. Il est liberal en petit echantillon.
    """
    n = len(a)
    m1, m2 = np.mean(a), np.mean(b)
    g1, g2 = np.mean(a ** 2), np.mean(b ** 2)
    v1, v2 = g1 - m1 ** 2, g2 - m2 ** 2
    delta = m1 / math.sqrt(v1) - m2 / math.sqrt(v2)
    grad = np.array([g1 / v1 ** 1.5, -g2 / v2 ** 1.5, -m1 / (2 * v1 ** 1.5), m2 / (2 * v2 ** 1.5)])
    y = np.column_stack([a - m1, b - m2, a ** 2 - g1, b ** 2 - g2])
    lags = _nw_lags(n)
    psi = y.T @ y / n
    for lag in range(1, lags + 1):
        g = y[lag:].T @ y[:-lag] / n
        psi += (1 - lag / (lags + 1)) * (g + g.T)
    psi *= n / (n - 4)
    se = math.sqrt(grad @ psi @ grad / n)
    z = delta / se
    return {"sharpe_diff_annual": float(delta * math.sqrt(12)), "z": float(z), "p": _p_normal(z), "n": n, "lags": lags}


def _tb3ms() -> dict[str, float]:
    text = requests.get(FRED_TB3MS, timeout=60).text
    out = {}
    for row in csv.DictReader(io.StringIO(text)):
        date = row.get("observation_date") or row.get("DATE")
        value = row.get("TB3MS")
        if date and value not in (None, "", "."):
            out[date[:7]] = float(value) / 100 / 12
    return out


def _window(months: list[str], lo: str, hi: str) -> np.ndarray:
    return np.array([lo <= m <= hi for m in months])


def stats(bab_scale: float) -> dict:
    with open(DATA / "monthly_returns.csv", encoding="utf-8") as f:
        rows = [r for r in csv.DictReader(f)]
    rf = _tb3ms()
    need = ["article_ret", "article_netexp", "bab_ret", "bab_netexp", "spy_ret", "spy_netexp", "spy_spy"]
    rows = [r for r in rows if all(r.get(c) for c in need) and r["month"] in rf]
    months = [r["month"] for r in rows]
    col = lambda c: np.array([float(r[c]) for r in rows])
    r_f = np.array([rf[m] for m in months])

    # Rendement en exces d'un compte LEAN (le cash n'y porte pas d'interet) : R - exposition nette x rf.
    ex = {arm: col(f"{arm}_ret") - col(f"{arm}_netexp") * r_f for arm in ("article", "bab", "spy")}
    mkt = col("spy_spy") - r_f  # marche = SPY total return, mesure dans le bras spy
    bab_unit = ex["bab"] / bab_scale  # BAB par unite, comparable a AFP 2014 Table 3

    out: dict = {"months": [months[0], months[-1], len(months)], "bab_scale": bab_scale, "windows": {}}
    for name, (lo, hi) in WINDOWS.items():
        m = _window(months, lo, hi)
        if m.sum() < 12:
            continue
        w = {
            "n": int(m.sum()),
            "sharpe": {arm: sharpe(ex[arm][m]) for arm in ex},
            "article_vs_spy": sharpe_diff_hac(ex["article"][m], ex["spy"][m]),
            "article_capm": ols_nw(ex["article"][m], mkt[m]),
            "bab_mean": ols_nw(bab_unit[m], None),
            "bab_capm": ols_nw(bab_unit[m], mkt[m]),
            "bab_vol_annual": float(np.std(bab_unit[m], ddof=1) * math.sqrt(12)),
            "mean_netexp": {arm: float(np.mean(col(f"{arm}_netexp")[m])) for arm in ex},
            "mean_gross": {arm: float(np.mean(col(f"{arm}_gross")[m])) for arm in ex},
        }
        out["windows"][name] = w

    legs_path = DATA / "bab_legs.csv"
    if legs_path.exists():
        with open(legs_path, encoding="utf-8") as f:
            legs = [r for r in csv.DictReader(f)]
        get = lambda c: np.array([float(r[c]) for r in legs])
        out["bab_legs"] = {
            "rebalances": len(legs),
            "industries_mean": float(np.mean(get("industries"))),
            "names_mean": float(np.mean(get("names"))),
            "beta_low_mean": float(np.mean(get("beta_low"))),
            "beta_high_mean": float(np.mean(get("beta_high"))),
            # Exposition par dollar de BAB (AFP Table 3 : $Long 1,34 / $Short 0,77), a partir des betas moyens
            "long_per_dollar": float(np.mean(1 / get("beta_low"))),
            "short_per_dollar": float(np.mean(1 / get("beta_high"))),
        }

    folds = np.array_split(np.arange(len(months)), 5)
    out["folds"] = []
    for idx in folds:
        sl = np.zeros(len(months), bool)
        sl[idx] = True
        out["folds"].append({
            "from": months[idx[0]], "to": months[idx[-1]],
            "article_alpha_pct": 100 * ols_nw(ex["article"][sl], mkt[sl])["coef"][0],
            "article_beta": ols_nw(ex["article"][sl], mkt[sl])["coef"][1],
            "bab_mean_pct": 100 * float(np.mean(bab_unit[sl])),
            "bab_t": ols_nw(bab_unit[sl], None)["t"][0],
        })
    (DATA / "arms_summary.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
    return out


def _report(out: dict) -> None:
    for name, w in out["windows"].items():
        a, b, jk = w["article_capm"], w["bab_mean"], w["article_vs_spy"]
        print(f"[{name}] n={w['n']} Sharpe art/bab/spy = "
              f"{w['sharpe']['article']:.3f}/{w['sharpe']['bab']:.3f}/{w['sharpe']['spy']:.3f} | "
              f"LW z={jk['z']:.2f} p={jk['p']:.3f} | art alpha={100*a['coef'][0]:.3f}%/m t={a['t'][0]:.2f} beta={a['coef'][1]:.3f} | "
              f"BAB {100*b['coef'][0]:.3f}%/m t={b['t'][0]:.2f} vol={100*w['bab_vol_annual']:.1f}% "
              f"beta={w['bab_capm']['coef'][1]:.3f}")
    for f in out["folds"]:
        print(f"  fold {f['from']}..{f['to']}: art alpha {f['article_alpha_pct']:.3f}%/m beta {f['article_beta']:.2f} | "
              f"BAB {f['bab_mean_pct']:.3f}%/m t={f['bab_t']:.2f}")


WINDOW_LABELS = {
    "full": "2010-01 → 2026-07 (tout)",
    "afp_overlap": "2010-01 → 2012-12 (fin de l'échantillon AFP)",
    "afp_oos": "2013-01 → 2026-07 (hors échantillon AFP)",
    "article_is": "2010-01 → 2024-12 (in-sample de l'article)",
    "article_oos": "2025-01 → 2026-07 (hors échantillon de l'article)",
}


def _fr(x: float, nd: int = 2) -> str:
    return f"{x:.{nd}f}".replace(".", ",").replace("-", "−")


def markdown() -> None:
    """Tables du README, relues depuis measures/ : aucun chiffre n'est recopie a la main."""
    q = json.loads((DATA / "qc_statistics.json").read_text(encoding="utf-8"))
    s = json.loads((DATA / "arms_summary.json").read_text(encoding="utf-8"))
    arms = [a for a in ("article", "bab", "spy") if a in q["arms"]]
    print("| Statistique QC | " + " | ".join(f"`{a}`" for a in arms) + " |")
    print("|---|" + "---|" * len(arms))
    for k in STAT_KEYS:
        print(f"| {k} | " + " | ".join(str(q["arms"][a]["statistics"].get(k)) for a in arms) + " |")
    print("| backtest | " + " | ".join(f"`{q['arms'][a]['backtestId']}`" for a in arms) + " |")
    print()
    print("| Fenêtre | mois | Sharpe excès article / bab / spy | Δ Sharpe article − spy (z, p) "
          "| alpha article %/mois (t) | bêta article | BAB %/mois par $ (t) | vol. BAB | bêta BAB |")
    print("|---|---|---|---|---|---|---|---|---|")
    for name, w in s["windows"].items():
        a, b, lw = w["article_capm"], w["bab_mean"], w["article_vs_spy"]
        print(f"| {WINDOW_LABELS.get(name, name)} | {w['n']} "
              f"| {_fr(w['sharpe']['article'])} / {_fr(w['sharpe']['bab'])} / {_fr(w['sharpe']['spy'])} "
              f"| {_fr(lw['sharpe_diff_annual'])} ({_fr(lw['z'])}, {_fr(lw['p'], 3)}) "
              f"| {_fr(100 * a['coef'][0], 3)} ({_fr(a['t'][0])}) | {_fr(a['coef'][1])} "
              f"| {_fr(100 * b['coef'][0], 3)} ({_fr(b['t'][0])}) | {_fr(100 * w['bab_vol_annual'], 1)} % "
              f"| {_fr(w['bab_capm']['coef'][1])} |")
    legs = s.get("bab_legs")
    if legs:
        print()
        print("| Composition du BAB (moyenne sur les rééquilibrages) | valeur |")
        print("|---|---|")
        print(f"| rééquilibrages | {legs['rebalances']} |")
        print(f"| industries retenues | {_fr(legs['industries_mean'], 1)} |")
        print(f"| noms en portefeuille | {_fr(legs['names_mean'], 0)} |")
        print(f"| bêta ex ante, jambe basse / jambe haute | {_fr(legs['beta_low_mean'])} / {_fr(legs['beta_high_mean'])} |")
        print(f"| $Long / $Short par dollar de BAB | {_fr(legs['long_per_dollar'])} / {_fr(legs['short_per_dollar'])} |")
    print()
    print("| Tranche | alpha article %/mois | bêta article | BAB %/mois par $ (t) |")
    print("|---|---|---|---|")
    for f in s["folds"]:
        print(f"| {f['from']} → {f['to']} | {_fr(f['article_alpha_pct'], 3)} | {_fr(f['article_beta'])} "
              f"| {_fr(f['bab_mean_pct'], 3)} ({_fr(f['bab_t'])}) |")


def main() -> None:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    f = sub.add_parser("fetch")
    f.add_argument("--project", type=int, required=True)
    f.add_argument("--backtest", action="append", required=True, help="arm=backtestId")
    s = sub.add_parser("stats")
    s.add_argument("--bab-scale", type=float, default=0.5)
    sub.add_parser("markdown")
    args = ap.parse_args()
    if args.cmd == "fetch":
        fetch(args.project, dict(b.split("=", 1) for b in args.backtest))
    elif args.cmd == "stats":
        _report(stats(args.bab_scale))
    else:
        markdown()


if __name__ == "__main__":
    main()
