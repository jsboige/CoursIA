"""Significativite de l'ecart entre la strategie 46 et ses benchmarks (#20388, #18906).

Entree : les graphiques "shadow" de trois backtests QC (strategie, SPY detenu, 60/40),
tels qu'ecrits par `read_backtest_chart` (contrat de rejeu en ombre, #18923 : la valeur du
portefeuille a chaque seance de SPY, dans e0..e4).

Sortie : pour chaque benchmark, trois tests sur les rendements journaliers apparies,
tous calcules par des organes existants de `ML-Training-Pipeline/scripts` :

1. ecart de Sharpe, Ledoit-Wolf 2008 (`m11c_sharpe_test.ledoit_wolf_sharpe_diff_se`) ;
2. ecart de Sharpe, bootstrap stationnaire (`m11c_sharpe_test.stationary_bootstrap_sharpe_diff`),
   intervalle percentile a 95 % ;
3. ecart de rendement moyen journalier, t de Newey-West (`diebold_mariano.newey_west_variance`).

Les p-valeurs sont rapportees brutes et apres correction de Holm. Sharpe a taux sans risque
nul, annualise par racine de 252 : il ne recopie pas le Sharpe de QC, qui retire le taux.

Usage :
    python significance.py --strategy s.json --bench spy=b1.json --bench 6040=b2.json [--out r.json]
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path

import numpy as np

SCRIPTS = Path(__file__).resolve().parents[2] / "ML-Training-Pipeline" / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from dm_test import newey_west_variance  # noqa: E402
from m11c_sharpe_test import (  # noqa: E402
    ledoit_wolf_sharpe_diff_se,
    stationary_bootstrap_sharpe_diff,
)
from shadow_replay import qc_daily_equity  # noqa: E402

ANNUAL = math.sqrt(252.0)


def two_sided_p(z: float) -> float:
    """p-valeur bilaterale d'une statistique normale centree reduite."""
    return math.erfc(abs(z) / math.sqrt(2.0))


def hac_lag(t: int) -> int:
    """Lag de troncature commun aux tests HAC : floor(T^0,25), au moins 1."""
    return max(1, int(math.floor(t ** 0.25)))


def paired_returns(dates_a: list[str], equity_a: list[float],
                   dates_b: list[str], equity_b: list[float]) -> tuple[np.ndarray, np.ndarray]:
    """Rendements journaliers simples de deux series de valeur, sur les memes seances.

    Les deux backtests tracent a chaque seance de SPY : une date presente d'un seul cote
    signale un trace incomplet, pas un calendrier different. On refuse plutot que de couper.
    """
    if dates_a != dates_b:
        only_a = sorted(set(dates_a) - set(dates_b))[:3]
        only_b = sorted(set(dates_b) - set(dates_a))[:3]
        raise ValueError(f"session dates differ (only in a: {only_a}, only in b: {only_b})")
    a = np.asarray(equity_a, dtype=float)
    b = np.asarray(equity_b, dtype=float)
    return a[1:] / a[:-1] - 1.0, b[1:] / b[:-1] - 1.0


def mean_diff_test(r_a: np.ndarray, r_b: np.ndarray) -> dict:
    """t de l'ecart de rendement moyen journalier, variance de Newey-West."""
    d = np.asarray(r_a, dtype=float) - np.asarray(r_b, dtype=float)
    t = len(d)
    lag = hac_lag(t)
    se = math.sqrt(newey_west_variance(d, lag) / t)
    stat = float(d.mean()) / se
    return {"mean_diff_daily": float(d.mean()), "se": se, "t": stat, "lag": lag,
            "p_two_sided": two_sided_p(stat)}


def compare(r_a: np.ndarray, r_b: np.ndarray, n_boot: int = 2000, mean_block: float = 10.0,
            seed: int = 0) -> dict:
    """Les trois tests de l'ecart a (strategie) - b (benchmark)."""
    t = len(r_a)
    sa, sb, diff, se = ledoit_wolf_sharpe_diff_se(r_a, r_b, q=hac_lag(t))
    z = diff / se
    p_one, obs, boots = stationary_bootstrap_sharpe_diff(r_a, r_b, n_boot=n_boot,
                                                         mean_block=mean_block, rng_seed=seed)
    lo, hi = np.percentile(boots, [2.5, 97.5])
    return {
        "sessions": t + 1,
        "sharpe_a": sa * ANNUAL,
        "sharpe_b": sb * ANNUAL,
        "sharpe_diff": diff * ANNUAL,
        "correlation": float(np.corrcoef(r_a, r_b)[0, 1]),
        "ledoit_wolf": {"se": se * ANNUAL, "z": z, "lag": hac_lag(t),
                        "p_two_sided": two_sided_p(z)},
        "bootstrap": {"n_boot": n_boot, "mean_block": mean_block, "seed": seed,
                      "ci95": [float(lo) * ANNUAL, float(hi) * ANNUAL],
                      "ci95_contains_zero": bool(lo <= 0.0 <= hi),
                      "p_one_sided": p_one, "obs": obs * ANNUAL},
        "mean_diff": mean_diff_test(r_a, r_b),
    }


def holm(pvalues: dict[str, float]) -> dict[str, float]:
    """p-valeurs ajustees de Holm-Bonferroni (monotones, plafonnees a 1)."""
    order = sorted(pvalues, key=pvalues.get)
    m = len(order)
    adjusted, running = {}, 0.0
    for i, key in enumerate(order):
        running = max(running, min(1.0, (m - i) * pvalues[key]))
        adjusted[key] = running
    return adjusted


def run(strategy: Path, benches: dict[str, Path], n_boot: int = 2000,
        mean_block: float = 10.0, seed: int = 0) -> dict:
    s_dates, s_eq = qc_daily_equity(json.loads(strategy.read_text(encoding="utf-8")))
    out = {"first_session": s_dates[0], "last_session": s_dates[-1], "comparisons": {}}
    raw = {}
    for name, path in benches.items():
        b_dates, b_eq = qc_daily_equity(json.loads(path.read_text(encoding="utf-8")))
        r_s, r_b = paired_returns(s_dates, s_eq, b_dates, b_eq)
        res = compare(r_s, r_b, n_boot=n_boot, mean_block=mean_block, seed=seed)
        out["comparisons"][name] = res
        raw[f"{name}/ledoit_wolf"] = res["ledoit_wolf"]["p_two_sided"]
        raw[f"{name}/mean_diff"] = res["mean_diff"]["p_two_sided"]
        # Le bootstrap rend une p unilaterale (H0 : Sharpe strategie <= benchmark) ;
        # doublee pour etre comparable aux deux autres, bilaterales.
        raw[f"{name}/bootstrap"] = min(1.0, 2.0 * min(res["bootstrap"]["p_one_sided"],
                                                      1.0 - res["bootstrap"]["p_one_sided"]))
    out["p_raw"] = raw
    out["p_holm"] = holm(raw)
    out["any_reject_5pct_raw"] = any(p < 0.05 for p in raw.values())
    out["any_reject_5pct_holm"] = any(p < 0.05 for p in out["p_holm"].values())
    return out


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--strategy", type=Path, required=True)
    ap.add_argument("--bench", action="append", required=True, metavar="NAME=PATH")
    ap.add_argument("--n-boot", type=int, default=2000)
    ap.add_argument("--mean-block", type=float, default=10.0)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", type=Path)
    args = ap.parse_args(argv)
    benches = dict((b.split("=", 1)[0], Path(b.split("=", 1)[1])) for b in args.bench)
    res = run(args.strategy, benches, args.n_boot, args.mean_block, args.seed)
    text = json.dumps(res, indent=2)
    if args.out:
        args.out.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
