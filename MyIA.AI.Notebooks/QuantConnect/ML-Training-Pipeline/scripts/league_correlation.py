"""Matrice de corrélation hebdomadaire des séries de la ligue (#19821, brique 4 ; #20083).

Une stratégie n'entre dans le panier que si elle se décorrèle du cœur. Ce script mesure
cette décorrélation sur les courbes de capital que les PRs d'évaluation ont mesurées sur
QC Cloud, au lieu de la supposer d'après la logique de la stratégie.

Protocole, écrit dans #20083 avant la mesure :

- clôture de capital par séance, lue par `shadow_replay.qc_daily_equity` (graphique
  `shadow`, séries e0..e4 entrelacées). Une référence détenue tracée dans b0..b4 se lit
  de la même façon ;
- clôture de semaine = dernier point de la semaine qui se termine le vendredi. Les séries
  crypto, qui ont des points le week-end, se lisent donc au vendredi, comme les actions ;
- rendement hebdomadaire = rapport de deux clôtures de semaines consécutives. Une semaine
  sans point est sautée : elle ne fabrique pas un rendement sur deux semaines. La dernière
  semaine de chaque série est retirée, la fin du backtest pouvant la couper en son milieu ;
- corrélation de Pearson sur les semaines communes aux deux séries, au moins 104 ;
- bootstrap circulaire par blocs apparié (mêmes indices pour les deux séries), blocs de
  8 semaines, 10 000 tirages, graine 0, intervalle à 95 %.

Le seuil de 0,7 appartient à la règle d'entrée du panier (brique 7). Ce script le
rapporte sans décider : il place l'estimation sous ou au-dessus du seuil, et marque
« fragile » une estimation dont l'intervalle chevauche le seuil.

Les membres sont listés dans `shadow/league_members.json`, une variante par stratégie
mesurée, et les séries restent dans les traces QC hors dépôt (`--traces-root`) :

    python league_correlation.py --traces-root <dossier des traces> \\
        --against spy --against btc --json matrice.json
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import math
import sys
from pathlib import Path

import numpy as np

from shadow_replay import qc_daily_equity

FRIDAY = 4
MIN_WEEKS = 104
BLOCK = 8
DRAWS = 10_000
SEED = 0
ENTRY_MAX_CORR = 0.7
MEMBERS = Path(__file__).resolve().parents[1] / "shadow" / "league_members.json"


def week_key(date: str) -> str:
    """Vendredi qui termine la semaine de `date` ; samedi et dimanche vont au vendredi suivant."""
    d = dt.date.fromisoformat(date)
    return (d + dt.timedelta(days=(FRIDAY - d.weekday()) % 7)).isoformat()


def weekly_returns(dates: list[str], equity: list[float]) -> dict[str, float]:
    """Rendements hebdomadaires, indexés par le vendredi qui termine la semaine."""
    closes: dict[str, float] = {}
    for d, v in sorted(zip(dates, equity)):
        closes[week_key(d)] = v
    weeks = sorted(closes)[:-1]
    out = {}
    for prev, cur in zip(weeks, weeks[1:]):
        if dt.date.fromisoformat(cur) - dt.date.fromisoformat(prev) == dt.timedelta(days=7):
            out[cur] = closes[cur] / closes[prev] - 1.0
    return out


def _rowwise_corr(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    a = a - a.mean(axis=1, keepdims=True)
    b = b - b.mean(axis=1, keepdims=True)
    with np.errstate(invalid="ignore", divide="ignore"):
        return (a * b).sum(axis=1) / np.sqrt((a * a).sum(axis=1) * (b * b).sum(axis=1))


def block_bootstrap_corr(x, y, block: int = BLOCK, draws: int = DRAWS, seed: int = SEED,
                         chunk: int = 500) -> dict:
    """Corrélation de Pearson et son bootstrap circulaire par blocs apparié.

    Les deux séries sont rééchantillonnées avec les mêmes indices, ce qui conserve leur
    dépendance semaine par semaine. Un tirage dont l'une des séries est constante n'a pas
    de corrélation : il est compté dans `undefined_draws` et écarté des quantiles.
    """
    x, y = np.asarray(x, dtype=float), np.asarray(y, dtype=float)
    n = x.size
    if y.size != n:
        raise ValueError(f"series lengths differ: {n} and {y.size}")
    if n < block:
        raise ValueError(f"only {n} weeks for a block of {block}")
    rng = np.random.default_rng(seed)
    n_blocks = math.ceil(n / block)
    offsets = np.arange(block)
    corrs = np.empty(draws)
    for lo in range(0, draws, chunk):
        hi = min(draws, lo + chunk)
        starts = rng.integers(0, n, size=(hi - lo, n_blocks))
        pos = ((starts[:, :, None] + offsets) % n).reshape(hi - lo, -1)[:, :n]
        corrs[lo:hi] = _rowwise_corr(x[pos], y[pos])
    defined = corrs[np.isfinite(corrs)]
    return {"observed": float(_rowwise_corr(x[None, :], y[None, :])[0]),
            "ci95": [float(np.quantile(defined, 0.025)), float(np.quantile(defined, 0.975))],
            "undefined_draws": int(draws - defined.size)}


def pair(a: dict[str, float], b: dict[str, float], **kw) -> dict:
    """Corrélation de deux séries hebdomadaires sur leurs semaines communes."""
    weeks = sorted(a.keys() & b.keys())
    if len(weeks) < MIN_WEEKS:
        return {"weeks": len(weeks), "observed": None,
                "reason": f"{len(weeks)} common weeks, fewer than {MIN_WEEKS}"}
    res = block_bootstrap_corr([a[w] for w in weeks], [b[w] for w in weeks], **kw)
    return {"weeks": len(weeks), "first": weeks[0], "last": weeks[-1], **res}


def position(res: dict, threshold: float = ENTRY_MAX_CORR) -> str:
    """Place une estimation par rapport au seuil d'entrée, sans décider de l'entrée."""
    if res.get("observed") is None:
        return "non mesurée"
    lo, hi = res["ci95"]
    side = "sous" if res["observed"] <= threshold else "au-dessus de"
    fragile = " (fragile)" if lo <= threshold < hi else ""
    return f"{side} {threshold:g}{fragile}"


def active_share(returns: dict[str, float]) -> float:
    """Part des semaines dont le rendement n'est pas nul, c'est-à-dire investies.

    Une stratégie souvent en liquide a beaucoup de semaines à zéro : sa corrélation se
    lit alors sur ses seules semaines investies, et cette part le dit.
    """
    v = np.fromiter(returns.values(), dtype=float)
    return float((np.abs(v) > 1e-12).mean()) if v.size else 0.0


def member_returns(root: Path, member: dict) -> dict[str, float]:
    """Rendements hebdomadaires d'un membre, lus dans `chart.json` de sa trace."""
    chart = json.loads((root / member["trace"] / "chart.json").read_text(encoding="utf-8"))
    prefix = member.get("series", "e")
    if prefix != "e":
        series = chart.get("series") or {}
        chart = {"series": {f"e{k}": series.get(f"{prefix}{k}") for k in range(5)}}
    return weekly_returns(*qc_daily_equity(chart))


def load_members(path: Path = MEMBERS) -> list[dict]:
    members = json.loads(path.read_text(encoding="utf-8"))["members"]
    ids = [m["id"] for m in members]
    if len(set(ids)) != len(ids):
        raise ValueError("duplicate member id")
    return members


def matrix(returns: dict[str, dict[str, float]], **kw) -> dict[tuple[str, str], dict]:
    ids = list(returns)
    return {(a, b): pair(returns[a], returns[b], **kw)
            for i, a in enumerate(ids) for b in ids[i + 1:]}


def _cell(res: dict | None) -> str:
    return "—" if res is None or res.get("observed") is None else f"{res['observed']:.2f}"


def report(members: list[dict], returns: dict[str, dict[str, float]],
           pairs: dict[tuple[str, str], dict], against: list[str]) -> str:
    ids = [m["id"] for m in members]
    lines = ["| Membre | Rôle | Trace | Issue | PR | Semaines | Investies | Première | Dernière |",
             "|---|---|---|---|---|---:|---:|---|---|"]
    for m in members:
        w = sorted(returns[m["id"]])
        lines.append(f"| `{m['id']}` | {m['role']} | `{m['trace']}`"
                     f"{' (' + m['series'] + ')' if m.get('series', 'e') != 'e' else ''} | "
                     f"{'#' + str(m['issue']) if m.get('issue') else ''} | "
                     f"{'#' + str(m['pr']) if m.get('pr') else ''} | {len(w)} | "
                     f"{active_share(returns[m['id']]):.0%} | {w[0]} | {w[-1]} |")
    lines += ["", "| | " + " | ".join(f"`{i}`" for i in ids) + " |",
              "|---|" + "---:|" * len(ids)]
    for a in ids:
        row = [("1.00" if a == b else _cell(pairs.get((a, b)) or pairs.get((b, a))))
               for b in ids]
        lines.append(f"| `{a}` | " + " | ".join(row) + " |")
    for ref in against:
        lines += ["", f"Corrélation à `{ref}` :", "",
                  "| Membre | Semaines | Corrélation | IC 95 % | Seuil 0,7 |",
                  "|---|---:|---:|---|---|"]
        for a in ids:
            if a == ref:
                continue
            res = pairs.get((a, ref)) or pairs.get((ref, a))
            ci = (f"[{res['ci95'][0]:.2f} ; {res['ci95'][1]:.2f}]"
                  if res.get("observed") is not None else res.get("reason", ""))
            lines.append(f"| `{a}` | {res['weeks']} | {_cell(res)} | {ci} | {position(res)} |")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--traces-root", type=Path, required=True,
                    help="dossier des traces QC (hors dépôt)")
    ap.add_argument("--members", type=Path, default=MEMBERS)
    ap.add_argument("--against", action="append", default=[],
                    help="membre auquel rapporter chaque série (répétable)")
    ap.add_argument("--json", type=Path, help="écrit la matrice complète en JSON")
    args = ap.parse_args(argv)
    members = load_members(args.members)
    ids = {m["id"] for m in members}
    unknown = [a for a in args.against if a not in ids]
    if unknown:
        ap.error(f"unknown member(s) for --against: {', '.join(unknown)}")
    returns = {m["id"]: member_returns(args.traces_root, m) for m in members}
    pairs = matrix(returns)
    sys.stdout.write(report(members, returns, pairs, args.against))
    if args.json:
        args.json.write_text(json.dumps(
            {"protocol": {"min_weeks": MIN_WEEKS, "block": BLOCK, "draws": DRAWS, "seed": SEED,
                          "threshold": ENTRY_MAX_CORR},
             "members": members,
             "pairs": [{"a": a, "b": b, **res} for (a, b), res in pairs.items()]},
            indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
