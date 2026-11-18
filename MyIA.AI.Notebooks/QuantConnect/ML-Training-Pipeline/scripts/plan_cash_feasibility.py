"""Can the paper harness plan buy more than its cash? Measure and correction (#19113).

``plan_orders`` turns target weights into whole-share orders. A line held above
its target by less than the band is not sold, while another line under its
target is bought, so the buys of a cycle can exceed the cash plus its sells.
This script replays the harness rule month by month on 2005-2026 and counts
the cycles where that happens, then compares the two ways the planner can keep
the buys within the cash.

Pre-registered on #19113 before any computation:

- data: daily closes of SPY, QQQ, IEF, GLD (the files of #19072), rebalanced on
  the last session of each month from 2005-01 to 2026-09, executed at the
  close, 5 bp of fees on the traded value, cash at 0 %;
- rule: ``inverse_vol_weights`` then ``plan_orders`` of the harness, with the
  defaults of ``CycleConfig`` (21 sessions, 50 % cap per line, 3-point band,
  0.2 % reserve, no minimum order);
- starting capital 10 000 and 100 000 in price units (whole shares matter);
- three policies:
  ``N`` the current plan, unchecked: a buy above the current cash stops the
  cycle, as the broker adapter does (sells sent, remaining buys dropped);
  ``S`` buys scaled down pro rata to fit cash + sells - reserve;
  ``R`` band-skipped sells on overweight lines released first, then ``S``;
- verdict: defect ``CONFIRME`` if ``N`` has at least one infeasible cycle at
  either capital; ``S`` and ``R`` must end every cycle with cash >= 0; ``R``
  becomes the harness default if its mean distance to the targets on the
  cycles where the constraint binds is lower than that of ``S`` at both
  capitals, otherwise ``S``. Sharpe and CAGR are context, not a verdict.

The closes are dividend-adjusted (yfinance): no dividend lands in cash, so the
replay is, if anything, short of cash compared with an account that receives
its distributions.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import sys
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np
import pandas as pd

SCRIPTS_DIR = Path(__file__).resolve().parent
PROJECTS_DIR = SCRIPTS_DIR.parent.parent / "projects"

SYMBOLS = ["SPY", "QQQ", "IEF", "GLD"]
DOWNLOAD_START, DOWNLOAD_END = "2003-01-01", "2026-10-03"
FIRST_MONTH, LAST_MONTH = "2005-01", "2026-09"
CAPITALS = [10_000.0, 100_000.0]
POLICIES = ["N", "S", "R"]
FEE = 0.0005
TRADING_DAYS = 252


def load_harness():
    """The paper harness rebalance module, imported from its file (one copy only)."""
    found = sorted(PROJECTS_DIR.glob("*/paper_harness/rebalance.py"))
    if len(found) != 1:
        raise RuntimeError(f"expected one paper_harness/rebalance.py, found {len(found)}")
    spec = importlib.util.spec_from_file_location("paper_harness_rebalance", found[0])
    module = importlib.util.module_from_spec(spec)
    # registered before execution: its dataclasses look their module up there
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def cycle_defaults() -> dict:
    """The ``CycleConfig`` defaults, read from the orchestrator source (no import of the package)."""
    found = sorted(PROJECTS_DIR.glob("*/paper_harness/orchestrator.py"))
    if len(found) != 1:
        raise RuntimeError(f"expected one paper_harness/orchestrator.py, found {len(found)}")
    text = found[0].read_text(encoding="utf-8")
    block = text[text.index("class CycleConfig"):]
    out = {}
    for name in ("budget_per_line", "max_weight", "lookback", "band", "min_notional", "cash_reserve"):
        line = next(ln for ln in block.splitlines() if ln.strip().startswith(f"{name}:"))
        out[name] = float(line.split("=")[1])
    out["lookback"] = int(out["lookback"])
    return out


# ---------------------------------------------------------------- data


def read_close(path: Path) -> pd.Series:
    df = pd.read_csv(path, parse_dates=["Date"], index_col="Date")
    s = df["Close"].astype(float).dropna()
    s.index = pd.DatetimeIndex(s.index).tz_localize(None).normalize()
    return s.groupby(level=0).last().sort_index()


def sha256(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rebalance_dates(index: pd.DatetimeIndex, first: str = FIRST_MONTH, last: str = LAST_MONTH) -> list:
    """Last session of each month from ``first`` to ``last`` (``YYYY-MM``), both included."""
    s = pd.Series(index, index=index)
    ends = s.groupby(index.to_period("M")).max()
    ends = ends[(ends.index >= pd.Period(first, "M")) & (ends.index <= pd.Period(last, "M"))]
    return list(ends.values)


# ---------------------------------------------------------------- simulation


@dataclass
class Book:
    cash: float
    shares: dict = field(default_factory=dict)

    def equity(self, prices: dict) -> float:
        return self.cash + sum(q * prices[s] for s, q in self.shares.items() if q)


def execute(book: Book, orders, prices: dict, fee: float = FEE) -> dict:
    """Send the orders in plan order, as the adapter does: a buy above the cash stops the cycle.

    Returns the number of orders filled and whether the cycle stopped.
    """
    filled = 0
    for o in orders:
        notional = abs(o.quantity) * prices[o.symbol]
        if o.quantity > 0 and notional > book.cash + 1e-9:
            return {"filled": filled, "stopped": True}
        book.cash -= o.quantity * prices[o.symbol] + fee * notional
        book.shares[o.symbol] = book.shares.get(o.symbol, 0) + o.quantity
        filled += 1
    return {"filled": filled, "stopped": False}


def plan_shortfall(orders, cash: float) -> float:
    """Buys of the plan minus its cash and sells (positive = the plan overdraws)."""
    buys = sum(o.notional for o in orders if o.quantity > 0)
    sells = sum(o.notional for o in orders if o.quantity < 0)
    return buys - (cash + sells)


def distance_to_targets(book: Book, targets: dict, prices: dict) -> float:
    """Sum over lines of |weight held - target weight| after the cycle."""
    equity = book.equity(prices)
    names = set(targets) | {s for s, q in book.shares.items() if q}
    return sum(abs(book.shares.get(s, 0) * prices[s] / equity - targets.get(s, 0.0)) for s in names)


def simulate(harness, closes: pd.DataFrame, dates: list, capital: float, policy: str,
             cfg: dict, fee: float = FEE) -> dict:
    """Replay one policy from ``capital`` in cash; daily marks between the rebalances."""
    if policy not in POLICIES:
        raise ValueError(f"unknown policy {policy}")
    book = Book(cash=capital)
    rebal = set(pd.DatetimeIndex(dates))
    start = pd.Timestamp(dates[0])
    marks, cycles = [], []
    for day, row in closes.loc[start:].iterrows():
        prices = {s: float(row[s]) for s in closes.columns}
        if day in rebal:
            history = closes.loc[:day]
            window = {s: history[s].values[-(cfg["lookback"] + 1):] for s in closes.columns}
            targets = harness.inverse_vol_weights(window, cfg["budget_per_line"],
                                                  cfg["max_weight"], cfg["lookback"])
            equity = book.equity(prices)
            kw = dict(band=cfg["band"], min_notional=cfg["min_notional"],
                      cash_reserve=cfg["cash_reserve"])
            free = harness.plan_orders(targets, book.shares, prices, equity, **kw)
            if policy == "N":
                plan = free
            else:
                plan = harness.plan_orders(targets, book.shares, prices, equity, **kw,
                                           cash=book.cash, release_skipped_sells=(policy == "R"))
            short = plan_shortfall(free, book.cash)
            run = execute(book, plan, prices, fee)
            cycles.append({
                "date": pd.Timestamp(day).strftime("%Y-%m-%d"),
                "equity": equity,
                "free_shortfall_pct": max(0.0, short) / equity,
                "binds": plan != free,
                "stopped": run["stopped"],
                "orders": run["filled"],
                "cash_after_pct": book.cash / book.equity(prices),
                "distance": distance_to_targets(book, targets, prices),
            })
        marks.append((day, book.equity(prices)))
    curve = pd.Series([v for _, v in marks], index=pd.DatetimeIndex([d for d, _ in marks]))
    return {"cycles": cycles, "curve": curve}


def summarize(sim: dict) -> dict:
    cycles = sim["cycles"]
    curve = sim["curve"]
    rets = curve.pct_change().dropna()
    years = (curve.index[-1] - curve.index[0]).days / 365.25
    infeasible = [c for c in cycles if c["free_shortfall_pct"] > 0]
    binding = [c for c in cycles if c["binds"]]
    return {
        "cycles": len(cycles),
        "stopped_cycles": sum(c["stopped"] for c in cycles),
        "overdrawing_plans": len(infeasible),
        "overdrawing_share": round(len(infeasible) / len(cycles), 4),
        "max_overdraw_pct_equity": round(max((c["free_shortfall_pct"] for c in cycles), default=0.0), 5),
        "binding_cycles": len(binding),
        "mean_distance_binding": (round(float(np.mean([c["distance"] for c in binding])), 5)
                                  if binding else None),
        "mean_distance_all": round(float(np.mean([c["distance"] for c in cycles])), 5),
        "min_cash_after_pct": round(min(c["cash_after_pct"] for c in cycles), 5),
        "orders_per_year": round(sum(c["orders"] for c in cycles) / years, 2),
        "sharpe_rf0": round(float(rets.mean() / rets.std(ddof=1) * math.sqrt(TRADING_DAYS)), 4),
        "cagr": round(float((curve.iloc[-1] / curve.iloc[0]) ** (1 / years) - 1), 4),
        "first_stopped": next((c["date"] for c in cycles if c["stopped"]), None),
    }


def verdict(table: dict) -> dict:
    """The pre-registered rule of #19113, applied to ``table[capital][policy]``."""
    caps = list(table)
    defect = any(table[k]["N"]["stopped_cycles"] > 0 or table[k]["N"]["overdrawing_plans"] > 0
                 for k in caps)
    eligible = {p: all(table[k][p]["min_cash_after_pct"] >= 0 and table[k][p]["stopped_cycles"] == 0
                       for k in caps) for p in ("S", "R")}

    def lower(k):
        r, s = table[k]["R"]["mean_distance_binding"], table[k]["S"]["mean_distance_binding"]
        return r is not None and s is not None and r < s

    if eligible["R"] and (not eligible["S"] or all(lower(k) for k in caps)):
        default = "R"
    elif eligible["S"]:
        default = "S"
    else:
        default = None
    return {"defect": "CONFIRME" if defect else "NON REPRODUIT",
            "eligible": eligible, "default_policy": default}


def run(data_dir: Path) -> dict:
    from panier_loader import ensure_symbol

    harness = load_harness()
    cfg = cycle_defaults()
    paths = {}
    for sym in SYMBOLS:
        p = ensure_symbol(sym, DOWNLOAD_START, DOWNLOAD_END, panier_dir=data_dir)
        if p is None:
            raise RuntimeError(f"no data for {sym}")
        paths[sym] = Path(p)
    closes = pd.concat({s: read_close(paths[s]) for s in SYMBOLS}, axis=1, join="inner").dropna()
    dates = rebalance_dates(closes.index)
    table = {}
    for capital in CAPITALS:
        table[f"{capital:.0f}"] = {p: summarize(simulate(harness, closes, dates, capital, p, cfg))
                                   for p in POLICIES}
    return {
        "issue": 19113,
        "parameters": {**cfg, "fee": FEE, "capitals": CAPITALS, "first_month": FIRST_MONTH,
                       "last_month": LAST_MONTH, "execution": "close of the last session of the month"},
        "data": {s: {"file": paths[s].name, "sha256": sha256(paths[s])} for s in SYMBOLS},
        "sessions": [closes.index[0].strftime("%Y-%m-%d"), closes.index[-1].strftime("%Y-%m-%d")],
        "rebalances": len(dates),
        "results": table,
        "verdict": verdict(table),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--data-dir", type=Path, required=True,
                    help="directory of the price CSVs (downloaded there when missing)")
    ap.add_argument("--out", type=Path,
                    default=SCRIPTS_DIR.parent / "results" / "plan_cash_feasibility.json")
    args = ap.parse_args()
    result = run(args.data_dir)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in ("rebalances", "verdict")}, indent=2))
    for cap, row in result["results"].items():
        for p, m in row.items():
            print(cap, p, {k: m[k] for k in ("stopped_cycles", "overdrawing_plans", "max_overdraw_pct_equity",
                                              "binding_cycles", "mean_distance_binding", "min_cash_after_pct",
                                              "orders_per_year", "sharpe_rf0", "cagr")})


if __name__ == "__main__":
    main()
