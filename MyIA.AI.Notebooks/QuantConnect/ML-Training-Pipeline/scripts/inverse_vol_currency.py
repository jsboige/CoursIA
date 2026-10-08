"""Inverse-volatility weights for a euro investor: volatility in USD or in EUR (#19072).

Pre-registration: issue #19072 (2026-10-04T06:42:34Z), published before any
computation. The rule under study is the one of the paper harness
(``paper_harness/rebalance.py``): ``realized_vol`` (21 simple daily returns,
``ddof=1``, sqrt(252)) and ``inverse_vol_weights`` (target / vol, capped per
line, total capped at 1). This script imports that module rather than copying
it, so the experiment measures the rule the harness runs.

The harness measures each line's volatility on the USD closes of SPY, QQQ, IEF
and GLD, while a euro investor holds them unhedged: the return they live is the
US return converted to EUR. Two conventions are compared:

- ``U`` (baseline): volatility of the USD closes;
- ``F`` (candidate): volatility of the closes converted to EUR,
  ``P_EUR = P_USD / EURUSD`` with ``EURUSD=X`` quoted in USD per EUR.

H1 (primary) -- forecast fidelity: for each holding month and line, the loss is
``(ln sigma_EUR(month) - ln sigma_hat)^2``; ``d(m)`` is the mean over lines of
``loss_U - loss_F``, tested by a circular block bootstrap of 6 months.

H2 -- net Sharpe in EUR at the 0.025 target: monthly rebalance at the last
session of each month, 3-point band, 5 bp fees on the traded value, cash at 0 %.
Both conventions hold the same assets: only the volatility measure changes.
Paired circular block bootstrap of 21 sessions (``circular_block_diff`` of the
#18921 verdict).

Both tests: 10,000 draws, seeds 0/1/7/42/99, the largest p is kept, Holm over
H1 and H2. ``BEATS``: statistic > 0, Holm p < 0.05 and statistic > 0 on each
half; ``NO BEATS``: statistic <= 0; otherwise ``INCONCLUSIVE``.

Control ``L`` (descriptive, from 2010): the target becomes the monthly
volatility of the UCITS line itself (Xetra closes in EUR), which does not share
the conversion noise of ``F``; the three forecasts U, F and L are scored on it.

Data: Yahoo daily closes through ``panier_loader.ensure_symbol``
(``auto_adjust=True``). The aggregate JSON goes to ``--out``; the CSVs stay
outside the repository (results-artifact-policy), their sha256 is in the JSON.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import sys
from pathlib import Path

import numpy as np
import pandas as pd

from strategy_metrics import TRADING_DAYS, cagr, max_drawdown, sharpe
from voltarget_strategy_verdict import circular_block_diff, holm

SCRIPTS_DIR = Path(__file__).resolve().parent
PROJECTS_DIR = SCRIPTS_DIR.parent.parent / "projects"

SIGNALS = ["SPY", "QQQ", "IEF", "GLD"]
FX = "EURUSD=X"
LINES = {"SPY": "SXR8.DE", "QQQ": "SXRV.DE", "IEF": "IUSM.DE", "GLD": "4GLD.DE"}

TARGETS = [0.015, 0.025, 0.04]
VERDICT_TARGET = 0.025
MAX_WEIGHT = 0.5
LOOKBACK = 21
BAND = 0.03
FEE = 0.0005
FX_ERROR = 0.04
MAX_FX_DROPS = 20

DOWNLOAD_START, DOWNLOAD_END = "2003-01-01", "2026-10-03"
HOLD_START, HOLD_END = "2005-01-01", "2026-09-30"
HALF_SPLIT = "2015-12-01"
L_START = "2010-01-01"
MIN_MONTH_RETURNS = 10

SEEDS = [0, 1, 7, 42, 99]
DRAWS = 10_000
DAY_BLOCK = 21
MONTH_BLOCK = 6


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


# ---------------------------------------------------------------- data


def read_close(path: Path) -> pd.Series:
    df = pd.read_csv(path, parse_dates=["Date"], index_col="Date")
    s = df["Close"].astype(float).dropna()
    s.index = pd.DatetimeIndex(s.index).tz_localize(None).normalize()
    return s.groupby(level=0).last().sort_index()


def sha256(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def drop_fx_errors(fx: pd.Series, threshold: float = FX_ERROR,
                   max_drops: int = MAX_FX_DROPS) -> tuple[pd.Series, list[str]]:
    """Remove, one at a time, the dates whose FX move exceeds ``threshold``.

    Dropping the first offending date and recomputing keeps the day after an
    isolated bad print (its return is then measured against the day before).
    A run of drops longer than ``max_drops`` means a level shift, not a bad
    print: it raises instead of silently eating the series.
    """
    fx = fx.copy()
    dropped: list[str] = []
    while True:
        moves = fx.pct_change().abs()
        bad = moves[moves > threshold]
        if bad.empty:
            return fx, dropped
        if len(dropped) >= max_drops:
            raise RuntimeError(f"more than {max_drops} FX moves above {threshold}")
        first = bad.index[0]
        dropped.append(first.strftime("%Y-%m-%d"))
        fx = fx.drop(first)


def build_panel(us_closes: dict[str, pd.Series], fx: pd.Series) -> dict:
    """USD and EUR closes on the strict common calendar, after the FX error rule."""
    if float(fx.median()) <= 1.0:
        raise RuntimeError("EURUSD median <= 1: the quote is not USD per EUR, stop")
    usd = pd.concat(us_closes, axis=1, join="inner")
    joined = usd.join(fx.rename("fx"), how="inner").dropna()
    fx_clean, dropped = drop_fx_errors(joined["fx"])
    joined = joined.loc[fx_clean.index]
    usd = joined[list(us_closes)]
    eur = usd.div(joined["fx"], axis=0)
    return {"usd": usd, "eur": eur, "fx": joined["fx"], "fx_dropped": dropped}


def first_rebalance_month(start: str) -> pd.Timestamp:
    """First day of the month before ``start``: its last session opens the first holding month."""
    return pd.Timestamp(start) - pd.offsets.MonthBegin(1)


def last_holding_month() -> pd.Timestamp:
    """First day of the month of ``HOLD_END``: rebalances before it open a month inside the window."""
    return pd.Timestamp(HOLD_END).replace(day=1)


def month_ends(index: pd.DatetimeIndex) -> pd.DatetimeIndex:
    """Last session of each calendar month present in ``index``."""
    s = pd.Series(index, index=index)
    return pd.DatetimeIndex(s.groupby([index.year, index.month]).max().to_numpy())


# ---------------------------------------------------------------- the rule


def forecasts(harness, prices: pd.DataFrame, date: pd.Timestamp) -> dict[str, float | None]:
    """``realized_vol`` of each column on the ``LOOKBACK + 1`` closes up to ``date``."""
    window = prices.loc[:date].tail(LOOKBACK + 1)
    return {c: harness.realized_vol(window[c].tolist(), LOOKBACK) for c in prices.columns}


def target_weights(harness, prices: pd.DataFrame, date: pd.Timestamp,
                   target: float) -> dict[str, float]:
    window = prices.loc[:date].tail(LOOKBACK + 1)
    closes = {c: window[c].tolist() for c in prices.columns}
    return harness.inverse_vol_weights(closes, target, MAX_WEIGHT, LOOKBACK)


def simulate(returns: pd.DataFrame, schedule: dict[pd.Timestamp, dict[str, float]],
             band: float = BAND, fee: float = FEE) -> dict:
    """Daily net returns of a drifting portfolio rebalanced on ``schedule``.

    ``returns``: daily returns of the held assets (EUR for both conventions).
    At each scheduled close a line trades only when its weight gap reaches
    ``band`` (an exit to zero always trades), the fee is ``fee`` times the
    traded weight, paid out of the portfolio. Cash earns 0 and may dip slightly
    below zero when untraded lines have drifted up: its minimum is reported.
    ``turnover`` is the traded weight of each session (0 between rebalances).
    """
    cols = list(returns.columns)
    w = dict.fromkeys(cols, 0.0)
    started = False
    out, moves, traded_total, fees_total, min_cash = [], [], 0.0, 0.0, 1.0
    for t, row in returns.iterrows():
        r_p = 0.0
        if started:
            r_p = sum(w[c] * row[c] for c in cols)
            growth = 1.0 + r_p
            w = {c: w[c] * (1.0 + row[c]) / growth for c in cols}
        fee_frac, moved = 0.0, 0.0
        if t in schedule:
            tgt = schedule[t]
            for c in cols:
                goal = float(tgt.get(c, 0.0))
                gap = goal - w[c]
                if gap == 0.0:
                    continue
                if (goal == 0.0 and w[c] != 0.0) or abs(gap) >= band:
                    moved += abs(gap)
                    w[c] = goal
            fee_frac = fee * moved
            traded_total += moved
            fees_total += fee_frac
            started = True
        if started:
            min_cash = min(min_cash, 1.0 - sum(w.values()))
        out.append((t, (1.0 + r_p) * (1.0 - fee_frac) - 1.0))
        moves.append((t, moved))
    series = pd.Series(dict(out)).sort_index()
    return {"returns": series, "turnover": pd.Series(dict(moves)).sort_index(),
            "traded": traded_total, "fees": fees_total, "min_cash_weight": min_cash}


# ---------------------------------------------------------------- tests


def block_bootstrap_mean(x, block: int, draws: int = DRAWS, seed: int = 0) -> dict:
    """Mean of ``x`` and its circular block bootstrap (one-sided p of mean <= 0)."""
    x = np.asarray(x, dtype=float)
    n = len(x)
    if n < block:
        raise ValueError(f"only {n} points for a block of {block}")
    rng = np.random.default_rng(seed)
    n_blocks = math.ceil(n / block)
    starts = rng.integers(0, n, size=(draws, n_blocks))
    pos = ((starts[:, :, None] + np.arange(block)) % n).reshape(draws, -1)[:, :n]
    means = x[pos].mean(axis=1)
    return {"observed": float(x.mean()), "p_one_sided": float((means <= 0).mean()),
            "ci95": [float(np.quantile(means, 0.025)), float(np.quantile(means, 0.975))]}


def verdict(observed: float, p_holm: float, halves: list[float]) -> str:
    """Pre-registered rule of #19072, for one hypothesis."""
    if observed <= 0:
        return "NO BEATS"
    if p_holm < 0.05 and all(h > 0 for h in halves):
        return "BEATS"
    return "INCONCLUSIVE"


def month_vol(returns: pd.Series) -> float | None:
    r = returns.dropna()
    if len(r) < MIN_MONTH_RETURNS:
        return None
    return float(r.std(ddof=1) * math.sqrt(TRADING_DAYS))


def forecast_losses(harness, estimators: dict[str, pd.DataFrame], target_prices: pd.DataFrame,
                    rebalances: pd.DatetimeIndex) -> pd.DataFrame:
    """One row per (holding month, line): realised vol and each estimator's forecast.

    The holding month of a rebalance is the calendar month that follows it; its
    realised volatility is measured on the daily returns of ``target_prices``
    during that month, on the target series' own sessions.
    """
    target_returns = target_prices.pct_change()
    rows = []
    for date in rebalances:
        nxt = date + pd.offsets.MonthBegin(1)
        month = target_returns.loc[(target_returns.index >= nxt)
                                   & (target_returns.index < nxt + pd.offsets.MonthBegin(1))]
        fc = {name: forecasts(harness, prices, date) for name, prices in estimators.items()}
        for line in target_prices.columns:
            realised = month_vol(month[line])
            sig = {name: fc[name].get(line) for name in estimators}
            if realised is None or any(v is None or v <= 0 for v in sig.values()):
                continue
            row = {"month": nxt.strftime("%Y-%m"), "line": line, "realised": realised}
            for name, v in sig.items():
                row[f"hat_{name}"] = v
                row[f"err_{name}"] = math.log(realised) - math.log(v)
                row[f"loss_{name}"] = row[f"err_{name}"] ** 2
            rows.append(row)
    return pd.DataFrame(rows)


def loss_summary(table: pd.DataFrame, names: list[str]) -> dict:
    """Per-line RMS log error and signed bias (mean of ln realised - ln forecast)."""
    out = {}
    for line, grp in table.groupby("line"):
        out[line] = {name: {"rms_log_error": round(float(np.sqrt(grp[f"loss_{name}"].mean())), 4),
                            "bias_log": round(float(grp[f"err_{name}"].mean()), 4)}
                     for name in names}
        out[line]["months"] = int(len(grp))
    return out


def monthly_diff(table: pd.DataFrame, base: str, cand: str) -> pd.Series:
    """``d(m)``: mean over lines of loss(base) - loss(cand), indexed by month."""
    d = table.assign(d=table[f"loss_{base}"] - table[f"loss_{cand}"])
    return d.groupby("month")["d"].mean().sort_index()


def halves_of(index_like, values: pd.Series) -> tuple[pd.Series, pd.Series]:
    first = values[index_like < HALF_SPLIT]
    second = values[index_like >= HALF_SPLIT]
    return first, second


def worst_p(fn, seeds=SEEDS) -> tuple[dict, list[float]]:
    runs = [fn(seed) for seed in seeds]
    ps = [r["p_one_sided"] for r in runs]
    best = dict(runs[0])
    best["p_one_sided"] = max(ps)
    return best, ps


# ---------------------------------------------------------------- run


def strategy_stats(rets: pd.Series, sim: dict, schedule: dict) -> dict:
    years = (rets.index[-1] - rets.index[0]).days / 365.25
    weights = pd.DataFrame(list(schedule.values())).fillna(0.0)
    return {
        "sharpe": round(float(sharpe(rets)), 4),
        "cagr": round(cagr(rets, years), 4),
        "max_drawdown": round(max_drawdown(rets), 4),
        "vol_annual": round(float(rets.std(ddof=1) * math.sqrt(TRADING_DAYS)), 4),
        "mean_target_weight": {c: round(float(weights[c].mean()), 4) for c in weights.columns},
        "mean_gross_exposure": round(float(weights.sum(axis=1).mean()), 4),
        "turnover_per_year": round(sim["traded"] / years, 4),
        "fees_total": round(sim["fees"], 5),
        "min_cash_weight": round(sim["min_cash_weight"], 4),
    }


def run(data_dir: Path, targets: list[float]) -> dict:
    from panier_loader import ensure_symbol

    harness = load_harness()
    paths = {}
    for sym in SIGNALS + [FX] + list(LINES.values()):
        p = ensure_symbol(sym, DOWNLOAD_START, DOWNLOAD_END, panier_dir=data_dir)
        if p is None:
            raise RuntimeError(f"no data for {sym}")
        paths[sym] = Path(p)

    panel = build_panel({s: read_close(paths[s]) for s in SIGNALS}, read_close(paths[FX]))
    usd, eur = panel["usd"], panel["eur"]
    eur_ret = eur.pct_change()

    rebal = month_ends(usd.index)
    rebal = rebal[(rebal >= first_rebalance_month(HOLD_START)) & (rebal < last_holding_month())]
    rebal = pd.DatetimeIndex([d for d in rebal if len(usd.loc[:d]) >= LOOKBACK + 1])

    # H1 -- forecast fidelity against next-month EUR volatility
    h1_table = forecast_losses(harness, {"U": usd, "F": eur}, eur, rebal)
    h1_table = h1_table[(h1_table["month"] >= HOLD_START[:7]) & (h1_table["month"] <= HOLD_END[:7])]
    # a holding month with fewer than MIN_MONTH_RETURNS sessions is not scored: listed, not hidden
    expected = {(d + pd.offsets.MonthBegin(1)).strftime("%Y-%m") for d in rebal}
    unscored = sorted(m for m in expected - set(h1_table["month"])
                      if HOLD_START[:7] <= m <= HOLD_END[:7])
    d = monthly_diff(h1_table, "U", "F")
    months = pd.Index(pd.to_datetime(d.index + "-01"))
    h1_boot, h1_ps = worst_p(lambda s: block_bootstrap_mean(d.to_numpy(), MONTH_BLOCK, DRAWS, s))
    d1, d2 = halves_of(months, pd.Series(d.to_numpy(), index=months))

    # H2 and descriptive stats -- simulated portfolios, returns in EUR
    sims = {}
    hold = (eur_ret.index >= HOLD_START) & (eur_ret.index <= HOLD_END)
    for target in targets:
        for name, prices in (("U", usd), ("F", eur)):
            schedule = {date: target_weights(harness, prices, date, target) for date in rebal}
            sim = simulate(eur_ret.fillna(0.0), schedule)
            rets = sim["returns"][hold]
            sims[(target, name)] = (rets, sim, schedule)

    comparisons = {}
    for target in targets:
        ru, rf = sims[(target, "U")][0], sims[(target, "F")][0]
        boot, ps = worst_p(lambda s: circular_block_diff(rf, ru, DAY_BLOCK, DRAWS, s))
        hu, hf = halves_of(ru.index, ru), halves_of(rf.index, rf)
        halves = [float(sharpe(hf[k]) - sharpe(hu[k])) for k in (0, 1)]
        comparisons[target] = {"diff_sharpe_F_minus_U": round(boot["observed"], 4),
                               "p_one_sided_max": round(boot["p_one_sided"], 4),
                               "p_by_seed": [round(p, 4) for p in ps],
                               "ci95_seed0": [round(v, 4) for v in boot["ci95"]],
                               "halves": [round(h, 4) for h in halves]}

    primary = {"H1": h1_boot["p_one_sided"]}
    if VERDICT_TARGET in comparisons:
        primary["H2"] = comparisons[VERDICT_TARGET]["p_one_sided_max"]
    p_holm = holm(primary)

    h1 = {"statistic_mean_d": round(h1_boot["observed"], 6),
          "p_one_sided_max": round(h1_boot["p_one_sided"], 4),
          "p_by_seed": [round(p, 4) for p in h1_ps],
          "ci95_seed0": [round(v, 6) for v in h1_boot["ci95"]],
          "p_holm": round(p_holm["H1"], 4),
          "halves_mean_d": [round(float(d1.mean()), 6), round(float(d2.mean()), 6)],
          "months": int(len(d)), "months_unscored": unscored, "pairs": int(len(h1_table)),
          "by_line": loss_summary(h1_table, ["U", "F"])}
    h1["verdict"] = verdict(h1_boot["observed"], p_holm["H1"], h1["halves_mean_d"])

    result = {
        "experiment": "inverse_vol_currency (#19072)",
        "preregistration": "https://github.com/jsboige/CoursIA/issues/19072",
        "window": {"hold_start": HOLD_START, "hold_end": HOLD_END, "half_split": HALF_SPLIT,
                   "sessions": int(hold.sum()), "rebalances": int(len(rebal))},
        "parameters": {"lookback": LOOKBACK, "max_weight": MAX_WEIGHT, "band": BAND,
                       "fee": FEE, "targets": targets, "verdict_target": VERDICT_TARGET,
                       "seeds": SEEDS, "draws": DRAWS, "day_block": DAY_BLOCK,
                       "month_block": MONTH_BLOCK},
        "data": {"source": "Yahoo Finance via panier_loader.ensure_symbol (auto_adjust=True)",
                 "sha256": {s: sha256(p) for s, p in paths.items()},
                 "fx_median": round(float(panel["fx"].median()), 4),
                 "fx_dropped_dates": panel["fx_dropped"],
                 "common_sessions": int(len(usd))},
        "H1": h1,
        "sharpe_comparison": {str(t): v for t, v in comparisons.items()},
        "strategies": {str(t): {name: strategy_stats(*sims[(t, name)]) for name in ("U", "F")}
                       for t in targets},
    }
    if VERDICT_TARGET in comparisons:
        c = comparisons[VERDICT_TARGET]
        result["H2"] = dict(c, p_holm=round(p_holm["H2"], 4),
                            verdict=verdict(c["diff_sharpe_F_minus_U"], p_holm["H2"], c["halves"]))

    result["L_control"] = l_control(harness, usd, eur, paths)
    return result


def l_control(harness, usd: pd.DataFrame, eur: pd.DataFrame, paths: dict) -> dict:
    """Descriptive: forecasts U, F, L scored on the UCITS lines' own monthly volatility."""
    lines = pd.concat({sig: read_close(paths[LINES[sig]]) for sig in SIGNALS}, axis=1, sort=True)
    rebal = month_ends(usd.index)
    rebal = rebal[(rebal >= first_rebalance_month(L_START)) & (rebal < last_holding_month())]
    keep = []
    for date in rebal:
        if all(lines[s].loc[:date].dropna().shape[0] >= LOOKBACK + 1 for s in SIGNALS):
            keep.append(date)
    rebal = pd.DatetimeIndex(keep)
    rows = []
    for sig in SIGNALS:
        own = lines[[sig]].dropna()
        table = forecast_losses(harness, {"U": usd[[sig]], "F": eur[[sig]], "L": own}, own, rebal)
        rows.append(table)
    table = pd.concat(rows, ignore_index=True)
    table = table[table["month"] <= HOLD_END[:7]]
    out = {"lines": LINES, "months": int(table["month"].nunique()),
           "first_month": str(table["month"].min()), "by_line": loss_summary(table, ["U", "F", "L"])}
    for base, cand in (("U", "F"), ("U", "L"), ("F", "L")):
        d = monthly_diff(table, base, cand)
        b = block_bootstrap_mean(d.to_numpy(), MONTH_BLOCK, DRAWS, SEEDS[0])
        out[f"mean_d_{base}_minus_{cand}"] = {"observed": round(b["observed"], 6),
                                              "ci95_seed0": [round(v, 6) for v in b["ci95"]]}
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--data-dir", type=Path, required=True,
                    help="directory of the Yahoo CSVs (downloaded there when missing)")
    ap.add_argument("--out", type=Path, help="write the aggregate JSON there")
    ap.add_argument("--targets", type=float, nargs="+", default=TARGETS)
    args = ap.parse_args()
    result = run(args.data_dir, args.targets)
    text = json.dumps(result, indent=2, ensure_ascii=False)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
