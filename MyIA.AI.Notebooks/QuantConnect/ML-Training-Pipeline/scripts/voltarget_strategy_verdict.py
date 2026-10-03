"""Strategy verdict of the #18921 experiment, from the QuantConnect chart files.

Pre-registration: issue #18921, comment 5964767205 (2026-10-03T02:44:26Z),
section 4. Every input here is a chart JSON written by
``scripts/qc-mcp-lite/server.py::read_backtest_chart``:

- ``coursia-18921-equity`` — net portfolio value at each close, carried by five
  interleaved series (``e0``..``e4``, one point every 5 sessions each): the
  built-in "Strategy Equity" chart is stored on a uniform ~1.3-day grid over
  20 years, so each interleaved series keeps its real dates;
- ``Exposure`` — long/short ratios, on QC's ~1.3-day grid;
- ``Portfolio Turnover`` — turnover as a fraction of the portfolio, same grid.

Daily net returns are read from the equity series and filtered down to the
common trading sessions (taken from a CSV of SPY daily bars: no trading
session, no return — a weekend point must not count as a flat day). The
verdict block is 2007-01-01..2026-08-31; the contamination sub-block
2025-01-01..2026-08-31 is reported apart and never decides.

Sharpe = mean / std * sqrt(252) of daily net returns, risk-free 0 (the Sharpe
printed by QC is reported alongside). Candidate vs baseline: paired circular
block bootstrap, blocks of 21 sessions, 10,000 draws, same indices for both
series; one-sided p = share of draws where the difference is <= 0. Holm at
0.05 across the two candidates. ``BEATS`` needs diff > 0, Holm p < 0.05 and
diff greater than the largest of the 8 placebo diffs; ``NO BEATS`` is diff <=
0; everything else is ``INCONCLUSIVE``.

Outputs the aggregate JSON (verdicts, per-variant stats) on stdout, and with
``--out-dir`` also writes it there (``--out-name``, default
``voltarget_strategy_verdict.json``) — the falsifiability aggregate committed
to the repo. The chart JSONs stay outside it (results-artifact-policy).

Experiment 5a-bis (pre-registration: issue #18921, comment 5965207764) reruns
the same grid with the rebalance calendar fixed. ``--reference-dir`` points to
the chart JSONs of the 5a run and adds its section 5 table: each variant's
stats under both calendars, and rv21 (this run) minus rv21 (reference run)
with the same paired bootstrap. That table is descriptive and decides nothing.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
import pandas as pd

TICKERS = ["SPY", "QQQ", "IEF", "GLD"]
BASELINE = "rv21"
CANDIDATES = ["har", "tsfm"]
PLACEBO_SEEDS = [0, 1, 7, 42, 99, 123, 256, 1000]
VERDICT_START, VERDICT_END = "2007-01-01", "2026-08-31"
CONTAMINATION_START = "2025-01-01"
BLOCK, DRAWS, RNG_SEED = 21, 10_000, 18921
EQUITY_SERIES = [f"e{k}" for k in range(5)]
TRADING_DAYS = 252
REPORTED = ["sharpe", "cagr", "max_drawdown", "gross_exposure_mean", "turnover_chart_mean"]
PREREG_5A = "issue #18921, comment 5964767205 (2026-10-03T02:44:26Z), section 4"


def _points(values: list) -> tuple[list, list]:
    """Timestamps and values of chart points: [t, v], [t, o, h, l, c] or {x, y}."""
    ts, ys = [], []
    for v in values:
        if isinstance(v, dict):
            ts.append(v["x"]); ys.append(v["y"])
        else:
            ts.append(v[0]); ys.append(v[-1])      # candle: the close
    return ts, ys


def _ny_dates(timestamps: list) -> pd.DatetimeIndex:
    idx = pd.to_datetime(timestamps, unit="s", utc=True).tz_convert("America/New_York")
    return idx.normalize().tz_localize(None)


def daily_close_equity(chart: dict) -> pd.Series:
    """Merge the interleaved equity series into one daily close series."""
    ts, ys = [], []
    for key in EQUITY_SERIES:
        s = (chart.get("series") or {}).get(key)
        if not s:
            raise ValueError(f"missing equity series {key!r}: re-run the backtest "
                             "with the coursia-18921-equity chart")
        t, y = _points(s["values"])
        ts += t; ys += y
    equity = pd.Series(ys, index=_ny_dates(ts)).sort_index()
    if equity.index.duplicated().any():
        raise ValueError("two equity points on the same session: the interleaving drifted")
    return equity


def daily_returns(equity: pd.Series, sessions: pd.DatetimeIndex) -> pd.Series:
    """Daily net returns on the trading sessions of the block.

    Every session must carry an equity point: a missing close would silently
    turn the next return into a two-session return.
    """
    missing = sessions.difference(equity.index)
    if len(missing):
        raise ValueError(f"{len(missing)} sessions without an equity point, "
                         f"first {missing[0]:%Y-%m-%d}")
    return equity.loc[equity.index.isin(sessions)].pct_change().dropna()


def load_sessions(spy_csv: Path, start: str = VERDICT_START, end: str = VERDICT_END) -> pd.DatetimeIndex:
    bars = pd.read_csv(spy_csv, index_col=0, parse_dates=True)
    idx = bars.index
    return idx[(idx >= start) & (idx <= end)]


def series_values(chart: dict, key: str) -> pd.Series:
    """One chart series by date (last value of the date)."""
    s = (chart.get("series") or {}).get(key)
    if not s:
        raise ValueError(f"missing series {key!r}")
    ts, ys = _points(s["values"])
    return pd.Series(ys, index=_ny_dates(ts)).groupby(level=0).last().sort_index()


def _sharpe(r: np.ndarray, axis: int | None = None) -> np.ndarray:
    return r.mean(axis=axis) / r.std(axis=axis, ddof=1) * math.sqrt(TRADING_DAYS)


def circular_block_diff(returns_a: pd.Series, returns_b: pd.Series,
                        block: int = BLOCK, draws: int = DRAWS,
                        seed: int = RNG_SEED, chunk: int = 500) -> dict:
    """Sharpe(a) - Sharpe(b) and its paired circular block bootstrap.

    Both series are resampled with the same indices. The seed is the same for
    every comparison: all pairs see the very same 10,000 draws.
    """
    if not returns_a.index.equals(returns_b.index):
        raise ValueError("the two return series do not cover the same sessions")
    a, b = returns_a.to_numpy(), returns_b.to_numpy()
    n = len(a)
    if n < block:
        raise ValueError(f"only {n} sessions for a block of {block}")
    rng = np.random.default_rng(seed)
    n_blocks = math.ceil(n / block)
    offsets = np.arange(block)
    diffs = np.empty(draws)
    for lo in range(0, draws, chunk):
        hi = min(draws, lo + chunk)
        starts = rng.integers(0, n, size=(hi - lo, n_blocks))
        pos = ((starts[:, :, None] + offsets) % n).reshape(hi - lo, -1)[:, :n]
        diffs[lo:hi] = _sharpe(a[pos], axis=1) - _sharpe(b[pos], axis=1)
    return {"observed": float(_sharpe(a) - _sharpe(b)),
            "p_one_sided": float((diffs <= 0).mean()),
            "ci95": [float(np.quantile(diffs, 0.025)), float(np.quantile(diffs, 0.975))]}


def holm(pvalues: dict[str, float]) -> dict[str, float]:
    """Holm step-down adjusted p-values."""
    order = sorted(pvalues, key=pvalues.get)
    m = len(order)
    adjusted, running = {}, 0.0
    for i, name in enumerate(order):
        running = max(running, (m - i) * pvalues[name])
        adjusted[name] = min(1.0, running)
    return adjusted


def _in_block(series: pd.Series) -> pd.Series:
    return series.loc[(series.index >= VERDICT_START) & (series.index <= VERDICT_END)]


def variant_stats(rets: pd.Series, exposure: dict, turnover: dict,
                  qc_stats: dict | None = None) -> dict:
    """Pre-reg section 4 reporting: Sharpe, CAGR, drawdown, exposure, turnover.

    Exposure and turnover come from QC's built-in charts, stored on a uniform
    grid of about 1.3 days: their means are averages over that grid, fit to
    compare variants with one another, not per-session figures. Turnover is a
    fraction of the portfolio (0.41 at the first rebalance, measured).
    """
    years = (rets.index[-1] - rets.index[0]).days / 365.25
    wealth = (1.0 + rets).cumprod()
    gross = _in_block(series_values(exposure, "Equity - Long Ratio")
                      + series_values(exposure, "Equity - Short Ratio"))
    turn = _in_block(series_values(turnover, "Portfolio Turnover"))
    out = {"n_days": int(len(rets)),
           "sharpe": round(float(_sharpe(rets.to_numpy())), 4),
           "cagr": round(float(wealth.iloc[-1] ** (1.0 / years) - 1.0), 4),
           "max_drawdown": round(float((wealth / wealth.cummax() - 1.0).min()), 4),
           "gross_exposure_mean": round(float(gross.mean()), 4),
           "turnover_chart_mean": round(float(turn.mean()), 6)}
    if qc_stats:
        st = qc_stats["statistics"]
        out["qc"] = {"backtest_id": qc_stats.get("backtestId", ""),
                     "sharpe": st["sharpeRatio"], "cagr": st["compoundingAnnualReturn"],
                     "drawdown": st["drawdown"], "orders": qc_stats.get("totalOrders")}
    return out


def qc_monthly_rv21(rv21_chart: dict, rebalance_dates: pd.DatetimeIndex) -> pd.DataFrame:
    """QC's rv21 in force during each month, one column per ticker.

    The chart is a step: the last rv21 computed by QC, plotted every 5
    sessions at the close. A point that falls on a rebalance date is dropped:
    whether it shows the old or the new value depends on event ordering
    (both are observed). Every other point between two rebalance dates must
    carry one value per month; anything else raises.
    """
    cols = {}
    for t in TICKERS:
        s = series_values(rv21_chart, t)
        s = s[~s.index.isin(rebalance_dates)]
        pos = rebalance_dates.searchsorted(s.index, side="right") - 1
        keep = pos >= 0
        g = pd.Series(s.to_numpy()[keep]).groupby(rebalance_dates[pos[keep]])
        if (g.max() / g.min() - 1.0).abs().max() > 1e-9:
            raise ValueError(f"{t}: two rv21 values within one month")
        cols[t] = g.first()
    return pd.DataFrame(cols)


def rv21_source_check(rv21_chart: dict, forecasts: pd.DataFrame) -> dict:
    """Pre-reg section 2: rv21 computed off QC vs rv21 computed by QC.

    A month whose four QC values all equal the previous month's is a month
    where QC did not rebalance: ``date_rules.month_start()`` without a symbol
    does not fire when the 1st of the month is not a trading day. Those
    months are counted and left out of the comparison (QC has no value of its
    own for them).
    """
    dates = pd.DatetimeIndex(sorted(forecasts["date"].unique()))
    qc = qc_monthly_rv21(rv21_chart, dates)
    skipped = qc.index[(qc == qc.shift()).all(axis=1)]
    fired = qc.drop(index=skipped)
    long = fired.stack().rename("rv21_qc").rename_axis(["date", "ticker"]).reset_index()
    m = forecasts[["date", "ticker", "rv21_vol_offqc"]].merge(long, on=["date", "ticker"])
    rel = (m["rv21_vol_offqc"] / m["rv21_qc"] - 1.0).abs()
    first_days = [d.replace(day=1) for d in skipped]
    return {"months": int(len(dates)),
            "months_without_qc_point": sorted(f"{d:%Y-%m}" for d in dates.difference(qc.index)),
            "months_not_rebalanced_by_qc": int(len(skipped)),
            "of_which_1st_on_weekend": int(sum(d.weekday() >= 5 for d in first_days)),
            "months_compared": int(len(fired)),
            "pairs": int(len(m)),
            "correlation": round(float(m["rv21_vol_offqc"].corr(m["rv21_qc"])), 4),
            "rel_gap_mean": round(float(rel.mean()), 4),
            "rel_gap_median": round(float(rel.median()), 4),
            "rel_gap_p95": round(float(rel.quantile(0.95)), 4),
            "rel_gap_max": round(float(rel.max()), 4)}


def gate(boot: dict, p_holm: float, placebo_max: float) -> str:
    """Pre-reg section 4 decision rule for one candidate."""
    if boot["observed"] <= 0:
        return "NO BEATS"
    if p_holm < 0.05 and boot["observed"] > placebo_max:
        return "BEATS"
    return "INCONCLUSIVE"


def compare(returns: dict[str, pd.Series]) -> dict:
    """Candidates and placebos against the baseline, Holm over the candidates."""
    boots = {m: circular_block_diff(returns[m], returns[BASELINE])
             for m in returns if m != BASELINE}
    adjusted = holm({c: boots[c]["p_one_sided"] for c in CANDIDATES})
    placebo_max = max(boots[f"placebo_{s}"]["observed"] for s in PLACEBO_SEEDS)
    out = {"candidates": {}, "placebo": {}, "placebo_max_diff": round(placebo_max, 4)}
    for c in CANDIDATES:
        b = boots[c]
        out["candidates"][c] = {"diff": round(b["observed"], 4),
                                "p_raw": round(b["p_one_sided"], 4),
                                "p_holm": round(adjusted[c], 4),
                                "ci95": [round(x, 4) for x in b["ci95"]],
                                "verdict": gate(b, adjusted[c], placebo_max)}
    for s in PLACEBO_SEEDS:
        b = boots[f"placebo_{s}"]
        out["placebo"][f"placebo_{s}"] = {"diff": round(b["observed"], 4),
                                          "p_raw": round(b["p_one_sided"], 4)}
    return out


def contamination(returns: dict[str, pd.Series]) -> dict:
    """Same comparison on the 2025-2026 sub-block; never decides the verdict."""
    return compare({m: r.loc[r.index >= CONTAMINATION_START] for m, r in returns.items()})


def calendar_effect(returns: dict[str, pd.Series], stats: dict[str, dict],
                    ref_returns: dict[str, pd.Series], ref_stats: dict[str, dict]) -> dict:
    """Pre-reg 5a-bis section 5: every variant under the two calendars.

    ``delta`` is this run minus the reference run. The baseline difference
    goes through the same paired bootstrap as the verdict: it measures what
    the calendar defect cost the published code, and decides nothing.
    """
    table = {}
    for m in stats:
        now = {k: stats[m][k] for k in REPORTED}
        ref = {k: ref_stats[m][k] for k in REPORTED}
        table[m] = {"this_run": now, "reference": ref,
                    "delta": {k: round(now[k] - ref[k], 6) for k in REPORTED}}
    b = circular_block_diff(returns[BASELINE], ref_returns[BASELINE])
    return {"stats_by_calendar": table,
            "rv21_minus_reference_rv21": {"diff": round(b["observed"], 4),
                                          "p_one_sided": round(b["p_one_sided"], 4),
                                          "ci95": [round(x, 4) for x in b["ci95"]]}}


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def load_run(charts_dir: Path, sessions: pd.DatetimeIndex) -> tuple[dict, dict]:
    """Daily net returns and section 4 stats of the 11 variants of one run."""
    returns, stats = {}, {}
    for m in [BASELINE, *CANDIDATES, *(f"placebo_{s}" for s in PLACEBO_SEEDS)]:
        d = charts_dir
        returns[m] = daily_returns(daily_close_equity(_read(d / f"{m}_coursia-18921-equity.json")),
                                   sessions)
        qc_stats = _read(d / f"{m}_stats.json") if (d / f"{m}_stats.json").exists() else None
        stats[m] = variant_stats(returns[m], _read(d / f"{m}_Exposure.json"),
                                 _read(d / f"{m}_Portfolio_Turnover.json"), qc_stats)
    return returns, stats


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("charts_dir", type=Path, help="chart JSONs written by read_backtest_chart")
    ap.add_argument("spy_csv", type=Path, help="daily SPY bars (trading sessions)")
    ap.add_argument("--forecasts", type=Path,
                    default=Path(__file__).resolve().parent / "results" / "voltarget_forecasts.csv")
    ap.add_argument("--out-dir", type=Path, default=None,
                    help="also write the aggregate JSON here")
    ap.add_argument("--out-name", default="voltarget_strategy_verdict.json",
                    help="file name of the aggregate JSON written under --out-dir")
    ap.add_argument("--preregistration", default=PREREG_5A,
                    help="pre-registration the run answers to, copied into the JSON")
    ap.add_argument("--reference-dir", type=Path, default=None,
                    help="chart JSONs of the reference run: adds the 5a-bis section 5 table")
    args = ap.parse_args()

    sessions = load_sessions(args.spy_csv)
    returns, stats = load_run(args.charts_dir, sessions)

    forecasts = pd.read_csv(args.forecasts, parse_dates=["date"])
    result = {
        "preregistration": args.preregistration,
        "verdict_block": [VERDICT_START, VERDICT_END],
        "method": {"blocks": BLOCK, "draws": DRAWS, "rng_seed": RNG_SEED,
                   "sharpe": "mean/std(ddof=1)*sqrt(252) of daily net returns, rf=0"},
        "stats": stats,
        "strategy_verdict": compare(returns),
        "contamination_subblock": contamination(returns),
        "rv21_source_check": rv21_source_check(
            _read(args.charts_dir / f"{BASELINE}_coursia-18921-rv21.json"), forecasts),
    }
    if args.reference_dir:
        ref_returns, ref_stats = load_run(args.reference_dir, sessions)
        result["calendar_effect"] = {"reference_charts": args.reference_dir.name,
                                     **calendar_effect(returns, stats, ref_returns, ref_stats)}
    text = json.dumps(result, indent=2) + "\n"
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / args.out_name).write_text(text, encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
