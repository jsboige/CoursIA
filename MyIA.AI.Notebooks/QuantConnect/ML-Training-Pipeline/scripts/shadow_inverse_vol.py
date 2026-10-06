"""Shadow-tracking entry point for the inverse-volatility rule of #19072 (#18923, step 2).

``shadow_replay.py`` calls ``inverse_vol(start=D, end=pass_date, **params)`` in a
worktree at the frozen commit (contract: ``shadow/README.md``). This module turns
the #19072 experiment into a strategy that opens on ``start``. It imports
``inverse_vol_currency`` (harness rule, panel, simulation) instead of copying it:
a frozen candidate replays the code that produced the #19072 verdict.

Registry parameters:

- ``convention``: ``"U"`` (volatility of the USD closes, the rule of the paper
  harness) or ``"F"`` (volatility of the closes converted to EUR);
- ``target``: the ``target`` of ``inverse_vol_weights`` (0.025 in the verdict of
  #19072).

Window and schedule:

- sessions in ``[start, end)``. ``end`` is the pass date: its session may still be
  trading when the pass runs, so it is left out and every returned session is
  closed;
- the portfolio holds cash before the first session on or after ``start``. Its
  close is the first rebalance: the opening allocation and its fee count;
- then the last session of each month that ends before ``end``. The month of
  ``end`` is not over, so its last known session is not a month-end;
- lookback, cap per line, band and fee are those of ``inverse_vol_currency``.

Both conventions hold the same assets and earn the returns of a euro investor
(closes converted to EUR): only the volatility measure changes, as in H2 of
#19072.

Data: Yahoo daily closes through ``panier_loader.ensure_symbol``, downloaded into
a temporary folder at each pass (``auto_adjust=True``: a dividend adjusts the past
closes, and each pass replays from ``start`` on the closes of its day).
"""

from __future__ import annotations

import contextlib
import sys
import tempfile
from pathlib import Path

import pandas as pd

import inverse_vol_currency as ivc

CONVENTIONS = ("U", "F")
HISTORY_DAYS = 120   # calendar days of closes before ``start``: LOOKBACK + 1 sessions, with room


def schedule_dates(index: pd.DatetimeIndex, start: str, end: str) -> pd.DatetimeIndex:
    """Rebalance sessions: the first one on or after ``start``, then complete month-ends before ``end``."""
    start_ts, end_ts = pd.Timestamp(start), pd.Timestamp(end)
    window = index[(index >= start_ts) & (index < end_ts)]
    if window.empty:
        raise ValueError(f"no session in [{start}, {end})")
    ends = ivc.month_ends(index[index < end_ts])
    complete = ends[(ends >= window[0]) & (ends + pd.offsets.MonthBegin(1) <= end_ts)]
    return window[:1].union(complete)


def replay(us_closes: dict[str, pd.Series], fx: pd.Series, start: str, end: str,
           convention: str, target: float, harness=None) -> dict:
    """Daily net returns in EUR of the rule opened on ``start``, over ``[start, end)``."""
    if convention not in CONVENTIONS:
        raise ValueError(f"convention must be one of {CONVENTIONS}, got {convention!r}")
    harness = harness or ivc.load_harness()
    panel = ivc.build_panel(us_closes, fx)
    keep = panel["usd"].index < pd.Timestamp(end)
    usd, eur = panel["usd"][keep], panel["eur"][keep]
    rebal = schedule_dates(usd.index, start, end)
    if len(usd.loc[:rebal[0]]) < ivc.LOOKBACK + 1:
        raise ValueError(f"fewer than {ivc.LOOKBACK + 1} closes up to {rebal[0].date()}")

    prices = usd if convention == "U" else eur
    schedule = {d: ivc.target_weights(harness, prices, d, target) for d in rebal}
    eur_ret = eur.pct_change().fillna(0.0)
    sim = ivc.simulate(eur_ret[eur_ret.index >= rebal[0]], schedule)

    rets, turnover = sim["returns"], sim["turnover"]
    # fee of each session in fraction of the starting equity: the equity before the fee times its rate
    rate = turnover * ivc.FEE
    equity = (1.0 + rets).cumprod()
    fees = float((equity / (1.0 - rate) * rate).sum())
    return {"dates": [d.strftime("%Y-%m-%d") for d in rets.index],
            "net_returns": [float(v) for v in rets],
            "turnover": [float(v) for v in turnover],
            "fees": fees}


def fetch_closes(start: str, end: str, folder: Path) -> tuple[dict[str, pd.Series], pd.Series]:
    """Yahoo closes of the four signals and of EURUSD, from ``HISTORY_DAYS`` before ``start`` to ``end`` (excluded)."""
    from panier_loader import ensure_symbol

    first = (pd.Timestamp(start) - pd.Timedelta(days=HISTORY_DAYS)).strftime("%Y-%m-%d")
    closes = {}
    for sym in ivc.SIGNALS + [ivc.FX]:
        path = ensure_symbol(sym, first, end, panier_dir=folder)
        if path is None:
            raise RuntimeError(f"no data for {sym}")
        closes[sym] = ivc.read_close(Path(path))
    return {s: closes[s] for s in ivc.SIGNALS}, closes[ivc.FX]


def inverse_vol(start: str, end: str, convention: str = "U",
                target: float = ivc.VERDICT_TARGET) -> dict:
    """Entry point of a shadow candidate (contract of ``shadow/README.md``)."""
    # the shadow driver reads the result on stdout: anything printed on the way goes to stderr
    with tempfile.TemporaryDirectory(prefix="shadow-ivol-") as tmp, \
            contextlib.redirect_stdout(sys.stderr):
        us_closes, fx = fetch_closes(start, end, Path(tmp))
        return replay(us_closes, fx, start, end, convention, target)
