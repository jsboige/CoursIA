"""Shadow-tracking entry point for a momentum rotation between six ETF pockets (#28992).

``shadow_replay.py`` calls ``etf_rotation(start=D, end=pass_date, **params)`` in a
worktree at the frozen commit (contract: ``shadow/README.md``). The rule is the one
pre-registered in #28992, on UCITS lines quoted in euros:

- six pockets, one line each (``POCKETS``): euro-area small caps, value,
  quality/profitability, growth, emerging markets, Japan;
- at the last session of each month, the 9-1 momentum of each pocket: the return
  from the month-end close of t-9 to the month-end close of t-1, the last month
  skipped (``look=9``, ``skip=1``);
- the ``top`` pockets of highest momentum get ``1/top`` each; a chosen pocket whose
  momentum is not strictly positive leaves its share to the waiting line
  (``WAITING``, an overnight-rate line), up to 100 % when no momentum is positive;
  ties are broken by the order of ``POCKETS``;
- the position is taken at the close of the signal session and held over the
  following month. A line trades only when its gap to the target reaches ``band``;
  an exit to zero always trades. The fee is ``fee`` times the traded weight,
  waiting line included. The ongoing charges of the ETFs are in their prices.

Window and schedule, as for ``shadow_inverse_vol``:

- sessions in ``[start, end)``. ``end`` is the pass date: its session may still be
  trading when the pass runs, so it is left out and every returned session is
  closed;
- the portfolio holds cash before the first session on or after ``start``. Its
  close is the first rebalance, on the signal of the last month-end before it (or
  of that session itself when it ends a month);
- then the last session of each month that ends before ``end``.

A rebalance where a pocket lacks a close ``look`` month-ends back raises: the rule
never falls back to fewer pockets.

Calendar: the sessions common to the six pockets. The waiting line is quoted on
another exchange; on a common session where it has no close, its last close is
carried forward (a return of 0 that day).

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

POCKETS = ["MMS.PA", "EVAE.PA", "EQUA.PA", "EGRO.PA", "PAEEM.PA", "PTPXE.PA"]
WAITING = "XEON.DE"
TOP, LOOK, SKIP = 2, 9, 1
BAND = 0.02
FEE = 0.001
HISTORY_DAYS = 400   # calendar days of closes before ``start``: LOOK month-ends, with room


def build_panel(closes: dict[str, pd.Series]) -> pd.DataFrame:
    """Closes on the sessions common to the pockets; the waiting line carried forward onto them."""
    missing = [s for s in POCKETS + [WAITING] if s not in closes]
    if missing:
        raise ValueError(f"missing closes for {missing}")
    pockets = pd.concat({s: closes[s] for s in POCKETS}, axis=1).dropna()
    waiting = closes[WAITING].reindex(pockets.index.union(closes[WAITING].index)).ffill()
    panel = pockets.copy()
    panel[WAITING] = waiting.reindex(pockets.index)
    return panel


def complete_month_ends(index: pd.DatetimeIndex, end: str) -> pd.DatetimeIndex:
    """Last session of each month of ``index`` that ends before ``end``."""
    end_ts = pd.Timestamp(end)
    ends = ivc.month_ends(index[index < end_ts])
    return ends[ends + pd.offsets.MonthBegin(1) <= end_ts]


def schedule_dates(index: pd.DatetimeIndex, start: str, end: str) -> pd.DatetimeIndex:
    """Rebalance sessions: the first one on or after ``start``, then complete month-ends before ``end``."""
    start_ts, end_ts = pd.Timestamp(start), pd.Timestamp(end)
    window = index[(index >= start_ts) & (index < end_ts)]
    if window.empty:
        raise ValueError(f"no session in [{start}, {end})")
    ends = complete_month_ends(index, end)
    return window[:1].union(ends[ends >= window[0]])


def momentum(prices: pd.DataFrame, anchors: pd.DatetimeIndex, date: pd.Timestamp,
             look: int = LOOK, skip: int = SKIP) -> pd.Series:
    """``look``-``skip`` momentum of each column at ``date``.

    ``t`` is the last anchor (complete month-end) on or before ``date``; the
    momentum is the return from the close of anchor ``t - look`` to the close of
    anchor ``t - skip``.
    """
    known = anchors[anchors <= date]
    if len(known) < look + 1:
        raise ValueError(f"fewer than {look + 1} month-ends up to {date.date()}")
    k = len(known) - 1
    first, last = prices.loc[known[k - look]], prices.loc[known[k - skip]]
    if first.isna().any() or last.isna().any():
        raise ValueError(f"missing month-end close for the momentum at {date.date()}")
    return last / first - 1.0


def target_weights(mom: pd.Series, top: int = TOP) -> dict[str, float]:
    """``1/top`` to each of the ``top`` best pockets with a positive momentum, the rest to the waiting line."""
    order = sorted(range(len(POCKETS)), key=lambda i: (-float(mom[POCKETS[i]]), i))
    weights = dict.fromkeys(POCKETS, 0.0)
    for i in order[:top]:
        if float(mom[POCKETS[i]]) > 0.0:
            weights[POCKETS[i]] = 1.0 / top
    weights[WAITING] = 1.0 - sum(weights.values())
    return weights


def replay(closes: dict[str, pd.Series], start: str, end: str, top: int = TOP,
           look: int = LOOK, skip: int = SKIP, band: float = BAND, fee: float = FEE) -> dict:
    """Daily net returns of the rotation opened on ``start``, over ``[start, end)``."""
    if not 1 <= top <= len(POCKETS):
        raise ValueError(f"top must be in [1, {len(POCKETS)}], got {top}")
    if not 0 <= skip < look:
        raise ValueError(f"need 0 <= skip < look, got skip={skip}, look={look}")
    panel = build_panel(closes)
    panel = panel[panel.index < pd.Timestamp(end)]
    if panel[WAITING].isna().any():
        first = panel.index[panel[WAITING].isna()][-1].date()
        panel = panel[panel.index > pd.Timestamp(first)]
    rebal = schedule_dates(panel.index, start, end)
    anchors = complete_month_ends(panel.index, end)
    schedule = {d: target_weights(momentum(panel[POCKETS], anchors, d, look, skip), top) for d in rebal}

    held_ret = panel.pct_change().fillna(0.0)
    sim = ivc.simulate(held_ret[held_ret.index >= rebal[0]], schedule, band=band, fee=fee)

    rets, turnover = sim["returns"], sim["turnover"]
    # fee of each session in fraction of the starting equity: the equity before the fee times its rate
    rate = turnover * fee
    equity = (1.0 + rets).cumprod()
    fees = float((equity / (1.0 - rate) * rate).sum())
    return {"dates": [d.strftime("%Y-%m-%d") for d in rets.index],
            "net_returns": [float(v) for v in rets],
            "turnover": [float(v) for v in turnover],
            "fees": fees}


def fetch_closes(start: str, end: str, folder: Path) -> dict[str, pd.Series]:
    """Yahoo closes of the pockets and of the waiting line, from ``HISTORY_DAYS`` before ``start`` to ``end`` (excluded)."""
    from panier_loader import ensure_symbol

    first = (pd.Timestamp(start) - pd.Timedelta(days=HISTORY_DAYS)).strftime("%Y-%m-%d")
    closes = {}
    for sym in POCKETS + [WAITING]:
        path = ensure_symbol(sym, first, end, panier_dir=folder)
        if path is None:
            raise RuntimeError(f"no data for {sym}")
        closes[sym] = ivc.read_close(Path(path))
    return closes


def etf_rotation(start: str, end: str, top: int = TOP, look: int = LOOK, skip: int = SKIP,
                 band: float = BAND, fee: float = FEE) -> dict:
    """Entry point of a shadow candidate (contract of ``shadow/README.md``)."""
    # the shadow driver reads the result on stdout: anything printed on the way goes to stderr
    with tempfile.TemporaryDirectory(prefix="shadow-etfrot-") as tmp, \
            contextlib.redirect_stdout(sys.stderr):
        closes = fetch_closes(start, end, Path(tmp))
        return replay(closes, start, end, top, look, skip, band, fee)
