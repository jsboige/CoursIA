"""yfinance -> QuantConnect LEAN daily equity converter (reproducible data pipeline).

Purpose
-------
`projects/DualMomentum/quantbook.ipynb` (PR #8401) re-executes locally via
``DefaultDataProvider`` reading ``/Lean/Data/equity/usa/daily/*.zip``. The 8 ETF
(SPY/EFA/BND/EEM/IEF/SHY/GLD/VNQ) must be present in that folder as LEAN *daily*
zips, converted from a free OHLCV source. #8401 performed that conversion
ad-hoc (the script was never committed), so the re-exec is NOT reproducible from
the repository. This module is the committed, tested converter that closes that
gap: anyone can regenerate the LEAN daily folder with one command.

Why yfinance (not Stooq)
------------------------
ai-01's DISPATCH (msg-...pkn3ev, 2026-07-27) proposed Stooq as the free source.
Firsthand probe this cycle: Stooq now gates downloads behind a JavaScript
SHA-256 proof-of-work (``/__verify``). Solving the PoW client-side (hashlib,
nonce found) returns ``verify 200`` but the subsequent CSV download yields
``Access denied`` -- Stooq enforces an additional anti-bot layer beyond the PoW
(IP / browser fingerprint). Programmatic Stooq access therefore requires a full
browser (Playwright), which is too fragile for a *reproducible* pipeline. We use
**yfinance**, which #8401 already used and which the user explicitly authorized
as a **data-source-to-convert** (Path A ingestion) -- the user's rejection
(17/07, 4 PRs closed, #7066) was yfinance as a *quantbook swap* (corrupting the
notebook source), NOT as an ingestion backend.

LEAN daily format (firsthand-verified in #8401)
-----------------------------------------------
The on-disk LEAN US-equity daily format, proven end-to-end in #8401 (the
quantbook read ``735100`` back as close ``73.51`` for EFA 2007-01-03):

    <data-folder>/equity/usa/daily/<ticker>.zip
        -> contains <ticker>.csv  (ticker LOWERCASE -- LEAN's own equity data
           uses lowercase, e.g. spy.zip/spy.csv; verified firsthand against the
           21 in-repo reference zips, ai-01 c.26)
        -> one line per trading day, NO header:
           YYYYMMDD HH:MM,Open,High,Low,Close,Volume
        -> OHLC are integers scaled x10000 (73.51 -> 735100)
        -> Volume is the raw integer share volume

The time component is ``00:00`` -- the LEAN daily-format convention (every daily
bar carries midnight), NOT the equity session close. Verified firsthand against
the 21 in-repo reference zips: every line carries ``00:00`` (e.g. ``spy.zip``
first line ``19980102 00:00,973100,975300,965300,973600,2150000``). LEAN's daily
reader keys on the date, so a wrong time does not break loudly -- which is why
the convention is pinned by an anchoring test in the test suite. Prices are RAW
(unadjusted for dividends) -- benign for a price-momentum signal, documented
transparently in the quantbook (cell[6]) and here. A full adjusted-close path
needs a Security Master or a dividend-aware converter (deferred).

Usage
-----
    # Regenerate the full DualMomentum 8-ETF universe into /Lean/Data
    python scripts/quantconnect/yfinance_to_lean_daily.py \\
        --tickers SPY EFA BND EEM IEF SHY GLD VNQ \\
        --out-folder /Lean/Data/equity/usa/daily

    # Single ticker, custom range, dry-run (prints first lines, writes nothing)
    python scripts/quantconnect/yfinance_to_lean_daily.py --tickers EFA --dry-run

Env: any Python with ``yfinance`` (coursia-ml-training has 1.5.2). The converter
itself only needs pandas + the stdlib to WRITE; yfinance is imported lazily so
the module + its offline tests run without network.
"""

from __future__ import annotations

import argparse
import zipfile
from pathlib import Path
from typing import Iterable, Optional

import pandas as pd

PRICE_SCALE = 10_000  # LEAN stores equity OHLC as int = round(price * 10000)
LEAN_DAILY_TIME = "00:00"  # LEAN daily-format convention: every daily bar carries midnight
# (NOT the equity session close -- verified firsthand against the 21 in-repo
# reference zips, ai-01 c.26). Renamed from SESSION_CLOSE_TIME to stop encoding
# the falsehood that 00:00 is a session-close hour.


def df_to_lean_rows(df, time: str = LEAN_DAILY_TIME) -> list[str]:
    """Convert a yfinance OHLCV DataFrame to LEAN daily CSV lines.

    ``df`` is expected to be yfinance's daily format: a DatetimeIndex (timezone-
    naive or aware) with columns Open/High/Low/Close/Volume. Returns a list of
    ``YYYYMMDD HH:MM,O,H,L,C,V`` strings with OHLC scaled x10000 as int.
    """
    # Drop rows with NaN in any consumed OHLCV field. yfinance's latest bar is
    # often intraday-incomplete (Close/Adj Close NaN while the session is still
    # open); without this guard it raises "cannot convert float NaN to integer"
    # below and aborts the whole provisioning. Loses only the incomplete bar.
    needed = ["Open", "High", "Low", "Close", "Volume"]
    df = df.dropna(subset=[c for c in needed if c in df.columns])
    rows: list[str] = []
    for ts, rec in df.iterrows():
        # Normalise the timestamp to a date (drop tz, take date part).
        try:
            ts = ts.tz_localize(None) if ts.tzinfo is not None else ts
        except AttributeError:
            pass
        o = int(round(float(rec["Open"]) * PRICE_SCALE))
        h = int(round(float(rec["High"]) * PRICE_SCALE))
        low = int(round(float(rec["Low"]) * PRICE_SCALE))
        c = int(round(float(rec["Close"]) * PRICE_SCALE))
        v = int(round(float(rec["Volume"])))
        rows.append(f"{ts:%Y%m%d} {time},{o},{h},{low},{c},{v}")
    return rows


def write_lean_zip(ticker: str, rows: Iterable[str], out_folder: Path) -> Path:
    """Write ``<out_folder>/<ticker>.zip`` containing ``<ticker>.csv`` (LOWERCASE).

    LEAN's own equity data uses lowercase symbol names (e.g. ``spy.zip`` /
    ``spy.csv``), verified firsthand against the 21 in-repo reference zips
    (ai-01 c.26). On a case-sensitive filesystem -- i.e. the Linux Docker
    container where lean-cli runs LEAN, the very target of this converter -- an
    uppercase ``SPY.zip`` written next to an existing ``spy.zip`` is a distinct,
    silently-invisible file. The ticker is therefore lowercased unconditionally.
    Returns the path to the written zip.
    """
    out_folder = Path(out_folder)
    out_folder.mkdir(parents=True, exist_ok=True)
    ticker_low = ticker.lower()
    zip_path = out_folder / f"{ticker_low}.zip"
    body = "\n".join(rows) + ("\n" if rows else "")
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
        zf.writestr(f"{ticker_low}.csv", body)
    return zip_path


def fetch_yfinance(ticker: str, start: Optional[str] = None,
                   end: Optional[str] = None):
    """Lazily import yfinance and download daily OHLCV for one ticker.

    Kept separate so the module + offline tests import without yfinance/ network.
    """
    import yfinance as yf  # noqa: WPS433 (lazy import: yfinance is optional at test time)
    df = yf.download(ticker, start=start, end=end, auto_adjust=False,
                     progress=False)
    if df is None or df.empty:
        raise RuntimeError(f"yfinance returned no data for {ticker!r}")
    # yfinance >= 0.24 returns MultiIndex columns (Field, Ticker) even for a
    # single ticker when multiple fields are requested. Flatten to the Field
    # level so row iteration yields scalars (df_to_lean_rows indexes by name).
    if isinstance(df.columns, pd.MultiIndex):
        # Drop the Ticker level, keep the Field level (Open/High/Low/Close/Volume).
        df.columns = df.columns.get_level_values(0)
    return df


def convert_one(ticker: str, out_folder: Path, start: Optional[str] = None,
                end: Optional[str] = None, dry_run: bool = False) -> int:
    """Download, convert, and write one ticker. Returns the number of bars."""
    df = fetch_yfinance(ticker, start=start, end=end)
    rows = df_to_lean_rows(df)
    if dry_run:
        print(f"[dry-run] {ticker}: {len(rows)} bars; first 3:")
        for r in rows[:3]:
            print("   ", r)
        return len(rows)
    zip_path = write_lean_zip(ticker, rows, out_folder)
    print(f"[ok] {ticker}: {len(rows)} bars -> {zip_path}")
    return len(rows)


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Convert free ETF daily OHLCV (yfinance) to LEAN daily equity zips.")
    p.add_argument("--tickers", nargs="+", required=True,
                   help="Tickers to convert (e.g. SPY EFA BND).")
    p.add_argument("--out-folder", type=Path,
                   default=Path("/Lean/Data/equity/usa/daily"),
                   help="LEAN daily equity output folder (default /Lean/Data/equity/usa/daily).")
    p.add_argument("--start", default=None, help="ISO start date (optional).")
    p.add_argument("--end", default=None, help="ISO end date (optional).")
    p.add_argument("--dry-run", action="store_true",
                   help="Print first rows per ticker, write nothing.")
    args = p.parse_args(argv)

    total = 0
    for tk in args.tickers:
        try:
            total += convert_one(tk, args.out_folder, args.start, args.end, args.dry_run)
        except Exception as exc:  # pragma: no cover - network / ticker errors
            print(f"[FAIL] {tk}: {exc}")
    print(f"\nDone: {total} bars across {len(args.tickers)} tickers.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
