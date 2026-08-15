"""yfinance -> VIX / VIX3M daily CSV provisioner (reproducible data pipeline).

Purpose
-------
``projects/VIX-TermStructure/quantbook.ipynb`` re-executes locally via Docker
``lean research``. The notebook's VIX/VIX3M series come from CBOE's PUBLIC
30-/93-day implied-volatility indices, which ``qb.add_data(CBOE, ...)`` can only
serve through QC Cloud alternative-data infrastructure (empty in local Docker
research). The notebook therefore falls back to loading the **same genuine
series** from local ``date,close`` CSVs (yfinance ``^VIX`` / ``^VIX3M`` =
CBOE public indices -- same data, local pipe, consistent with how the sibling
quantbooks use local LEAN equity/crypto data instead of QC Cloud).

CBOE custom data needs QC Cloud (the $600/yr Security Master is NOT used --
``lean data download`` is excluded per ai-01 c.38); yfinance is the free,
authorized ingestion path (the user's 2026-07 yfinance rejection was about
swapping it into the notebook *source*, not about ingestion). This module is
the committed, reproducible converter that regenerates the two CSVs in one
command so the re-exec metrics are reproducible (C945-L: provisioning is
shipped, data is gitignored -- ``*.csv`` under ``projects/`` is gitignored by
``QuantConnect/.gitignore`` line 96, and no sibling quantbook ships committed
CSVs either).

CSV format
----------
    date,close
    2011-12-01,27.41
    2011-12-02,27.52
    ...

``date`` is the trading day (YYYY-MM-DD), ``close`` is the raw float settle.
This is the simple format the notebook's ``_find('vix_daily.csv')`` loader
expects (``pd.read_csv(..., parse_dates=['date'], index_col='date')['close']``)
-- NOT the LEAN daily-zip OHLCV format produced by ``yfinance_to_lean_daily.py``
(VIX is a CBOE *index*, read as a ``date,close`` research series, not a LEAN
equity daily bar).

Usage
-----
    # Regenerate the VIX/VIX3M CSVs into the LEAN data folder (the Docker mount)
    python scripts/quantconnect/provision_vix_csv.py \\
        --out-folder lean-workspace/data

    # Dry-run (prints first rows, writes nothing)
    python scripts/quantconnect/provision_vix_csv.py --dry-run

Env: any Python with ``yfinance`` (coursia-ml-training has it). yfinance is
imported lazily so the module imports offline.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Optional

# CBOE public implied-vol indices -> yfinance tickers. VIX3M is the 93-day
# series (CBOE VXV / "3-Month VIX"); yfinance exposes it as ^VIX3M.
SERIES = {
    "vix_daily.csv": "^VIX",
    "vix3m_daily.csv": "^VIX3M",
}
DEFAULT_START = "2010-01-01"  # window wider than the notebook's 2012-2025 range


def fetch_series(yf_ticker: str, start: str):
    """Lazily import yfinance and download daily Close for one CBOE index."""
    import yfinance as yf  # noqa: WPS433 (lazy: yfinance optional at import time)
    df = yf.download(yf_ticker, start=start, progress=False, auto_adjust=False)
    if df is None or df.empty:
        raise RuntimeError(f"yfinance returned no data for {yf_ticker!r}")
    # Flatten yfinance >= 0.24 MultiIndex columns to the Field level.
    if isinstance(df.columns, getattr(__import__("pandas"), "MultiIndex")):
        df.columns = df.columns.get_level_values(0)
    # Drop the trailing intraday-incomplete bar (Close NaN while session open) --
    # C962-L: without this the latest row carries NaN and corrupts the series.
    if "Close" in df.columns:
        df = df.dropna(subset=["Close"])
    return df["Close"]


def to_csv_lines(close) -> list[str]:
    """Convert a Close Series to ``date,close`` CSV lines (ISO date, float)."""
    lines = ["date,close"]
    for ts, val in close.items():
        ts = ts.tz_localize(None) if getattr(ts, "tzinfo", None) else ts
        lines.append(f"{ts:%Y-%m-%d},{float(val)}")
    return lines


def write_csv(path: Path, lines: list[str]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    # ``newline="\n"`` pins LF line endings on Windows too: ``Path.write_text``
    # otherwise translates ``\n`` -> ``\r\n``, so the ``date,close`` CSVs minted on
    # a Windows worker would differ byte-for-byte from those minted under the
    # Linux Docker ``lean research`` container that consumes them (non-reproducible
    # data files). Matches the canonical pattern in ``populate_cost_metadata.py``.
    path.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    return path


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Provision VIX/VIX3M daily CSVs (yfinance ^VIX/^VIX3M = CBOE public indices).")
    p.add_argument("--out-folder", type=Path, default=Path("lean-workspace/data"),
                   help="Output folder for vix_daily.csv / vix3m_daily.csv "
                        "(default lean-workspace/data, the Docker /Lean/Data mount).")
    p.add_argument("--start", default=DEFAULT_START, help="ISO start date (default 2010-01-01).")
    p.add_argument("--dry-run", action="store_true", help="Print first rows, write nothing.")
    args = p.parse_args(argv)

    for fname, yf_ticker in SERIES.items():
        close = fetch_series(yf_ticker, args.start)
        lines = to_csv_lines(close)
        out = args.out_folder / fname
        if args.dry_run:
            print(f"[dry-run] {yf_ticker} -> {out}: {len(lines) - 1} bars; first 3:")
            for ln in lines[1:4]:
                print("   ", ln)
            continue
        write_csv(out, lines)
        print(f"[ok] {yf_ticker}: {len(lines) - 1} bars -> {out}")
    print(f"\nDone: {len(SERIES)} CBOE series provisioned into {args.out_folder}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
