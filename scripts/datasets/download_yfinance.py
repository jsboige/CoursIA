"""
Download market data via yfinance with local Parquet cache.

Usage:
    python scripts/datasets/download_yfinance.py --symbols SPY,AAPL,TLT --start 2020-01-01 --end 2024-01-01
    python scripts/datasets/download_yfinance.py --symbols BTC-USD --start 2018-01-01 --interval 1d
    python scripts/datasets/download_yfinance.py --config datasets_config.yaml

Output:
    CSV files in --output-dir (default: MyIA.AI.Notebooks/QuantConnect/datasets/yfinance/)
    One file per symbol: {SYMBOL}_{start}_{end}.csv
"""

import argparse
import hashlib
import json
import sys
from datetime import datetime
from pathlib import Path

CACHE_DIR = Path(__file__).resolve().parent.parent.parent / "MyIA.AI.Notebooks" / "QuantConnect" / "datasets" / "yfinance_cache"
DEFAULT_OUTPUT = Path(__file__).resolve().parent.parent.parent / "MyIA.AI.Notebooks" / "QuantConnect" / "datasets" / "yfinance"


def _cache_key(symbol: str, start: str, end: str, interval: str) -> str:
    raw = f"{symbol}_{start}_{end}_{interval}"
    return hashlib.md5(raw.encode()).hexdigest()[:12]


def _cache_path(symbol: str, start: str, end: str, interval: str) -> Path:
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    return CACHE_DIR / f"{symbol}_{_cache_key(symbol, start, end, interval)}.parquet"


def _download(symbol: str, start: str, end: str, interval: str, use_cache: bool) -> "pd.DataFrame":
    import pandas as pd

    cache = _cache_path(symbol, start, end, interval)
    if use_cache and cache.exists():
        print(f"  Cache hit: {cache.name}")
        return pd.read_parquet(cache)

    import yfinance as yf

    print(f"  Downloading {symbol} [{start} -> {end}] interval={interval} ...")
    df = yf.download(symbol, start=start, end=end, interval=interval, auto_adjust=True, progress=False)

    if df.empty:
        print(f"  WARNING: no data returned for {symbol}", file=sys.stderr)
        return df

    if isinstance(df.columns, pd.MultiIndex):
        df.columns = df.columns.get_level_values(0)

    cache.parent.mkdir(parents=True, exist_ok=True)
    df.to_parquet(cache)
    print(f"  Cached: {cache.name}")
    return df


def download(symbols: list[str], start: str, end: str, interval: str, output_dir: Path, use_cache: bool = True) -> list[Path]:
    output_dir.mkdir(parents=True, exist_ok=True)
    written = []

    for symbol in symbols:
        df = _download(symbol, start, end, interval, use_cache)
        if df.empty:
            continue

        filename = f"{symbol.replace('-', '_')}_{start}_{end}.csv"
        out_path = output_dir / filename
        df.to_csv(out_path)
        print(f"  Written: {out_path} ({len(df)} rows)")
        written.append(out_path)

    return written


def main():
    parser = argparse.ArgumentParser(description="Download market data via yfinance")
    parser.add_argument("--symbols", required=True, help="Comma-separated ticker symbols (e.g. SPY,AAPL,TLT)")
    parser.add_argument("--start", default="2020-01-01", help="Start date (YYYY-MM-DD)")
    parser.add_argument("--end", default=datetime.now().strftime("%Y-%m-%d"), help="End date (YYYY-MM-DD)")
    parser.add_argument("--interval", default="1d", choices=["1m", "5m", "15m", "30m", "60m", "1d", "1wk", "1mo"], help="Data interval")
    parser.add_argument("--output-dir", default=str(DEFAULT_OUTPUT), help="Output directory for CSV files")
    parser.add_argument("--no-cache", action="store_true", help="Skip local Parquet cache")
    args = parser.parse_args()

    symbols = [s.strip().upper() for s in args.symbols.split(",")]
    output_dir = Path(args.output_dir)
    print(f"yfinance download: {len(symbols)} symbols, {args.start} -> {args.end}, interval={args.interval}")

    written = download(symbols, args.start, args.end, args.interval, output_dir, use_cache=not args.no_cache)
    print(f"\nDone: {len(written)}/{len(symbols)} files written to {output_dir}")


if __name__ == "__main__":
    main()
