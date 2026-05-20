"""
Manage a local crypto price archive (2010s decade).

Downloads and consolidates historical crypto prices from multiple sources
(Binance, CoinGecko) into a unified CSV archive per asset.

Usage:
    # Build full archive for BTC (2015-2024)
    python scripts/datasets/manage_crypto_archive.py --symbol BTC --start 2015-01-01 --end 2024-12-31

    # Build archive for ETH
    python --symbol ETH --start 2017-01-01

    # List available archives
    python --list

    # Update existing archive (append new data)
    python --symbol BTC --update

Output:
    CSV files in --output-dir (default: MyIA.AI.Notebooks/QuantConnect/datasets/crypto_archive/)
    Format: {SYMBOL}_USDT_archive.csv with columns [date, open, high, low, close, volume]
"""

import argparse
import sys
from datetime import datetime
from pathlib import Path

import pandas as pd

DEFAULT_OUTPUT = Path(__file__).resolve().parent.parent.parent / "MyIA.AI.Notebooks" / "QuantConnect" / "datasets" / "crypto_archive"

# Map symbol to CoinGecko ID and Binance pair
COINGECKO_MAP = {
    "BTC": "bitcoin",
    "ETH": "ethereum",
    "BNB": "binancecoin",
    "SOL": "solana",
    "XRP": "ripple",
    "ADA": "cardano",
    "DOGE": "dogecoin",
    "DOT": "polkadot",
}

BINANCE_MAP = {
    "BTC": "BTCUSDT",
    "ETH": "ETHUSDT",
    "BNB": "BNBUSDT",
    "SOL": "SOLUSDT",
    "XRP": "XRPUSDT",
    "ADA": "ADAUSDT",
    "DOGE": "DOGEUSDT",
    "DOT": "DOTUSDT",
}


def _download_coingecko(coin_id: str, start: str, end: str) -> pd.DataFrame:
    """Download daily OHLCV from CoinGecko (free, no API key, rate-limited)."""
    try:
        from pycoingecko import CoinGeckoAPI
    except ImportError:
        raise ImportError("pycoingecko required: pip install pycoingecko")

    cg = CoinGeckoAPI()
    start_ts = int(datetime.strptime(start, "%Y-%m-%d").timestamp())
    end_ts = int(datetime.strptime(end, "%Y-%m-%d").timestamp())

    data = cg.get_coin_market_chart_range_by_id(
        id=coin_id, vs_currency="usd", from_timestamp=start_ts, to_timestamp=end_ts,
    )

    prices = pd.DataFrame(data["prices"], columns=["timestamp", "close"])
    volumes = pd.DataFrame(data["total_volumes"], columns=["timestamp", "volume"])
    mcaps = pd.DataFrame(data["market_caps"], columns=["timestamp", "market_cap"])

    df = prices.merge(volumes, on="timestamp").merge(mcaps, on="timestamp")
    df["date"] = pd.to_datetime(df["timestamp"], unit="ms").dt.date
    df = df.drop(columns=["timestamp"]).drop_duplicates(subset=["date"]).sort_values("date")
    df = df[["date", "close", "volume", "market_cap"]]
    return df


def _download_binance_historical(symbol: str, start: str, end: str) -> pd.DataFrame:
    """Download via yfinance as fallback (uses Binance data under the hood for crypto)."""
    import yfinance as yf

    ticker = f"{symbol}-USD"
    df = yf.download(ticker, start=start, end=end, interval="1d", auto_adjust=True, progress=False)
    if df.empty:
        return df

    if isinstance(df.columns, pd.MultiIndex):
        df.columns = df.columns.get_level_values(0)

    df = df.reset_index()
    df.columns = [c.lower() for c in df.columns]
    df["date"] = pd.to_datetime(df["date"]).dt.date
    return df[["date", "open", "high", "low", "close", "volume"]]


def build_archive(symbol: str, start: str, end: str, output_dir: Path) -> Path:
    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"Building crypto archive: {symbol} [{start} -> {end}]")

    # Try yfinance first (simpler, covers Binance data)
    try:
        df = _download_binance_historical(symbol, start, end)
        if not df.empty:
            print(f"  Downloaded via yfinance: {len(df)} rows")
        else:
            print("  yfinance returned empty, trying CoinGecko...")
            df = pd.DataFrame()
    except Exception as e:
        print(f"  yfinance failed ({e}), trying CoinGecko...")
        df = pd.DataFrame()

    # Fallback to CoinGecko
    if df.empty:
        try:
            coin_id = COINGECKO_MAP.get(symbol.upper())
            if not coin_id:
                raise ValueError(f"No CoinGecko mapping for {symbol}")
            df_cg = _download_coingecko(coin_id, start, end)
            df = df_cg.rename(columns={"close": "close"})
            print(f"  Downloaded via CoinGecko: {len(df)} rows")
        except Exception as e:
            print(f"  CoinGecko also failed: {e}", file=sys.stderr)
            print("ERROR: Could not download data from any source.", file=sys.stderr)
            sys.exit(1)

    out_path = output_dir / f"{symbol}_USDT_archive.csv"
    df.to_csv(out_path, index=False)
    print(f"  Written: {out_path} ({len(df)} rows, {df['date'].min()} -> {df['date'].max()})")
    return out_path


def update_archive(symbol: str, output_dir: Path) -> Path | None:
    existing = output_dir / f"{symbol}_USDT_archive.csv"
    if not existing.exists():
        print(f"No existing archive for {symbol}. Use --start and --end to create one.")
        return None

    df_old = pd.read_csv(existing)
    last_date = pd.to_datetime(df_old["date"].max()).strftime("%Y-%m-%d")
    today = datetime.now().strftime("%Y-%m-%d")

    print(f"Updating {symbol} archive: appending {last_date} -> {today}")
    df_new = _download_binance_historical(symbol, last_date, today)

    if df_new.empty:
        print("  No new data available.")
        return None

    df_combined = pd.concat([df_old, df_new], ignore_index=True)
    df_combined = df_combined.drop_duplicates(subset=["date"]).sort_values("date")

    df_combined.to_csv(existing, index=False)
    print(f"  Updated: {existing} ({len(df_combined)} rows, +{len(df_new)} new)")
    return existing


def list_archives(output_dir: Path):
    if not output_dir.exists():
        print("No archives directory yet.")
        return

    archives = sorted(output_dir.glob("*_archive.csv"))
    if not archives:
        print("No archives found.")
        return

    print(f"{'Symbol':<8} {'Start':<12} {'End':<12} {'Rows':<8} {'Size':<10}")
    print("-" * 50)
    for f in archives:
        df = pd.read_csv(f)
        symbol = f.stem.replace("_USDT_archive", "")
        size_kb = f.stat().st_size / 1024
        print(f"{symbol:<8} {df['date'].min()} {df['date'].max()} {len(df):<8} {size_kb:.0f} KB")


def main():
    parser = argparse.ArgumentParser(description="Manage local crypto price archive")
    parser.add_argument("--symbol", help="Crypto symbol (BTC, ETH, SOL, etc.)")
    parser.add_argument("--start", default="2015-01-01", help="Archive start date")
    parser.add_argument("--end", default=datetime.now().strftime("%Y-%m-%d"), help="Archive end date")
    parser.add_argument("--output-dir", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--update", action="store_true", help="Update existing archive with new data")
    parser.add_argument("--list", action="store_true", help="List available archives")
    args = parser.parse_args()

    output_dir = Path(args.output_dir)

    if args.list:
        list_archives(output_dir)
    elif args.symbol:
        if args.update:
            update_archive(args.symbol.upper(), output_dir)
        else:
            build_archive(args.symbol.upper(), args.start, args.end, output_dir)
    else:
        parser.error("Provide --symbol or --list")


if __name__ == "__main__":
    main()
