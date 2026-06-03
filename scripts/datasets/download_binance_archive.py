"""
Download historical klines from Binance public data archives.

Binance provides free historical data at:
    https://data.binance.vision/?prefix=data/spot/daily/klines/

Supports: spot, futures (USDM, COIN)
Timeframes: 1m, 5m, 15m, 30m, 1h, 2h, 4h, 6h, 8h, 12h, 1d, 3d, 1w, 1mo

Usage:
    python scripts/datasets/download_binance_archive.py --symbol BTCUSDT --start 2023-01-01 --end 2023-12-31
    python scripts/datasets/download_binance_archive.py --symbol ETHUSDT --market futures --interval 1h
    python scripts/datasets/download_binance_archive.py --symbol BTCUSDT --start 2020-01-01 --end 2023-12-31 --output-dir ./data

Output:
    CSV files in --output-dir (default: MyIA.AI.Notebooks/QuantConnect/datasets/binance/)
    One file per month/day: {SYMBOL}_{INTERVAL}_{DATE}.csv
"""

import argparse
import zipfile
from datetime import datetime, timedelta
from io import BytesIO, StringIO
from pathlib import Path

try:
    import requests
except ImportError:
    raise ImportError("requests is required: pip install requests")

import pandas as pd

BINANCE_BASE = "https://data.binance.vision/data"
DEFAULT_OUTPUT = Path(__file__).resolve().parent.parent.parent / "MyIA.AI.Notebooks" / "QuantConnect" / "datasets" / "binance"

KLINES_COLUMNS = [
    "open_time", "open", "high", "low", "close", "volume",
    "close_time", "quote_volume", "trades", "taker_buy_base_volume",
    "taker_buy_quote_volume", "ignore",
]


def _build_url(symbol: str, market: str, interval: str, date_str: str, freq: str) -> str:
    if market == "spot":
        prefix = f"{BINANCE_BASE}/spot/{freq}/klines/{symbol}/{interval}"
    elif market == "futures":
        prefix = f"{BINANCE_BASE}/futures/um/{freq}/klines/{symbol}/{interval}"
    else:
        raise ValueError(f"Unknown market: {market}")

    return f"{prefix}/{symbol}-{interval}-{date_str}.zip"


def _download_one(symbol: str, market: str, interval: str, date_str: str, freq: str) -> pd.DataFrame | None:
    url = _build_url(symbol, market, interval, date_str, freq)
    resp = requests.get(url, timeout=30)

    if resp.status_code == 404:
        return None
    resp.raise_for_status()

    with zipfile.ZipFile(BytesIO(resp.content)) as zf:
        csv_name = [n for n in zf.namelist() if n.endswith(".csv")]
        if not csv_name:
            return None
        with zf.open(csv_name[0]) as f:
            df = pd.read_csv(f, header=None, names=KLINES_COLUMNS)

    return df


def _date_range_monthly(start: datetime, end: datetime) -> list[str]:
    dates = []
    current = start.replace(day=1)
    while current <= end:
        dates.append(current.strftime("%Y-%m"))
        if current.month == 12:
            current = current.replace(year=current.year + 1, month=1)
        else:
            current = current.replace(month=current.month + 1)
    return dates


def _date_range_daily(start: datetime, end: datetime) -> list[str]:
    dates = []
    current = start
    while current <= end:
        dates.append(current.strftime("%Y-%m-%d"))
        current += timedelta(days=1)
    return dates


def download(symbol: str, start: str, end: str, interval: str, market: str, output_dir: Path) -> list[Path]:
    output_dir.mkdir(parents=True, exist_ok=True)
    start_dt = datetime.strptime(start, "%Y-%m-%d")
    end_dt = datetime.strptime(end, "%Y-%m-%d")

    use_monthly = interval in ("1d", "3d", "1w", "1mo")
    freq = "monthly" if use_monthly else "daily"
    date_list = _date_range_monthly(start_dt, end_dt) if use_monthly else _date_range_daily(start_dt, end_dt)

    written = []
    print(f"Binance archive: {symbol} {interval} {market}, {len(date_list)} periods ({freq})")

    for date_str in date_list:
        df = _download_one(symbol, market, interval, date_str, freq)
        if df is None:
            continue

        filename = f"{symbol}_{interval}_{date_str}.csv"
        out_path = output_dir / filename
        df.to_csv(out_path, index=False)
        print(f"  {date_str}: {len(df)} rows -> {filename}")
        written.append(out_path)

    return written


def main():
    parser = argparse.ArgumentParser(description="Download Binance historical klines")
    parser.add_argument("--symbol", required=True, help="Trading pair (e.g. BTCUSDT)")
    parser.add_argument("--start", default="2023-01-01")
    parser.add_argument("--end", default=datetime.now().strftime("%Y-%m-%d"))
    parser.add_argument("--interval", default="1d", help="Kline interval (1m,5m,15m,1h,4h,1d,1w,etc)")
    parser.add_argument("--market", default="spot", choices=["spot", "futures"])
    parser.add_argument("--output-dir", default=str(DEFAULT_OUTPUT))
    args = parser.parse_args()

    output_dir = Path(args.output_dir)
    written = download(args.symbol.upper(), args.start, args.end, args.interval, args.market, output_dir)
    print(f"\nDone: {len(written)} files written to {output_dir}")


if __name__ == "__main__":
    main()
