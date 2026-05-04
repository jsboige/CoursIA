"""
Stitch crypto datasets into continuous BTC/USD series (2012-2026).

Data sources (in priority order):
1. Bitstamp BTC/USD 1h (2014-08 to 2024-08) — personal dataset, USD
2. Binance BTC/USDT 1h (2011-09 to 2023-11) — for pre-2014 extension
3. yfinance BTC-USD (2024-08 to present) — for recent gap fill

Default start date is 2012-01-01 (2011 data excluded: only 307/8760 hours,
massive gaps, BTC at $2-15 with negligible volume — unreliable for training).

Output: continuous hourly CSV + quality report.

Usage:
    python scripts/datasets/stitch_crypto.py
    python scripts/datasets/stitch_crypto.py --start-date 2014-01-01
    python scripts/datasets/stitch_crypto.py --skip-download  # offline mode
"""

import argparse
import logging
import os
import sys
import zipfile
from datetime import datetime
from pathlib import Path

import pandas as pd

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger(__name__)

# Default paths
DEFAULT_DATA_ROOT = r"G:\Mon Drive\MyIA\Dev\Trading\Data"
DEFAULT_OUTPUT_DIR = "MyIA.AI.Notebooks/QuantConnect/datasets/crypto"
DEFAULT_START_DATE = "2012-01-01"  # 2011 excluded: 307/8760h, massive gaps, unreliable

# Anti-bias policy: these symbols are FORBIDDEN in new trainings
FORBIDDEN_SYMBOLS = {"AAPL", "MSFT", "GOOG", "AMZN", "NVDA", "TSLA", "META"}


def load_bitstamp_1h(path: str) -> pd.DataFrame:
    """Load Bitstamp BTC/USD hourly CSV (CryptoDataDownload format).

    File is reverse-chronological, columns: unix,date,symbol,open,high,low,close,Volume BTC,Volume USD
    """
    log.info("Loading Bitstamp 1h: %s", path)
    df = pd.read_csv(path, skiprows=1, parse_dates=["date"])
    df = df.sort_values("date").reset_index(drop=True)
    df = df.rename(columns={
        "date": "timestamp",
        "Volume BTC": "volume_btc",
        "Volume USD": "volume_usd",
    })
    df["source"] = "bitstamp"
    df["close"] = pd.to_numeric(df["close"], errors="coerce")
    df["open"] = pd.to_numeric(df["open"], errors="coerce")
    df["high"] = pd.to_numeric(df["high"], errors="coerce")
    df["low"] = pd.to_numeric(df["low"], errors="coerce")
    log.info("  Bitstamp: %d rows, %s → %s", len(df), df["timestamp"].iloc[0], df["timestamp"].iloc[-1])
    return df[["timestamp", "open", "high", "low", "close", "volume_btc", "volume_usd", "source"]]


def load_binance_hourly_from_zip(zip_path: str) -> pd.DataFrame:
    """Load Binance BTC/USDT hourly data from zip.

    Format: datetime(YYYYMMDD HH:MM),open,high,low,close,volume (no header)
    """
    log.info("Loading Binance hourly zip: %s", zip_path)
    with zipfile.ZipFile(zip_path) as zf:
        names = zf.namelist()
        csv_name = [n for n in names if n.endswith(".csv")][0]
        with zf.open(csv_name) as f:
            df = pd.read_csv(f, header=None, names=["datetime", "open", "high", "low", "close", "volume"])

    df["timestamp"] = pd.to_datetime(df["datetime"], format="%Y%m%d %H:%M")
    df = df.drop(columns=["datetime"]).sort_values("timestamp").reset_index(drop=True)
    df["source"] = "binance"
    df = df.rename(columns={"volume": "volume_usdt"})
    df["volume_usd"] = df["close"] * df["volume_usdt"]
    df["volume_btc"] = df["volume_usdt"]
    for col in ["open", "high", "low", "close"]:
        df[col] = pd.to_numeric(df[col], errors="coerce")
    log.info("  Binance: %d rows, %s → %s", len(df), df["timestamp"].iloc[0], df["timestamp"].iloc[-1])
    return df[["timestamp", "open", "high", "low", "close", "volume_btc", "volume_usd", "source"]]


def load_yfinance_btc(start: str, end: str) -> pd.DataFrame:
    """Download BTC-USD from yfinance for the gap period."""
    try:
        import yfinance as yf
    except ImportError:
        log.warning("yfinance not installed, skipping recent data download")
        return pd.DataFrame()

    log.info("Downloading BTC-USD from yfinance: %s → %s", start, end)
    ticker = yf.download("BTC-USD", start=start, end=end, interval="1h", progress=False)
    if ticker.empty:
        log.warning("yfinance returned empty data")
        return pd.DataFrame()

    if isinstance(ticker.columns, pd.MultiIndex):
        ticker.columns = [c[0] if isinstance(c, tuple) else c for c in ticker.columns]

    df = ticker.reset_index()
    df = df.rename(columns={
        "Date": "timestamp",
        "Datetime": "timestamp",
        "Open": "open",
        "High": "high",
        "Low": "low",
        "Close": "close",
        "Volume": "volume_usd",
    })
    df["source"] = "yfinance"
    df["volume_btc"] = df["volume_usd"] / df["close"]
    log.info("  yfinance: %d rows", len(df))
    return df[["timestamp", "open", "high", "low", "close", "volume_btc", "volume_usd", "source"]]


def validate_overlap(df_a: pd.DataFrame, df_b: pd.DataFrame, max_close_diff_pct: float = 0.5) -> dict:
    """Validate overlap between two datasets on close prices.

    Returns dict with overlap stats.
    """
    a_min, a_max = df_a["timestamp"].min(), df_a["timestamp"].max()
    b_min, b_max = df_b["timestamp"].min(), df_b["timestamp"].max()
    overlap_start = max(a_min, b_min)
    overlap_end = min(a_max, b_max)

    if overlap_start >= overlap_end:
        return {"has_overlap": False, "message": "No temporal overlap"}

    a_overlap = df_a[(df_a["timestamp"] >= overlap_start) & (df_a["timestamp"] <= overlap_end)].set_index("timestamp")
    b_overlap = df_b[(df_b["timestamp"] >= overlap_start) & (df_b["timestamp"] <= overlap_end)].set_index("timestamp")

    common_idx = a_overlap.index.intersection(b_overlap.index)
    if len(common_idx) == 0:
        return {"has_overlap": False, "message": "No common timestamps in overlap period"}

    a_close = a_overlap.loc[common_idx, "close"]
    b_close = b_overlap.loc[common_idx, "close"]
    diff_pct = ((a_close - b_close) / b_close * 100).abs()

    return {
        "has_overlap": True,
        "overlap_start": str(overlap_start),
        "overlap_end": str(overlap_end),
        "common_points": len(common_idx),
        "mean_diff_pct": float(diff_pct.mean()),
        "max_diff_pct": float(diff_pct.max()),
        "within_threshold": bool((diff_pct <= max_close_diff_pct).all()),
    }


def stitch_datasets(sources: list[pd.DataFrame]) -> pd.DataFrame:
    """Stitch multiple datasets with priority ordering.

    Priority: first dataset in list > later ones for overlapping timestamps.
    Deduplicates on timestamp, keeping the first occurrence.
    """
    combined = pd.concat(sources, ignore_index=True)
    combined = combined.drop_duplicates(subset=["timestamp"], keep="first")
    combined = combined.sort_values("timestamp").reset_index(drop=True)
    return combined


def quality_report(df: pd.DataFrame) -> dict:
    """Generate quality report for stitched dataset."""
    report = {}
    report["total_rows"] = len(df)
    report["date_range"] = f"{df['timestamp'].iloc[0]} → {df['timestamp'].iloc[-1]}"

    hourly_diff = df["timestamp"].diff()
    expected_gap = pd.Timedelta(hours=1)

    gaps = hourly_diff[(hourly_diff > expected_gap * 1.5) & (hourly_diff.notna())]
    report["num_gaps"] = len(gaps)
    if len(gaps) > 0:
        report["max_gap"] = str(gaps.max())
        report["gap_details"] = [
            {"after": str(df.loc[gaps.index[i] - 1, "timestamp"]),
             "before": str(df.loc[gaps.index[i], "timestamp"]),
             "duration_hours": int(gaps.iloc[i].total_seconds() / 3600)}
            for i in range(min(20, len(gaps)))
        ]

    # Source breakdown
    report["sources"] = df["source"].value_counts().to_dict()

    # Price sanity checks
    report["min_close"] = float(df["close"].min())
    report["max_close"] = float(df["close"].max())
    report["nan_close"] = int(df["close"].isna().sum())

    # Yearly coverage
    df["_year"] = df["timestamp"].dt.year
    yearly = df.groupby("_year").size()
    report["yearly_hours"] = yearly.to_dict()
    df.drop(columns=["_year"], inplace=True)

    return report


def main():
    parser = argparse.ArgumentParser(description="Stitch crypto datasets into continuous BTC/USD series")
    parser.add_argument("--data-root", default=DEFAULT_DATA_ROOT, help="Root of personal trading data")
    parser.add_argument("--output-dir", default=DEFAULT_OUTPUT_DIR, help="Output directory")
    parser.add_argument("--skip-download", action="store_true", help="Skip yfinance download")
    parser.add_argument("--start-date", default=DEFAULT_START_DATE, help="Earliest date to include (default: 2012-01-01, 2011 unreliable)")
    parser.add_argument("--overlap-threshold", type=float, default=0.5, help="Max close price diff %% for overlap validation")
    args = parser.parse_args()

    data_root = Path(args.data_root)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    sources = []

    # 1. Bitstamp BTC/USD 1h (primary, 2014-2024)
    bitstamp_path = data_root / "Bitstamp_BTCUSD_1h_2014-20240808.csv"
    if bitstamp_path.exists():
        df_bitstamp = load_bitstamp_1h(str(bitstamp_path))
        sources.append(df_bitstamp)
    else:
        log.warning("Bitstamp file not found: %s", bitstamp_path)

    # 2. Binance BTC/USDT 1h (extension to 2011-2023)
    binance_zip = data_root / "Binance" / "Hour" / "btcusdt_trade.all.zip"
    if binance_zip.exists():
        df_binance = load_binance_hourly_from_zip(str(binance_zip))
        # Only use Binance data before Bitstamp starts (to avoid USDT/USD conversion issues)
        if sources:
            bitstamp_start = sources[0]["timestamp"].min()
            # Use Binance for pre-2017 only (Bitstamp has better coverage from 2017+)
            # Actually keep overlap for validation, dedup will handle priority
            sources.append(df_binance)
        else:
            sources.append(df_binance)
    else:
        log.warning("Binance hourly zip not found: %s", binance_zip)

    # 3. yfinance BTC-USD (gap fill 2024-08 to present)
    if not args.skip_download and sources:
        latest_ts = max(s["timestamp"].max() for s in sources)
        now = pd.Timestamp.now(tz="UTC").tz_localize(None)
        if (now - latest_ts).days > 1:
            gap_start = (latest_ts + pd.Timedelta(hours=1)).strftime("%Y-%m-%d")
            gap_end = now.strftime("%Y-%m-%d")
            df_yf = load_yfinance_btc(gap_start, gap_end)
            if not df_yf.empty:
                sources.append(df_yf)

    if not sources:
        log.error("No data sources available. Check --data-root path.")
        sys.exit(1)

    # Overlap validation
    if len(sources) >= 2:
        for i in range(len(sources) - 1):
            overlap = validate_overlap(sources[i], sources[i + 1], args.overlap_threshold)
            log.info("Overlap validation (source %d vs %d): %s", i, i + 1, overlap)

    # Stitch (priority: first source wins on overlap)
    stitched = stitch_datasets(sources)

    # Filter early unreliable data (2011 has only 307/8760 hours, massive gaps)
    start_dt = pd.Timestamp(args.start_date)
    before_filter = len(stitched)
    stitched = stitched[stitched["timestamp"] >= start_dt].reset_index(drop=True)
    if before_filter != len(stitched):
        log.info("Filtered %d rows before %s (unreliable early data)", before_filter - len(stitched), args.start_date)

    # Quality report
    report = quality_report(stitched)
    log.info("=== Quality Report ===")
    for k, v in report.items():
        if k != "gap_details":
            log.info("  %s: %s", k, v)

    # Save
    out_path = output_dir / "BTC_USD_1h_stitched.csv"
    stitched.to_csv(out_path, index=False)
    log.info("Saved stitched dataset: %s (%d rows)", out_path, len(stitched))

    # Save report
    import json
    report_path = output_dir / "BTC_USD_1h_stitched_report.json"
    with open(report_path, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2, default=str)
    log.info("Saved quality report: %s", report_path)

    # Summary
    print(f"\n{'='*60}")
    print(f"BTC/USD Stitched Dataset Summary")
    print(f"{'='*60}")
    print(f"Output:     {out_path}")
    print(f"Rows:       {report['total_rows']:,}")
    print(f"Range:      {report['date_range']}")
    print(f"Gaps:       {report['num_gaps']}")
    print(f"Sources:    {report['sources']}")
    print(f"NaN close:  {report['nan_close']}")
    print(f"Price range: ${report['min_close']:,.2f} → ${report['max_close']:,.2f}")
    if report.get("gap_details"):
        print(f"\nTop gaps:")
        for g in report["gap_details"][:5]:
            print(f"  {g['after']} → {g['before']} ({g['duration_hours']}h)")


if __name__ == "__main__":
    main()
