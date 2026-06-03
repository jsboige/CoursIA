"""
Explore and extract FXCM forex data from forex.zip archive.

Extracts bid/ask OHLCV data from nested zip archives, converts to standard
CSV format with mid-price OHLCV.

Data source: FXCM (via CryptoDataDownload / Kaggle)
Pairs: EURUSD, GBPUSD, NZDUSD, EURGBP (+ AUDUSD, CHFUSD, JPYUSD at hourly)
Resolutions: daily, hourly, minute

Usage:
    python scripts/datasets/dezip_forex.py --list              # list contents
    python scripts/datasets/dezip_forepy.py --extract daily     # extract daily data
    python scripts/datasets/dezip_forex.py --extract hourly     # extract hourly data
    python scripts/datasets/dezip_forex.py --extract all        # extract everything
"""

import argparse
import io
import logging
import zipfile
from pathlib import Path

import pandas as pd

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger(__name__)

DEFAULT_FOREX_ZIP = r"G:\Mon Drive\MyIA\Dev\Trading\Data\Forex\forex.zip"
DEFAULT_OUTPUT_DIR = "MyIA.AI.Notebooks/QuantConnect/datasets/forex"


def list_contents(zip_path: str) -> dict:
    """List archive contents grouped by resolution."""
    with zipfile.ZipFile(zip_path) as zf:
        names = [n for n in zf.namelist() if n.endswith(".zip")]

    result = {"daily": [], "hourly": [], "minute": []}
    for n in names:
        parts = n.split("/")
        if len(parts) < 4:
            continue
        pair_file = parts[-1]
        if "/daily/" in n:
            result["daily"].append({"path": n, "pair": pair_file.replace(".zip", "")})
        elif "/hour/" in n:
            result["hourly"].append({"path": n, "pair": pair_file.replace(".zip", "")})
        elif "/minute/" in n:
            result["minute"].append({"path": n, "pair": parts[-2], "date_file": pair_file})

    return result


def extract_inner_csv(zf: zipfile.ZipFile, inner_path: str) -> pd.DataFrame:
    """Extract CSV from a zip-within-zip archive."""
    with zf.open(inner_path) as inner_file:
        with zipfile.ZipFile(io.BytesIO(inner_file.read())) as inner_zf:
            csv_names = [n for n in inner_zf.namelist() if n.endswith(".csv")]
            if not csv_names:
                log.warning("No CSV in %s", inner_path)
                return pd.DataFrame()
            with inner_zf.open(csv_names[0]) as csv_file:
                cols = ["datetime", "bid_open", "bid_high", "bid_low", "bid_close", "bid_vol",
                        "ask_open", "ask_high", "ask_low", "ask_close", "ask_vol"]
                df = pd.read_csv(csv_file, header=None, names=cols)

    df["timestamp"] = pd.to_datetime(df["datetime"], format="%Y%m%d %H:%M")
    df = df.drop(columns=["datetime"])

    # Compute mid-price
    df["open"] = (df["bid_open"] + df["ask_open"]) / 2
    df["high"] = (df["bid_high"] + df["ask_high"]) / 2
    df["low"] = (df["bid_low"] + df["ask_low"]) / 2
    df["close"] = (df["bid_close"] + df["ask_close"]) / 2
    df["spread"] = df["ask_close"] - df["bid_close"]

    return df


def extract_resolution(zip_path: str, resolution: str, output_dir: Path) -> list[Path]:
    """Extract all data for a given resolution."""
    contents = list_contents(zip_path)
    items = contents.get(resolution, [])
    if not items:
        log.warning("No data for resolution: %s", resolution)
        return []

    output_dir.mkdir(parents=True, exist_ok=True)
    written = []

    with zipfile.ZipFile(zip_path) as zf:
        # Group by pair for minute data (merge daily files)
        pairs_data: dict[str, list[pd.DataFrame]] = {}

        for item in items:
            pair = item["pair"]
            if pair in pairs_data:
                pair = f"{pair}_{resolution}"
            log.info("Extracting %s %s: %s", pair, resolution, item["path"])

            try:
                df = extract_inner_csv(zf, item["path"])
                if df.empty:
                    continue
                df["pair"] = pair
                if pair not in pairs_data:
                    pairs_data[pair] = []
                pairs_data[pair].append(df)
            except Exception as e:
                log.error("Failed to extract %s: %s", item["path"], e)

        for pair, dfs in pairs_data.items():
            if not dfs:
                continue
            combined = pd.concat(dfs, ignore_index=True)
            combined = combined.sort_values("timestamp").reset_index(drop=True)

            # Deduplicate
            combined = combined.drop_duplicates(subset=["timestamp"], keep="last")

            out_path = output_dir / f"{pair}_{resolution}.csv"
            out_cols = ["timestamp", "open", "high", "low", "close", "spread",
                        "bid_open", "bid_high", "bid_low", "bid_close",
                        "ask_open", "ask_high", "ask_low", "ask_close", "pair"]
            combined[out_cols].to_csv(out_path, index=False)
            log.info("Saved: %s (%d rows, %s → %s)",
                     out_path, len(combined),
                     combined["timestamp"].iloc[0], combined["timestamp"].iloc[-1])
            written.append(out_path)

    return written


def main():
    parser = argparse.ArgumentParser(description="Extract FXCM forex data from zip archive")
    parser.add_argument("--zip-path", default=DEFAULT_FOREX_ZIP, help="Path to forex.zip")
    parser.add_argument("--output-dir", default=DEFAULT_OUTPUT_DIR, help="Output directory")
    parser.add_argument("--list", action="store_true", help="List archive contents")
    parser.add_argument("--extract", choices=["daily", "hourly", "minute", "all"],
                        help="Resolution to extract")
    args = parser.parse_args()

    if args.list:
        contents = list_contents(args.zip_path)
        print(f"\n{'='*60}")
        print(f"Forex Archive Contents")
        print(f"{'='*60}")
        for res, items in contents.items():
            pairs = sorted(set(i["pair"] for i in items))
            print(f"\n{res.upper()} ({len(items)} files, {len(pairs)} pairs):")
            for p in pairs:
                count = sum(1 for i in items if i["pair"] == p)
                print(f"  {p}: {count} file(s)")
        return

    if not args.extract:
        parser.print_help()
        return

    resolutions = ["daily", "hourly"] if args.extract == "all" else [args.extract]
    all_written = []

    for res in resolutions:
        log.info("=== Extracting %s data ===", res)
        written = extract_resolution(args.zip_path, res, Path(args.output_dir))
        all_written.extend(written)

    print(f"\n{'='*60}")
    print(f"Forex Extraction Summary")
    print(f"{'='*60}")
    print(f"Extracted: {len(all_written)} files")
    for p in all_written:
        print(f"  {p}")


if __name__ == "__main__":
    main()
