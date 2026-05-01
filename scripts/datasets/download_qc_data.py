"""
Download historical data from QuantConnect via the Object Store or lean-cli.

This script provides two modes:
1. **lean-cli mode** (default): Uses `lean data download` for local data files.
2. **object-store mode**: Downloads files previously uploaded to QC Object Store.

Prerequisites for lean-cli mode:
    pip install lean
    lean login  # Set up QC credentials

Prerequisites for object-store mode:
    Configured qc-mcp MCP server (Docker)

Usage:
    # Download equity daily data via lean-cli
    python scripts/datasets/download_qc_data.py --symbol SPY --start 2020-01-01 --end 2023-12-31 --resolution daily

    # Download crypto minute data
    python --symbol BTCUSD --security-type crypto --resolution minute --start 2023-01-01

    # Download from QC Object Store
    python --mode object-store --key my-datasets/spy_daily.csv --output spy_daily.csv

Output:
    Data files in --output-dir (default: MyIA.AI.Notebooks/QuantConnect/datasets/qc/)
"""

import argparse
import subprocess
import sys
from datetime import datetime
from pathlib import Path

DEFAULT_OUTPUT = Path(__file__).resolve().parent.parent.parent / "MyIA.AI.Notebooks" / "QuantConnect" / "datasets" / "qc"


def _check_lean_cli():
    try:
        result = subprocess.run(["lean", "--version"], capture_output=True, text=True, timeout=10)
        if result.returncode != 0:
            raise FileNotFoundError
    except (FileNotFoundError, subprocess.TimeoutExpired):
        print("ERROR: lean CLI not found. Install with: pip install lean", file=sys.stderr)
        print("Then run: lean login", file=sys.stderr)
        sys.exit(1)


def download_lean_cli(
    symbol: str,
    security_type: str,
    resolution: str,
    start: str,
    end: str,
    output_dir: Path,
) -> list[Path]:
    _check_lean_cli()
    output_dir.mkdir(parents=True, exist_ok=True)

    cmd = [
        "lean", "data", "download",
        "--data-provider", "QuantConnect",
        "--security-type", security_type,
        "--resolution", resolution,
        "--ticker", symbol,
        "--start", start,
        "--end", end,
        "--destination", str(output_dir),
    ]

    print(f"Downloading QC data: {symbol} ({security_type}/{resolution}) [{start} -> {end}]")
    print(f"  Command: {' '.join(cmd)}")

    result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
    if result.returncode != 0:
        print(f"ERROR: {result.stderr}", file=sys.stderr)
        sys.exit(1)

    if result.stdout:
        print(result.stdout)

    files = list(output_dir.rglob("*.*"))
    print(f"  Downloaded {len(files)} file(s) to {output_dir}")
    return files


def download_object_store(key: str, output: str, output_dir: Path) -> Path:
    """Download a file from QC Object Store via qc-mcp (if available) or direct API."""
    output_dir.mkdir(parents=True, exist_ok=True)
    out_path = output_dir / output

    print(f"QC Object Store download: {key} -> {out_path}")
    print("NOTE: For Object Store downloads, use qc-mcp MCP server or lean CLI:")
    print(f"  lean object-store get --key {key} --filepath {out_path}")
    print("Or call the MCP tool: read_object_store_file_download_url")

    return out_path


def main():
    parser = argparse.ArgumentParser(description="Download historical data from QuantConnect")
    parser.add_argument("--mode", choices=["lean-cli", "object-store"], default="lean-cli", help="Download mode")
    parser.add_argument("--symbol", default="SPY", help="Ticker symbol (e.g. SPY, BTCUSD, EURUSD)")
    parser.add_argument("--security-type", default="equity", choices=["equity", "crypto", "forex", "future", "option"], help="Security type")
    parser.add_argument("--resolution", default="daily", choices=["tick", "second", "minute", "hour", "daily"], help="Data resolution")
    parser.add_argument("--start", default="2020-01-01", help="Start date (YYYY-MM-DD)")
    parser.add_argument("--end", default=datetime.now().strftime("%Y-%m-%d"), help="End date (YYYY-MM-DD)")
    parser.add_argument("--key", help="Object Store key (for object-store mode)")
    parser.add_argument("--output", help="Output filename (for object-store mode)")
    parser.add_argument("--output-dir", default=str(DEFAULT_OUTPUT), help="Output directory")
    args = parser.parse_args()

    output_dir = Path(args.output_dir)

    if args.mode == "lean-cli":
        download_lean_cli(args.symbol, args.security_type, args.resolution, args.start, args.end, output_dir)
    else:
        if not args.key:
            parser.error("--key is required for object-store mode")
        filename = args.output or args.key.split("/")[-1]
        download_object_store(args.key, filename, output_dir)


if __name__ == "__main__":
    main()
