"""
Download datasets from Kaggle using the Kaggle CLI.

Prerequisites:
    pip install kaggle
    # Place kaggle.json in ~/.kaggle/ (from https://www.kaggle.com/settings -> API)

Usage:
    python scripts/datasets/download_kaggle.py --dataset stefanoleone992/mutual-fund-etf-dataset
    python scripts/datasets/download_kaggle.py --dataset mcianfood/us-stock-market-historical-data --output-dir ./data
    python scripts/datasets/download_kaggle.py --list --search "crypto historical"

Output:
    Files extracted to --output-dir (default: MyIA.AI.Notebooks/QuantConnect/datasets/kaggle/)
"""

import argparse
import subprocess
import sys
from pathlib import Path

DEFAULT_OUTPUT = Path(__file__).resolve().parent.parent.parent / "MyIA.AI.Notebooks" / "QuantConnect" / "datasets" / "kaggle"


def _check_kaggle_cli():
    try:
        result = subprocess.run(["kaggle", "--version"], capture_output=True, text=True, timeout=10)
        if result.returncode != 0:
            raise FileNotFoundError
    except (FileNotFoundError, subprocess.TimeoutExpired):
        print("ERROR: kaggle CLI not found. Install with: pip install kaggle", file=sys.stderr)
        print("Place kaggle.json in ~/.kaggle/ from https://www.kaggle.com/settings -> API", file=sys.stderr)
        sys.exit(1)


def search_datasets(query: str, max_results: int = 10):
    _check_kaggle_cli()
    result = subprocess.run(
        ["kaggle", "datasets", "list", "-s", query, "--max-size", str(max_results), "--csv"],
        capture_output=True, text=True, timeout=30,
    )
    print(result.stdout)
    if result.stderr:
        print(result.stderr, file=sys.stderr)


def download(dataset: str, output_dir: Path, unzip: bool = True) -> Path:
    _check_kaggle_cli()
    target = output_dir / dataset.replace("/", "__")
    target.mkdir(parents=True, exist_ok=True)

    cmd = [
        "kaggle", "datasets", "download",
        "-d", dataset,
        "-p", str(target),
    ]
    if unzip:
        cmd.append("--unzip")

    print(f"Downloading Kaggle dataset: {dataset}")
    print(f"  Target: {target}")

    result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
    if result.returncode != 0:
        print(f"ERROR: {result.stderr}", file=sys.stderr)
        sys.exit(1)

    files = list(target.iterdir())
    print(f"  Downloaded {len(files)} file(s):")
    for f in files:
        size_mb = f.stat().st_size / (1024 * 1024)
        print(f"    {f.name} ({size_mb:.1f} MB)")

    return target


def main():
    parser = argparse.ArgumentParser(description="Download datasets from Kaggle")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--dataset", help="Kaggle dataset slug (e.g. user/dataset-name)")
    group.add_argument("--list", action="store_true", help="Search datasets (use --search for query)")
    parser.add_argument("--search", default="", help="Search query (use with --list)")
    parser.add_argument("--output-dir", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--no-unzip", action="store_true", help="Keep zip file")
    args = parser.parse_args()

    if args.list:
        search_datasets(args.search)
    else:
        output_dir = Path(args.output_dir)
        download(args.dataset, output_dir, unzip=not args.no_unzip)


if __name__ == "__main__":
    main()
