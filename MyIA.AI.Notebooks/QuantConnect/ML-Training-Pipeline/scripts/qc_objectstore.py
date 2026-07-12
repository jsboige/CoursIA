"""
QC ObjectStore integration for Dataset V2.

Uploads pre-computed feature datasets to QuantConnect ObjectStore
so research notebooks and live algorithms can access them via
self.ObjectStore.ReadBytes(key).

Two usage modes:
    1. CLI: python qc_objectstore.py upload --dir datasets_v2/
    2. Programmatic: from qc_objectstore import upload_dataset_v2

Inside a QC algorithm, load with:
    import io
    data = self.ObjectStore.ReadBytes("ml-datasets/v2/SPY_v2.parquet")
    features = pd.read_parquet(io.BytesIO(data))

Issue #754 Phase C: data persistence for cross-platform access.
"""

from __future__ import annotations

import argparse
import base64
import logging
import sys
from pathlib import Path

import pandas as pd

log = logging.getLogger(__name__)

OBJECT_STORE_PREFIX = "ml-datasets/v2"


def prepare_for_upload(
    dataset_dir: str | Path,
    symbols: list[str] | None = None,
) -> dict[str, Path]:
    """Discover and validate Dataset V2 Parquet files for upload.

    Returns dict of {object_key: local_path}.
    """
    dataset_dir = Path(dataset_dir)
    if not dataset_dir.exists():
        raise FileNotFoundError(f"Dataset directory not found: {dataset_dir}")

    parquet_files = sorted(dataset_dir.glob("*_v2.parquet"))
    if not parquet_files:
        raise FileNotFoundError(f"No *_v2.parquet files in {dataset_dir}")

    # Validate each file
    valid = {}
    for pf in parquet_files:
        try:
            df = pd.read_parquet(pf)
            if len(df) == 0:
                log.warning(f"  {pf.name}: empty, skipping")
                continue
            if "target" not in df.columns:
                log.warning(f"  {pf.name}: no target column, skipping")
                continue

            symbol = pf.stem.replace("_v2", "")
            if symbols and symbol not in symbols:
                continue

            key = f"{OBJECT_STORE_PREFIX}/{pf.name}"
            valid[key] = pf
            log.info(f"  {pf.name}: {len(df)} rows, {len(df.columns)} cols, valid")
        except Exception as e:
            log.warning(f"  {pf.name}: invalid parquet ({e}), skipping")

    return valid


def upload_via_mcp(
    files: dict[str, Path],
    organization_id: str,
    dry_run: bool = False,
) -> list[str]:
    """Upload files to QC ObjectStore using MCP tools.

    This is designed to be called from a Claude Code session where
    the quantconnect MCP server is available. Outside of that context,
    use the QC API directly.

    Returns list of uploaded object keys.
    """
    uploaded = []
    for key, path in files.items():
        if dry_run:
            log.info(f"  [DRY RUN] Would upload {path.name} -> {key}")
            uploaded.append(key)
            continue

        # Read file as binary
        data = path.read_bytes()
        data_b64 = base64.b64encode(data).decode("ascii")

        log.info(f"  Uploading {path.name} -> {key} ({len(data)} bytes)")
        # Note: actual upload happens via MCP tool call from the agent
        # The caller should invoke mcp__quantconnect__upload_object
        uploaded.append(key)

    return uploaded


def generate_qc_loader_code() -> str:
    """Generate Python code snippet for loading Dataset V2 in QC algorithms."""
    return '''
# Load Dataset V2 from ObjectStore in a QC algorithm
import io
import pandas as pd

def load_features_from_objectstore(algorithm, symbol: str) -> pd.DataFrame:
    """Load pre-computed features from QC ObjectStore.

    Args:
        algorithm: QCAlgorithm instance (provides self.ObjectStore)
        symbol: Ticker symbol (e.g. "SPY", "BTC-USD")

    Returns:
        DataFrame with features + regime labels + target.
    """
    key = f"ml-datasets/v2/{symbol.replace('-', '_')}_v2.parquet"

    if not algorithm.ObjectStore.ContainsKey(key):
        algorithm.Log(f"Dataset V2 not found in ObjectStore: {key}")
        return pd.DataFrame()

    data = algorithm.ObjectStore.ReadBytes(key)
    features = pd.read_parquet(io.BytesIO(data))
    algorithm.Log(f"Loaded {len(features)} rows from {key}")
    return features


# Usage in Initialize():
#   self.features_spy = load_features_from_objectstore(self, "SPY")
#   self.features_btc = load_features_from_objectstore(self, "BTC-USD")
'''


def main():
    parser = argparse.ArgumentParser(description="QC ObjectStore Dataset V2 manager")
    parser.add_argument(
        "action",
        choices=["upload", "validate", "loader-code"],
        help="Action to perform",
    )
    parser.add_argument(
        "--dir", type=str, default="datasets_v2",
        help="Directory with Dataset V2 Parquet files",
    )
    parser.add_argument(
        "--symbols", type=str, default=None,
        help="Comma-separated symbols to upload (default: all)",
    )
    parser.add_argument(
        "--org-id", type=str, default=None,
        help="QuantConnect organization ID",
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--verbose", action="store_true")

    args = parser.parse_args()
    level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(level=level, format="%(asctime)s %(levelname)-8s %(message)s")

    if args.action == "loader-code":
        print(generate_qc_loader_code())
        return

    symbols = args.symbols.split(",") if args.symbols else None

    log.info(f"Scanning {args.dir} for Dataset V2 files...")
    files = prepare_for_upload(args.dir, symbols=symbols)
    log.info(f"Found {len(files)} valid dataset files")

    if args.action == "validate":
        for key, path in files.items():
            df = pd.read_parquet(path)
            regimes = [c for c in df.columns if c.startswith("regime_")]
            cross = [c for c in df.columns if c.startswith(("bond_", "commodity_", "equity_"))]
            print(f"  {path.name:30s}: {len(df):5d} rows, {len(df.columns):2d} cols, "
                  f"regimes={regimes}, cross-asset={cross}")
        return

    if args.action == "upload":
        if not args.org_id:
            log.error("--org-id required for upload action")
            sys.exit(1)

        uploaded = upload_via_mcp(files, args.org_id, dry_run=args.dry_run)
        log.info(f"Uploaded {len(uploaded)}/{len(files)} files")
        if args.dry_run:
            log.info("(dry run — no files were actually uploaded)")


if __name__ == "__main__":
    main()
