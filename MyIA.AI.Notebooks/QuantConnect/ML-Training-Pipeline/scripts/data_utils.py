"""
Shared data loading and generation utilities for ML-Training-Pipeline scripts.

Consolidates duplicated load_data, generate_synthetic_data, and compute_data_hash
from train_transformer.py, train_lstm.py, and train_dqn_rl.py.

Usage:
    from data_utils import load_data, generate_synthetic_data, compute_data_hash
"""

import hashlib
from pathlib import Path

import numpy as np
import pandas as pd


def load_data(
    data_dir: Path, symbol: str, start: str | None = None, end: str | None = None
) -> pd.DataFrame:
    """Load OHLCV data from downloaded CSV files.

    Concatenates all matching {symbol}_*.csv files, deduplicates by index,
    and optionally filters by date range.
    """
    candidates = sorted(data_dir.glob(f"{symbol}_*.csv"))
    if not candidates:
        raise FileNotFoundError(f"No CSV files found for {symbol} in {data_dir}")

    dfs = []
    for f in candidates:
        chunk = pd.read_csv(f, parse_dates=["Date"], index_col="Date")
        dfs.append(chunk)

    df = pd.concat(dfs).sort_index()
    df = df[~df.index.duplicated(keep="first")]

    if start:
        df = df[df.index >= start]
    if end:
        df = df[df.index <= end]

    return df


def generate_synthetic_data(n_rows: int = 5000) -> pd.DataFrame:
    """Generate synthetic OHLCV data for dry-run validation."""
    np.random.seed(42)
    dates = pd.date_range("2010-01-01", periods=n_rows, freq="B")
    close = 100.0 * np.exp(np.cumsum(np.random.normal(0.0003, 0.015, n_rows)))

    df = pd.DataFrame(
        {
            "Close": close,
            "Open": close * (1 + np.random.normal(0, 0.003, n_rows)),
            "High": close * (1 + np.abs(np.random.normal(0, 0.008, n_rows))),
            "Low": close * (1 - np.abs(np.random.normal(0, 0.008, n_rows))),
            "Volume": np.random.lognormal(15, 1, n_rows),
        },
        index=dates,
    )
    return df


def compute_data_hash(df: pd.DataFrame) -> str:
    """Compute SHA256 hash of the dataset for reproducibility."""
    return hashlib.sha256(
        pd.util.hash_pandas_object(df).values.tobytes()
    ).hexdigest()[:16]
