"""
Load and validate multi-asset panier data for anti-bias training.

Provides utilities to load the anti-bias panier (26 symbols, 7 asset classes)
into aligned DataFrames suitable for cross-asset ML training.

Panier data is built by `scripts/datasets/build_panier_anti_bias.py` (root level)
and stored in `QuantConnect/datasets/panier/`.

Usage:
    from panier_loader import load_panier, get_panier_symbols, PANIER_GROUPS

    # Load all symbols as dict of DataFrames
    panier = load_panier()
    spy = panier["SPY"]

    # Load aligned close prices
    closes = load_panier_closes()

    # Load specific group
    sectors = load_panier(group="us_equity_sectors")
"""

from __future__ import annotations

from pathlib import Path

import numpy as np
import pandas as pd

PANIER_DIR = Path(__file__).resolve().parent.parent.parent / "datasets" / "panier"

PANIER_GROUPS = {
    "us_equity_broad": ["SPY", "RSP", "IWM"],
    "us_equity_sectors": [
        "XLF", "XLK", "XLV", "XLY", "XLP", "XLI", "XLU", "XLB", "XLRE", "XLC",
    ],
    "volatility": ["VIX"],
    "us_bonds": ["TLT", "IEF", "SHY"],
    "commodities": ["GLD", "USO", "DBA"],
    "international": ["EFA", "EEM"],
    "crypto": ["BTC-USD", "ETH-USD", "LTC-USD", "XRP-USD"],
}

FORBIDDEN_SYMBOLS = {"AAPL", "MSFT", "GOOG", "AMZN", "NVDA", "TSLA", "META"}

TICKER_MAP = {"VIX": "^VIX"}

STAGE_3A_SYMBOLS = list(dict.fromkeys(
    PANIER_GROUPS["us_equity_sectors"]  # 10 sectors
    + PANIER_GROUPS["us_bonds"]  # 3 bonds
    + PANIER_GROUPS["commodities"]  # 3 commodities
    + PANIER_GROUPS["international"]  # 2 intl
    + ["RSP"]  # equal-weight S&P
    + ["VIX"]  # volatility
))  # Total: 19 unique assets


def get_panier_symbols(group: str | None = None) -> list[str]:
    """Get flat list of panier symbols, optionally filtered by group."""
    if group is not None:
        if group not in PANIER_GROUPS:
            raise ValueError(f"Unknown group: {group}. Valid: {list(PANIER_GROUPS.keys())}")
        return PANIER_GROUPS[group]
    symbols = []
    for grp in PANIER_GROUPS.values():
        symbols.extend(grp)
    return symbols


def _find_file(symbol: str, panier_dir: Path | None = None) -> Path | None:
    """Find the CSV file for a symbol in the panier directory."""
    panier_dir = panier_dir or PANIER_DIR
    variants = [
        f"{symbol.replace('-', '_')}_*.csv",
        f"{TICKER_MAP.get(symbol, symbol).replace('-', '_').replace('^', '')}_*.csv",
        f"{TICKER_MAP.get(symbol, symbol).replace('-', '_')}_*.csv",
    ]
    for pattern in variants:
        matches = list(panier_dir.glob(pattern))
        if matches:
            return matches[0]
    return None


def load_panier(
    group: str | None = None,
    start: str | None = None,
    end: str | None = None,
    panier_dir: Path | None = None,
) -> dict[str, pd.DataFrame]:
    """Load panier data as dict of DataFrames keyed by symbol.

    Parameters
    ----------
    group : str or None
        Filter to a specific asset class group. None = all symbols.
    start, end : str or None
        Date range filter (inclusive).
    panier_dir : Path or None
        Override panier data directory.

    Returns
    -------
    dict mapping symbol -> DataFrame with OHLCV columns.
    """
    symbols = get_panier_symbols(group)
    panier_dir = panier_dir or PANIER_DIR
    result = {}

    for symbol in symbols:
        path = _find_file(symbol, panier_dir)
        if path is None:
            continue

        df = pd.read_csv(path, index_col=0, parse_dates=True)
        if start:
            df = df[df.index >= start]
        if end:
            df = df[df.index <= end]
        result[symbol] = df

    return result


def load_panier_closes(
    group: str | None = None,
    start: str | None = None,
    end: str | None = None,
    panier_dir: Path | None = None,
) -> pd.DataFrame:
    """Load aligned close prices for panier symbols.

    Returns DataFrame indexed by Date with columns = symbols.
    """
    panier_dir = panier_dir or PANIER_DIR

    # Try pre-computed summary first
    summary_path = panier_dir / "panier_close_all.csv"
    if summary_path.exists() and group is None:
        df = pd.read_csv(summary_path, index_col=0, parse_dates=True)
        if start:
            df = df[df.index >= start]
        if end:
            df = df[df.index <= end]
        return df

    # Build from individual files
    data = load_panier(group=group, start=start, end=end, panier_dir=panier_dir)
    closes = {}
    for symbol, df in data.items():
        if "Close" in df.columns:
            closes[symbol] = df["Close"]

    panel = pd.DataFrame(closes)
    panel.index.name = "Date"
    return panel


def load_panier_returns(
    group: str | None = None,
    start: str | None = None,
    end: str | None = None,
    panier_dir: Path | None = None,
) -> pd.DataFrame:
    """Load aligned daily returns for panier symbols.

    Returns DataFrame of pct_change() values, dropping the first row.
    """
    closes = load_panier_closes(group=group, start=start, end=end, panier_dir=panier_dir)
    return closes.pct_change().dropna()


def validate_panier_integrity(panier_dir: Path | None = None) -> dict:
    """Validate panier data quality: no NaN closes, date coverage, group balance.

    Returns dict with validation results.
    """
    panier_dir = panier_dir or PANIER_DIR
    symbols = get_panier_symbols()
    results = {"total": len(symbols), "ok": 0, "missing": 0, "issues": []}

    for symbol in symbols:
        path = _find_file(symbol, panier_dir)
        if path is None:
            results["missing"] += 1
            results["issues"].append({"symbol": symbol, "issue": "file_not_found"})
            continue

        df = pd.read_csv(path, index_col=0, parse_dates=True)
        n_nans = int(df["Close"].isna().sum()) if "Close" in df.columns else -1
        n_rows = len(df)

        if n_nans > 0:
            results["issues"].append({
                "symbol": symbol, "issue": "nan_in_close", "count": n_nans,
            })
        if n_rows < 1000:
            results["issues"].append({
                "symbol": symbol, "issue": "low_coverage", "rows": n_rows,
            })
        if symbol in FORBIDDEN_SYMBOLS:
            results["issues"].append({
                "symbol": symbol, "issue": "FORBIDDEN_SYMBOL",
            })

        if n_nans == 0 and n_rows >= 1000 and symbol not in FORBIDDEN_SYMBOLS:
            results["ok"] += 1

    # Group balance check
    group_balance = {}
    for grp_name, grp_symbols in PANIER_GROUPS.items():
        group_balance[grp_name] = sum(
            1 for s in grp_symbols if _find_file(s, panier_dir) is not None
        )
    results["group_balance"] = group_balance

    return results


def compute_cross_asset_features(
    closes: pd.DataFrame,
    lookback: int = 20,
) -> pd.DataFrame:
    """Compute cross-asset features from aligned close prices.

    Features:
    - Relative momentum (each asset's return vs SPY)
    - Cross-asset correlation (rolling)
    - Sector rotation signals

    Parameters
    ----------
    closes : DataFrame
        Aligned close prices from load_panier_closes().
    lookback : int
        Rolling window for feature computation.

    Returns
    -------
    DataFrame with cross-asset features, indexed by Date.
    """
    features = pd.DataFrame(index=closes.index)

    # Returns
    returns = closes.pct_change()

    # Relative momentum vs SPY (if present)
    if "SPY" in closes.columns:
        spy_ret = returns["SPY"]
        for col in returns.columns:
            if col != "SPY":
                features[f"rel_mom_{col}"] = returns[col].rolling(lookback).sum() - spy_ret.rolling(lookback).sum()

    # Rolling correlation with SPY
    if "SPY" in closes.columns:
        for col in returns.columns:
            if col != "SPY":
                features[f"corr_spy_{col}"] = returns["SPY"].rolling(lookback).corr(returns[col])

    # Cross-asset volatility ratio
    for col in returns.columns:
        features[f"vol_{col}"] = returns[col].rolling(lookback).std()

    return features.dropna()
