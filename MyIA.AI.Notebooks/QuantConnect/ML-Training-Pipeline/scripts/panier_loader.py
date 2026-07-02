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

import sys
from pathlib import Path

import numpy as np
import pandas as pd

PANIER_DIR = Path(__file__).resolve().parent.parent.parent / "datasets" / "panier"
DEFAULT_START = "2015-01-01"
DEFAULT_END = "2026-05-23"

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
    if not panier_dir.exists():
        return None
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


def ensure_symbol(
    symbol: str,
    start: str | None = None,
    end: str | None = None,
    panier_dir: Path | None = None,
) -> Path | None:
    """Ensure a symbol's CSV exists locally; download via yfinance if missing.

    Returns the path of the (existing or newly fetched) CSV, or None when the
    download fails. Output matches the convention written by
    `scripts/datasets/build_panier_anti_bias.py`:
    `<SYMBOL_underscored>_<start>_<end>.csv` with `Date,Close,High,Low,Open,Volume`.

    yfinance is imported lazily so the loader stays import-safe on machines
    without the dependency installed for pure-read use cases.
    """
    panier_dir = panier_dir or PANIER_DIR
    panier_dir.mkdir(parents=True, exist_ok=True)

    existing = _find_file(symbol, panier_dir)
    if existing is not None:
        return existing

    start = start or DEFAULT_START
    end = end or DEFAULT_END

    try:
        import yfinance as yf
    except ImportError:
        print(
            f"[panier_loader] yfinance not installed; cannot fetch {symbol}. "
            f"Install with `pip install yfinance` or pre-populate {panier_dir}.",
            file=sys.stderr,
        )
        return None

    ticker = TICKER_MAP.get(symbol, symbol)
    try:
        df = yf.download(
            ticker,
            start=start,
            end=end,
            progress=False,
            auto_adjust=True,
            actions=False,
        )
    except Exception as exc:  # noqa: BLE001 — network/HTTP errors vary by provider
        print(f"[panier_loader] yfinance download failed for {ticker}: {exc}", file=sys.stderr)
        return None

    if df is None or df.empty:
        print(f"[panier_loader] yfinance returned no data for {ticker}", file=sys.stderr)
        return None

    if isinstance(df.columns, pd.MultiIndex):
        df.columns = df.columns.get_level_values(0)

    keep = [c for c in ("Close", "High", "Low", "Open", "Volume") if c in df.columns]
    df = df[keep]
    df.index.name = "Date"

    fname = f"{symbol.replace('-', '_').replace('^', '')}_{start}_{end}.csv"
    out_path = panier_dir / fname
    df.to_csv(out_path)
    return out_path


def load_panier(
    group: str | None = None,
    start: str | None = None,
    end: str | None = None,
    panier_dir: Path | None = None,
    auto_fetch: bool = False,
) -> dict[str, pd.DataFrame]:
    """Load panier data as dict of DataFrames keyed by symbol.

    Parameters
    ----------
    group : str or None
        Filter to a specific asset class group. None = all symbols.
    start, end : str or None
        Date range filter (inclusive). Also used as the yfinance fetch window
        when `auto_fetch=True`.
    panier_dir : Path or None
        Override panier data directory.
    auto_fetch : bool
        If True, missing symbols are downloaded via yfinance into `panier_dir`
        (matching `build_panier_anti_bias.py` naming) before being loaded.
        Default False preserves the historical silent-skip behaviour so callers
        opt in explicitly to network access.

    Returns
    -------
    dict mapping symbol -> DataFrame with OHLCV columns.
    """
    symbols = get_panier_symbols(group)
    panier_dir = panier_dir or PANIER_DIR
    result = {}

    for symbol in symbols:
        path = _find_file(symbol, panier_dir)
        if path is None and auto_fetch:
            path = ensure_symbol(symbol, start=start, end=end, panier_dir=panier_dir)
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
    auto_fetch: bool = False,
) -> pd.DataFrame:
    """Load aligned close prices for panier symbols.

    Returns DataFrame indexed by Date with columns = symbols.

    auto_fetch: when True, missing per-symbol CSVs are fetched via yfinance
    (lazy import) before assembly. The pre-computed summary path always
    bypasses fetch — delete panier_close_all.csv to force per-symbol rebuild.
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
    data = load_panier(
        group=group,
        start=start,
        end=end,
        panier_dir=panier_dir,
        auto_fetch=auto_fetch,
    )
    closes = {}
    for symbol, df in data.items():
        if "Close" in df.columns:
            closes[symbol] = df["Close"]

    panel = pd.DataFrame(closes)
    panel.index.name = "Date"
    # Fail fast with an actionable message when the dataset is missing and the
    # caller opted out of network access (auto_fetch=False). Without this guard
    # a fresh clone silently gets an empty DataFrame (see #4921).
    if not closes and not auto_fetch:
        raise FileNotFoundError(
            f"No panier CSV data found in {panier_dir}. "
            f"Build it first with:\n"
            f"    python scripts/datasets/build_panier_anti_bias.py\n"
            f"(datasets/ is gitignored by design -- the build script is the "
            f"reproducibility path). Alternatively call "
            f"load_panier_closes(auto_fetch=True) to fetch via yfinance."
        )
    return panel


def load_panier_returns(
    group: str | None = None,
    start: str | None = None,
    end: str | None = None,
    panier_dir: Path | None = None,
    auto_fetch: bool = False,
) -> pd.DataFrame:
    """Load aligned daily returns for panier symbols.

    Returns DataFrame of pct_change() values, dropping the first row.

    auto_fetch: propagated to load_panier_closes().
    """
    closes = load_panier_closes(
        group=group,
        start=start,
        end=end,
        panier_dir=panier_dir,
        auto_fetch=auto_fetch,
    )
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


def _cli() -> int:
    import argparse

    parser = argparse.ArgumentParser(
        description="Panier loader utilities (verify integrity, pre-fetch missing symbols).",
    )
    parser.add_argument(
        "--ensure-all",
        action="store_true",
        help="Download any missing panier symbol via yfinance, then exit.",
    )
    parser.add_argument(
        "--validate",
        action="store_true",
        help="Print validate_panier_integrity() summary.",
    )
    parser.add_argument("--start", default=DEFAULT_START)
    parser.add_argument("--end", default=DEFAULT_END)
    parser.add_argument(
        "--panier-dir",
        default=None,
        help=f"Override panier directory (default: {PANIER_DIR}).",
    )
    args = parser.parse_args()

    panier_dir = Path(args.panier_dir) if args.panier_dir else PANIER_DIR

    if args.ensure_all:
        missing_before = [
            s for s in get_panier_symbols() if _find_file(s, panier_dir) is None
        ]
        print(
            f"[panier_loader] ensure-all: {len(missing_before)} missing in {panier_dir}"
        )
        ok, failed = 0, []
        for symbol in missing_before:
            path = ensure_symbol(
                symbol, start=args.start, end=args.end, panier_dir=panier_dir
            )
            if path is not None:
                ok += 1
                print(f"  + {symbol} -> {path.name}")
            else:
                failed.append(symbol)
                print(f"  ! {symbol} FAILED")
        print(
            f"[panier_loader] ensure-all done: {ok} fetched, {len(failed)} failed"
        )
        if failed:
            print(f"  failed: {failed}")
            return 1

    if args.validate:
        report = validate_panier_integrity(panier_dir=panier_dir)
        print(
            f"[panier_loader] validate: ok={report['ok']}/{report['total']}, "
            f"missing={report['missing']}, issues={len(report['issues'])}"
        )
        for issue in report["issues"][:10]:
            print(f"  - {issue}")
        if len(report["issues"]) > 10:
            print(f"  ... ({len(report['issues']) - 10} more)")

    return 0


if __name__ == "__main__":
    raise SystemExit(_cli())
