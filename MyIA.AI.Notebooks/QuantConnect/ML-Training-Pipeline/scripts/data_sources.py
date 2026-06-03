"""
Unified data source interface for ML-Training-Pipeline.

Provides a single fetch_data() entry point that tries local CSV files first,
then falls back to online APIs (yfinance, FRED). All downloads are Parquet-cached
to avoid redundant network calls.

Providers:
    - yfinance: Free, no API key. US equities, ETFs, crypto. Daily/intraday.
    - FRED: Free API key. Macro indicators (rates, CPI, VIX).
    - Stub interfaces for premium providers (Polygon, Tiingo, Alpha Vantage).

Usage:
    from data_sources import fetch_data, DataRequest

    # Simple: fetch OHLCV for SPY
    df = fetch_data("SPY", start="2020-01-01", end="2024-01-01")

    # With explicit provider
    df = fetch_data("SPY", source="yfinance", start="2020-01-01")

    # Macro data from FRED (requires FRED_API_KEY env var)
    rates = fetch_data("DGS10", source="fred", start="2020-01-01")

References:
    - yfinance: https://github.com/ranaroussi/yfinance
    - FRED API: https://fred.stlouisfed.org/docs/api/fred/
"""

from __future__ import annotations

import os
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np
import pandas as pd


DEFAULT_DATA_DIR = Path(__file__).resolve().parent.parent.parent / "datasets" / "yfinance"
DEFAULT_CACHE_DIR = Path(__file__).resolve().parent.parent.parent / "datasets" / "cache"


@dataclass
class DataRequest:
    """Parameters for a data fetch request."""

    symbol: str
    start: str | None = None
    end: str | None = None
    interval: str = "1d"
    source: str = "auto"
    data_dir: Path = field(default_factory=lambda: DEFAULT_DATA_DIR)
    cache_dir: Path = field(default_factory=lambda: DEFAULT_CACHE_DIR)
    use_cache: bool = True

    def cache_path(self) -> Path:
        key = f"{self.symbol}_{self.start}_{self.end}_{self.interval}_{self.source}"
        import hashlib
        h = hashlib.md5(key.encode()).hexdigest()[:12]
        return self.cache_dir / f"{self.symbol}_{h}.parquet"


@dataclass
class DataResult:
    """Result of a data fetch."""

    df: pd.DataFrame
    source_used: str
    from_cache: bool
    symbol: str
    n_rows: int = 0

    def __post_init__(self):
        if self.n_rows == 0:
            self.n_rows = len(self.df)


def fetch_data(
    symbol: str,
    start: str | None = None,
    end: str | None = None,
    interval: str = "1d",
    source: str = "auto",
    data_dir: Path | None = None,
    cache_dir: Path | None = None,
    use_cache: bool = True,
) -> pd.DataFrame:
    """Fetch OHLCV data with local-first strategy.

    Tries in order:
    1. Parquet cache (if use_cache=True)
    2. Local CSV files in data_dir
    3. Online provider (yfinance for equities, FRED for macro)

    Parameters
    ----------
    symbol : str
        Ticker symbol (e.g. "SPY", "BTC-USD", "DGS10").
    start : str or None
        Start date (YYYY-MM-DD).
    end : str or None
        End date (YYYY-MM-DD).
    interval : str
        Data interval ("1d", "1wk", "1mo", etc.).
    source : str
        "auto", "yfinance", "fred", "csv".
    data_dir : Path or None
        Directory with pre-downloaded CSV files.
    cache_dir : Path or None
        Directory for Parquet cache files.
    use_cache : bool
        Whether to use Parquet cache.

    Returns
    -------
    pd.DataFrame with columns: Open, High, Low, Close, Volume (OHLCV).
    For FRED data: single column named after the series.
    """
    req = DataRequest(
        symbol=symbol,
        start=start,
        end=end,
        interval=interval,
        source=source,
        data_dir=data_dir or DEFAULT_DATA_DIR,
        cache_dir=cache_dir or DEFAULT_CACHE_DIR,
        use_cache=use_cache,
    )

    result = _resolve(req)
    return result.df


def _resolve(req: DataRequest) -> DataResult:
    """Resolve data request through cache → local → online chain."""
    # 1. Parquet cache
    if req.use_cache:
        cached = _load_cache(req)
        if cached is not None:
            return DataResult(df=cached, source_used="cache", from_cache=True, symbol=req.symbol)

    # 2. Local CSV (if source is auto or csv)
    if req.source in ("auto", "csv"):
        local = _load_local_csv(req)
        if local is not None:
            if req.use_cache:
                _save_cache(req, local)
            return DataResult(df=local, source_used="csv", from_cache=False, symbol=req.symbol)
        if req.source == "csv":
            raise FileNotFoundError(
                f"No CSV files found for {req.symbol} in {req.data_dir}"
            )

    # 3. Online provider
    if req.source in ("auto", "yfinance"):
        online = _fetch_yfinance(req)
        if online is not None:
            if req.use_cache:
                _save_cache(req, online)
            return DataResult(df=online, source_used="yfinance", from_cache=False, symbol=req.symbol)

    if req.source in ("auto", "fred"):
        online = _fetch_fred(req)
        if online is not None:
            if req.use_cache:
                _save_cache(req, online)
            return DataResult(df=online, source_used="fred", from_cache=False, symbol=req.symbol)

    raise ValueError(
        f"Cannot resolve data for {req.symbol}: no local files and no provider available. "
        f"Tried: cache={req.use_cache}, csv={req.data_dir}, source={req.source}"
    )


def _load_cache(req: DataRequest) -> pd.DataFrame | None:
    path = req.cache_path()
    if not path.exists():
        return None
    df = pd.read_parquet(path)
    return _filter_date_range(df, req.start, req.end)


def _save_cache(req: DataRequest, df: pd.DataFrame) -> None:
    path = req.cache_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    df.to_parquet(path)


def _load_local_csv(req: DataRequest) -> pd.DataFrame | None:
    """Load from pre-downloaded CSV files using data_utils.load_data pattern."""
    data_dir = req.data_dir
    if not data_dir.exists():
        return None

    candidates = sorted(data_dir.glob(f"{req.symbol}_*.csv"))
    if not candidates:
        # Try underscore variant (BTC-USD -> BTC_USD)
        alt_symbol = req.symbol.replace("-", "_")
        candidates = sorted(data_dir.glob(f"{alt_symbol}_*.csv"))
    if not candidates:
        return None

    dfs = []
    for f in candidates:
        chunk = pd.read_csv(f, parse_dates=["Date"], index_col="Date")
        dfs.append(chunk)

    df = pd.concat(dfs).sort_index()
    df = df[~df.index.duplicated(keep="first")]
    return _filter_date_range(df, req.start, req.end)


def _fetch_yfinance(req: DataRequest) -> pd.DataFrame | None:
    """Fetch from yfinance (free, no API key needed)."""
    try:
        import yfinance as yf
    except ImportError:
        return None

    end_date = req.end or pd.Timestamp.now().strftime("%Y-%m-%d")
    df = yf.download(
        req.symbol,
        start=req.start,
        end=end_date,
        interval=req.interval,
        auto_adjust=True,
        progress=False,
    )

    if df.empty:
        return None

    # Flatten MultiIndex columns if present
    if isinstance(df.columns, pd.MultiIndex):
        df.columns = df.columns.get_level_values(0)

    # Normalize column names
    df.columns = [c.capitalize() for c in df.columns]

    return df


def _fetch_fred(req: DataRequest) -> pd.DataFrame | None:
    """Fetch from FRED API (free, requires FRED_API_KEY env var)."""
    api_key = os.environ.get("FRED_API_KEY")
    if not api_key:
        return None

    try:
        import requests
    except ImportError:
        return None

    url = "https://api.stlouisfed.org/fred/series/observations"
    params = {
        "series_id": req.symbol,
        "api_key": api_key,
        "file_type": "json",
        "observation_start": req.start or "",
        "observation_end": req.end or "",
        "frequency": _fred_frequency(req.interval),
    }

    resp = requests.get(url, params=params, timeout=30)
    if resp.status_code != 200:
        return None

    data = resp.json()
    observations = data.get("observations", [])
    if not observations:
        return None

    records = []
    for obs in observations:
        val = obs["value"]
        if val == ".":
            continue
        records.append({"Date": obs["date"], req.symbol: float(val)})

    if not records:
        return None

    df = pd.DataFrame(records)
    df["Date"] = pd.to_datetime(df["Date"])
    df = df.set_index("Date").sort_index()
    return df


def _fred_frequency(interval: str) -> str:
    """Map interval to FRED frequency parameter."""
    mapping = {
        "1d": "d",
        "1wk": "w",
        "1mo": "m",
        "3mo": "q",
        "1y": "a",
    }
    return mapping.get(interval, "d")


def _filter_date_range(
    df: pd.DataFrame,
    start: str | None,
    end: str | None,
) -> pd.DataFrame:
    """Filter DataFrame by date range."""
    if start:
        df = df[df.index >= start]
    if end:
        df = df[df.index <= end]
    return df


# ---------------------------------------------------------------------------
# Provider registry for extensibility
# ---------------------------------------------------------------------------

_PROVIDERS: dict[str, callable] = {
    "yfinance": _fetch_yfinance,
    "fred": _fetch_fred,
}


def register_provider(name: str, fetch_fn: callable) -> None:
    """Register a custom data provider.

    The fetch_fn must accept a DataRequest and return pd.DataFrame or None.
    """
    _PROVIDERS[name] = fetch_fn


def list_providers() -> list[str]:
    """List registered provider names."""
    return list(_PROVIDERS.keys())


def fetch_multi(
    symbols: list[str],
    start: str | None = None,
    end: str | None = None,
    interval: str = "1d",
    source: str = "auto",
    data_dir: Path | None = None,
    cache_dir: Path | None = None,
) -> dict[str, pd.DataFrame]:
    """Fetch data for multiple symbols.

    Returns dict mapping symbol → DataFrame. Failed fetches are silently skipped.
    """
    results = {}
    for symbol in symbols:
        try:
            df = fetch_data(
                symbol, start=start, end=end, interval=interval,
                source=source, data_dir=data_dir, cache_dir=cache_dir,
            )
            results[symbol] = df
        except (ValueError, FileNotFoundError):
            continue
    return results
