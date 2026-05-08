"""Intraday OHLCV loader for HAR + Realized Variance baselines.

Unifies access to local hourly crypto datasets (Bitstamp BTC, Binance ETH/BTC)
and remote yfinance hourly downloads (SOL or any ticker) under a single API.

Used by `train_har_baseline.py` and the `realized_variance` module to compute
daily Realized Variance from intraday log returns. Pure pandas, no GPU.

Local data sources (read-only, paths from `dataset_paths.md` memory):
- BTC: `G:/Mon Drive/MyIA/Dev/Trading/Data/Bitstamp_BTCUSD_1h_2014-20240808.csv`
       Header: `unix,date,symbol,open,high,low,close,Volume BTC,Volume USD`
       Coverage: 2014-2024 (~10y)
- ETH: `G:/Mon Drive/MyIA/Dev/Trading/Data/Binance/Hour/ethbusd_trade.zip`
       Header (no col names): `YYYYMMDD HH:MM,open,high,low,close,volume`
       Coverage: 2019-10 to 2023-12 (~4y)

Remote (last 730 days only, requires `yfinance`):
- Any ticker via `load_yf_intraday(ticker, interval="1h")`
"""

from __future__ import annotations

import os
import zipfile
from dataclasses import dataclass
from pathlib import Path

import numpy as np
import pandas as pd

DEFAULT_DATA_ROOT = Path(os.environ.get(
    "TRADING_DATA_ROOT",
    "G:/Mon Drive/MyIA/Dev/Trading/Data",
))


@dataclass(frozen=True)
class IntradayDataset:
    symbol: str
    df: pd.DataFrame  # index = tz-naive DatetimeIndex (hourly), columns >= ["close"]
    source: str  # "bitstamp" | "binance" | "yfinance" | "synthetic"

    def __post_init__(self) -> None:
        if not isinstance(self.df.index, pd.DatetimeIndex):
            raise TypeError(f"{self.symbol}: index must be DatetimeIndex, got {type(self.df.index)}")
        if "close" not in self.df.columns:
            raise ValueError(f"{self.symbol}: missing 'close' column, got {list(self.df.columns)}")
        if self.df.index.has_duplicates:
            raise ValueError(f"{self.symbol}: duplicate timestamps in index")
        if not self.df.index.is_monotonic_increasing:
            raise ValueError(f"{self.symbol}: index not monotonic increasing")


def load_bitstamp_btc(path: Path | str | None = None) -> IntradayDataset:
    """Load the Bitstamp BTC/USD hourly CSV (CryptoDataDownload format)."""
    p = Path(path) if path else DEFAULT_DATA_ROOT / "Bitstamp_BTCUSD_1h_2014-20240808.csv"
    if not p.exists():
        raise FileNotFoundError(f"Bitstamp BTC CSV not found at {p}")
    df = pd.read_csv(p, skiprows=1)
    df["date"] = pd.to_datetime(df["date"], errors="coerce")
    df = df.dropna(subset=["date"]).rename(columns={"close": "close", "Volume BTC": "volume_btc"})
    df = df[["date", "open", "high", "low", "close", "volume_btc"]].set_index("date")
    df = df.sort_index()
    df = df[~df.index.duplicated(keep="last")]
    return IntradayDataset("BTC-USD", df, source="bitstamp")


def load_binance_eth(path: Path | str | None = None, tmp_dir: Path | str | None = None) -> IntradayDataset:
    """Load the Binance ETH/BUSD hourly zip (no header, YYYYMMDD HH:MM,open,high,low,close,vol)."""
    p = Path(path) if path else DEFAULT_DATA_ROOT / "Binance" / "Hour" / "ethbusd_trade.zip"
    if not p.exists():
        raise FileNotFoundError(f"Binance ETH zip not found at {p}")
    extract_root = Path(tmp_dir) if tmp_dir else Path(os.environ.get("TEMP", "/tmp")) / "har_intraday_cache"
    extract_root.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(p) as zf:
        names = zf.namelist()
        csv_name = next((n for n in names if n.endswith(".csv")), None)
        if csv_name is None:
            raise ValueError(f"No CSV inside {p}, found {names}")
        zf.extract(csv_name, extract_root)
    csv_path = extract_root / csv_name
    df = pd.read_csv(csv_path, header=None, names=["ts", "open", "high", "low", "close", "volume"])
    df["ts"] = pd.to_datetime(df["ts"], format="%Y%m%d %H:%M", errors="coerce")
    df = df.dropna(subset=["ts"]).set_index("ts")
    df = df.sort_index()
    df = df[~df.index.duplicated(keep="last")]
    return IntradayDataset("ETH-USD", df, source="binance")


def load_yf_intraday(
    ticker: str,
    interval: str = "1h",
    period: str = "730d",
) -> IntradayDataset:
    """Fetch intraday OHLCV via yfinance. Hourly only goes back ~730 days."""
    try:
        import yfinance as yf
    except ImportError as exc:
        raise ImportError("yfinance not installed; pip install yfinance") from exc
    df = yf.download(ticker, interval=interval, period=period, auto_adjust=False, progress=False, threads=False)
    if df is None or df.empty:
        raise RuntimeError(f"yfinance returned empty data for {ticker} (interval={interval}, period={period})")
    if isinstance(df.columns, pd.MultiIndex):
        df.columns = [c[0].lower() for c in df.columns]
    else:
        df.columns = [str(c).lower() for c in df.columns]
    df.index = pd.to_datetime(df.index)
    if df.index.tz is not None:
        df.index = df.index.tz_convert(None)
    df = df[~df.index.duplicated(keep="last")].sort_index()
    return IntradayDataset(ticker, df, source="yfinance")


def load_default_universe(
    bitstamp_path: Path | str | None = None,
    binance_path: Path | str | None = None,
    sol_ticker: str = "SOL-USD",
    skip_remote: bool = False,
) -> dict[str, IntradayDataset]:
    """Load BTC + ETH from local + SOL from yfinance (skipped if `skip_remote`)."""
    out: dict[str, IntradayDataset] = {}
    out["BTC-USD"] = load_bitstamp_btc(bitstamp_path)
    out["ETH-USD"] = load_binance_eth(binance_path)
    if not skip_remote:
        try:
            out[sol_ticker] = load_yf_intraday(sol_ticker)
        except Exception as exc:
            print(f"[WARN] SOL fetch failed ({exc}); continuing with BTC + ETH only")
    return out


def hourly_log_returns(ds: IntradayDataset) -> pd.Series:
    """Compute close-to-close log returns at the native hourly granularity."""
    close = ds.df["close"].astype(float)
    rets = np.log(close).diff().dropna()
    rets.name = f"{ds.symbol}_logret_1h"
    return rets


def synthesize_intraday(
    n_days: int = 30,
    obs_per_day: int = 24,
    seed: int = 0,
    annualized_vol: float = 0.6,
) -> IntradayDataset:
    """Generate a synthetic GBM-like hourly series for unit tests."""
    rng = np.random.default_rng(seed)
    n = n_days * obs_per_day
    idx = pd.date_range("2020-01-01", periods=n, freq="h")
    sigma_step = annualized_vol / np.sqrt(365.0 * obs_per_day)
    rets = rng.normal(0.0, sigma_step, size=n)
    close = 100.0 * np.exp(np.cumsum(rets))
    df = pd.DataFrame({"close": close}, index=idx)
    return IntradayDataset("SYN", df, source="synthetic")
