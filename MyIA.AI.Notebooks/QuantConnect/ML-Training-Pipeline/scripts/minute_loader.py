"""Minute OHLCV/close loader for M12-HF (HAR-RV-J at 1-min sampling).

M12-HF (#4132) upgrades the M12 HAR-RV-J estimators from HOURLY intraday
(24 obs/day) to MINUTE intraday (~1440 obs/day) to tighten the realized
variance / bipower-variation / jump-component estimates. The estimators
(`daily_realized_variance`, `daily_bipower_variation`, `daily_jump_component`)
are resolution-agnostic — they take any intraday log-return Series — so the
only new piece is a loader that produces MINUTE close prices from owned data.

Local data source (0 QCC, owned, verified G.1 firsthand 2026-06-25):
    BTC: `G:/Mon Drive/MyIA/Dev/Trading/Data/bitstampUSD.csv.gz`
         Bitcoincharts tick format: `unix_seconds, price, amount`
         ~70.3M trades, coverage 2011-09 -> 2024-02 (covers the decisive
         2022 bear + 2023 recovery segment).

Resolution choice (microstructure noise, Hansen-Lunde 2006):
    1-min is near-optimal for liquid crypto (BTC). Sparse 5-min available as a
    defensive option for less-liquid coins. Default = 1-min.

Only the close price is materialized (RV/BPV/J use close-to-close log returns),
keeping the resample cheap: `price.resample('1min').last()`.

Pure pandas/numpy, no GPU. Used by `m12_hf_har_rv_j.py` (fork of m12_har_rv_j.py).
"""

from __future__ import annotations

import os
import gzip
from pathlib import Path

import numpy as np
import pandas as pd

from intraday_loader import IntradayDataset  # reuse the dataclass contract

DEFAULT_DATA_ROOT = Path(os.environ.get(
    "TRADING_DATA_ROOT",
    "G:/Mon Drive/MyIA/Dev/Trading/Data",
))

# Window aligned with #1630 / the decisive post-2018 segment (bear-2022 + recovery-2023).
# The BTC tick source covers 2011-2024; we keep 2018-01 onward by default so the
# minute vs hourly comparison shares a common recent period.
DEFAULT_START = pd.Timestamp("2018-01-01")


def load_bitstamp_btc_minute(
    path: Path | str | None = None,
    sample_freq: str = "1min",
    start: pd.Timestamp | None = None,
    tmp_cache: Path | str | None = None,
) -> IntradayDataset:
    """Load Bitstamp BTC tick data, resample to `sample_freq` close prices.

    Parameters
    ----------
    sample_freq : str
        Pandas offset alias for sparse sampling. ``"1min"`` (default, near-optimal
        for liquid BTC) or ``"5min"`` (defensive, microstructure-robust).
    start : pd.Timestamp | None
        Drop data strictly before this date (default 2018-01-01, aligned with the
        #1630 window and the decisive 2022/2023 regimes).
    tmp_cache : Path | str | None
        Optional on-disk Parquet cache for the resampled close (avoids re-resampling
        the 70M-tick source on repeated runs).

    Returns
    -------
    IntradayDataset
        symbol="BTC-USD", source="bitstamp_minute", df indexed by tz-naive
        DatetimeIndex at `sample_freq`, with a single ``close`` column.
    """
    p = Path(path) if path else DEFAULT_DATA_ROOT / "bitstampUSD.csv.gz"
    if not p.exists():
        raise FileNotFoundError(f"Bitstamp BTC tick gz not found at {p}")
    if start is None:
        start = DEFAULT_START

    cache_path = None
    if tmp_cache is not None:
        cache_path = Path(tmp_cache)
        cache_key = f"btc_bitstamp_{sample_freq}_{start:%Y%m%d}.parquet"
        cache_file = cache_path / cache_key
        if cache_file.exists():
            df = pd.read_parquet(cache_file)
            df.index = pd.to_datetime(df.index)
            if "close" not in df.columns:
                df.columns = ["close"]
            return IntradayDataset("BTC-USD", df, source="bitstamp_minute")

    # Stream-decompress the tick CSV: unix_seconds, price, amount.
    with gzip.open(p, "rt") as f:
        ticks = pd.read_csv(
            f,
            header=None,
            names=["ts", "price", "amount"],
            usecols=["ts", "price"],
            dtype={"ts": "int64", "price": "float32"},
        )

    # Drop bogus epoch-zero artefacts (some Bitcoincharts dumps contain a few
    # 1970-timestamped rows). Convert to tz-naive UTC DatetimeIndex.
    ticks = ticks[ticks["ts"] > 946_684_800]  # > 2000-01-01
    ticks.index = pd.to_datetime(ticks["ts"].astype("int64"), unit="s", utc=True)
    ticks.index = ticks.index.tz_convert(None)
    ticks = ticks[~ticks.index.duplicated(keep="last")]

    # Close = last observed trade price in each `sample_freq` bucket.
    close = ticks["price"].resample(sample_freq).last().dropna()
    close = close[close.index >= start]
    close.name = "close"

    if cache_path is not None:
        cache_path.mkdir(parents=True, exist_ok=True)
        close.to_frame().to_parquet(cache_file)

    df = close.to_frame("close")
    return IntradayDataset("BTC-USD", df, source="bitstamp_minute")


def minute_log_returns(ds: IntradayDataset) -> pd.Series:
    """Close-to-close log returns at the native minute granularity."""
    close = ds.df["close"].astype(float)
    rets = np.log(close).diff().dropna()
    rets.name = f"{ds.symbol}_logret_minute"
    return rets


def load_btc_minute_returns(
    sample_freq: str = "1min",
    start: pd.Timestamp | None = None,
    tmp_cache: Path | str | None = None,
) -> pd.Series:
    """Convenience: BTC minute log returns straight from the owned tick source."""
    ds = load_bitstamp_btc_minute(sample_freq=sample_freq, start=start, tmp_cache=tmp_cache)
    return minute_log_returns(ds)
