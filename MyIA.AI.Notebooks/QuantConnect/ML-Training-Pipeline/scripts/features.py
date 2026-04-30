"""
Reusable feature engineering for financial OHLCV data.

Provides composable indicator functions and a FeatureEngineer class
that computes all indicators, handles NaN removal, and caches results
as Parquet for fast reload.

Indicators:
    Returns (1d/5d/10d/20d), Volatility (5d/20d), Volume ratio,
    MA ratios (5/10/20/60), RSI-14, MACD + signal, Bollinger Band width,
    True Range, ATR-14, OBV (On-Balance Volume)

Usage:
    from features import FeatureEngineer

    engineer = FeatureEngineer(lookback=20)
    features = engineer.transform(df)  # DataFrame with all features + target

    # Cache to parquet for fast reload
    engineer.transform(df, cache_path="features_cache/spy_features.parquet")

    # Load from cache
    features = engineer.load_cache("features_cache/spy_features.parquet")
"""

import hashlib
from pathlib import Path

import numpy as np
import pandas as pd


def compute_returns(df: pd.DataFrame, windows: list[int] | None = None) -> pd.DataFrame:
    """Compute percentage returns at multiple horizons."""
    if windows is None:
        windows = [1, 5, 10, 20]
    feat = pd.DataFrame(index=df.index)
    for w in windows:
        feat[f"ret_{w}d"] = df["Close"].pct_change(w)
    return feat


def compute_volatility(df: pd.DataFrame, windows: list[int] | None = None) -> pd.DataFrame:
    """Compute realized volatility (rolling std of returns)."""
    if windows is None:
        windows = [5, 20]
    feat = pd.DataFrame(index=df.index)
    returns = df["Close"].pct_change()
    for w in windows:
        feat[f"vol_{w}d"] = returns.rolling(w).std()
    return feat


def compute_volume_ratio(df: pd.DataFrame, window: int = 20) -> pd.DataFrame:
    """Volume divided by its rolling mean."""
    feat = pd.DataFrame(index=df.index)
    feat["vol_ratio"] = df["Volume"] / df["Volume"].rolling(window).mean()
    return feat


def compute_ma_ratios(df: pd.DataFrame, windows: list[int] | None = None) -> pd.DataFrame:
    """Price / moving average ratio at multiple horizons."""
    if windows is None:
        windows = [5, 10, 20, 60]
    feat = pd.DataFrame(index=df.index)
    for w in windows:
        feat[f"ma_ratio_{w}"] = df["Close"] / df["Close"].rolling(w).mean()
    return feat


def compute_rsi(df: pd.DataFrame, period: int = 14) -> pd.DataFrame:
    """Relative Strength Index."""
    feat = pd.DataFrame(index=df.index)
    delta = df["Close"].diff()
    gain = delta.where(delta > 0, 0.0).rolling(period).mean()
    loss = (-delta.where(delta < 0, 0.0)).rolling(period).mean()
    rs = gain / loss.replace(0, 1e-10)
    feat[f"rsi_{period}"] = 100 - (100 / (1 + rs))
    return feat


def compute_macd(
    df: pd.DataFrame,
    fast: int = 12,
    slow: int = 26,
    signal: int = 9,
) -> pd.DataFrame:
    """MACD line and signal line."""
    feat = pd.DataFrame(index=df.index)
    ema_fast = df["Close"].ewm(span=fast, adjust=False).mean()
    ema_slow = df["Close"].ewm(span=slow, adjust=False).mean()
    feat["macd"] = ema_fast - ema_slow
    feat["macd_signal"] = feat["macd"].ewm(span=signal, adjust=False).mean()
    return feat


def compute_bollinger(df: pd.DataFrame, window: int = 20) -> pd.DataFrame:
    """Bollinger Band width (normalized)."""
    feat = pd.DataFrame(index=df.index)
    sma = df["Close"].rolling(window).mean()
    std = df["Close"].rolling(window).std()
    feat["bb_width"] = (df["Close"] - sma) / (2 * std.replace(0, 1e-10))
    return feat


def compute_true_range_atr(df: pd.DataFrame, period: int = 14) -> pd.DataFrame:
    """True Range and Average True Range (requires OHLC)."""
    feat = pd.DataFrame(index=df.index)
    if "High" not in df.columns or "Low" not in df.columns:
        return feat
    feat["true_range"] = (df["High"] - df["Low"]) / df["Close"]
    feat[f"atr_{period}"] = feat["true_range"].rolling(period).mean()
    return feat


def compute_obv(df: pd.DataFrame) -> pd.DataFrame:
    """On-Balance Volume."""
    feat = pd.DataFrame(index=df.index)
    direction = np.sign(df["Close"].diff())
    direction.iloc[0] = 0
    feat["obv"] = (direction * df["Volume"]).cumsum()
    # Normalized OBV
    feat["obv_norm"] = feat["obv"] / feat["obv"].rolling(20).std().replace(0, 1e-10)
    return feat


class FeatureEngineer:
    """Composable feature engineering for OHLCV data.

    Computes all indicators, adds a forward-return target, drops NaN rows,
    and optionally caches results as Parquet.

    Args:
        lookback: Minimum rows to keep after NaN removal (default 20).
        indicators: List of indicator names to compute. Default: all.
            Options: returns, volatility, volume_ratio, ma_ratios, rsi,
                     macd, bollinger, true_range_atr, obv
    """

    ALL_INDICATORS = [
        "returns",
        "volatility",
        "volume_ratio",
        "ma_ratios",
        "rsi",
        "macd",
        "bollinger",
        "true_range_atr",
        "obv",
    ]

    def __init__(
        self,
        lookback: int = 20,
        indicators: list[str] | None = None,
    ):
        self.lookback = lookback
        self.indicators = indicators or self.ALL_INDICATORS

    def transform(
        self,
        df: pd.DataFrame,
        cache_path: str | Path | None = None,
        add_target: bool = True,
    ) -> pd.DataFrame:
        """Compute features from OHLCV DataFrame.

        Args:
            df: DataFrame with at least Close, Volume columns (OHLC for some indicators).
            cache_path: If provided, save/load features as Parquet.
            add_target: Add forward 1-day return as 'target' column.

        Returns:
            DataFrame with feature columns (and optional target), NaN rows dropped.
        """
        if cache_path:
            cache_path = Path(cache_path)
            cache_path.parent.mkdir(parents=True, exist_ok=True)
            if cache_path.exists():
                cached = pd.read_parquet(cache_path)
                data_hash = self._data_hash(df)
                if cached.attrs.get("data_hash") == data_hash:
                    return cached

        parts = []
        for ind in self.indicators:
            if ind == "returns":
                parts.append(compute_returns(df))
            elif ind == "volatility":
                parts.append(compute_volatility(df))
            elif ind == "volume_ratio":
                parts.append(compute_volume_ratio(df))
            elif ind == "ma_ratios":
                parts.append(compute_ma_ratios(df))
            elif ind == "rsi":
                parts.append(compute_rsi(df))
            elif ind == "macd":
                parts.append(compute_macd(df))
            elif ind == "bollinger":
                parts.append(compute_bollinger(df))
            elif ind == "true_range_atr":
                parts.append(compute_true_range_atr(df))
            elif ind == "obv":
                parts.append(compute_obv(df))

        features = pd.concat(parts, axis=1)

        if add_target:
            features["target"] = df["Close"].pct_change().shift(-1)

        features = features.dropna()

        if cache_path:
            features.attrs["data_hash"] = self._data_hash(df)
            features.to_parquet(cache_path)

        return features

    @staticmethod
    def _data_hash(df: pd.DataFrame) -> str:
        return hashlib.sha256(
            pd.util.hash_pandas_object(df).values.tobytes()
        ).hexdigest()[:16]

    @staticmethod
    def load_cache(cache_path: str | Path) -> pd.DataFrame:
        """Load features from Parquet cache."""
        return pd.read_parquet(Path(cache_path))

    @property
    def feature_columns(self) -> list[str]:
        """Return expected feature column names (excluding target)."""
        dummy_index = pd.date_range("2000-01-01", periods=100, freq="B")
        dummy_df = pd.DataFrame(
            {
                "Close": 100.0 + np.random.randn(100).cumsum(),
                "Open": 100.0 + np.random.randn(100).cumsum(),
                "High": 101.0 + np.random.randn(100).cumsum(),
                "Low": 99.0 + np.random.randn(100).cumsum(),
                "Volume": np.abs(np.random.randn(100)) * 1e6,
            },
            index=dummy_index,
        )
        features = self.transform(dummy_df, add_target=False)
        return list(features.columns)
