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
    alpha = 1.0 / period
    gain = delta.where(delta > 0, 0.0).ewm(alpha=alpha, min_periods=period).mean()
    loss = (-delta.where(delta < 0, 0.0)).ewm(alpha=alpha, min_periods=period).mean()
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


def compute_obv(df: pd.DataFrame, window: int = 20) -> pd.DataFrame:
    """On-Balance Volume (rolling-std normalized).

    Raw OBV cumsum is non-stationary and leaks temporal position.
    We keep only the rolling-std normalized variant.
    """
    feat = pd.DataFrame(index=df.index)
    direction = np.sign(df["Close"].diff())
    direction.iloc[0] = 0
    raw_obv = (direction * df["Volume"]).cumsum()
    feat["obv"] = raw_obv / raw_obv.rolling(window).std().replace(0, 1e-10)
    return feat


def compute_regime(df: pd.DataFrame, ma_window: int = 200, vol_window: int = 63) -> pd.DataFrame:
    """Market regime indicators: trend and volatility regime."""
    feat = pd.DataFrame(index=df.index)
    sma = df["Close"].rolling(ma_window).mean()
    feat["trend_regime"] = (df["Close"] > sma).astype(float)
    feat["trend_strength"] = (df["Close"] - sma) / sma
    realized_vol = df["Close"].pct_change().rolling(vol_window).std()
    vol_rank = realized_vol.rolling(252, min_periods=63).rank(pct=True)
    feat["vol_regime"] = vol_rank
    feat["vol_zscore"] = (realized_vol - realized_vol.rolling(252, min_periods=63).mean()) / \
        realized_vol.rolling(252, min_periods=63).std().replace(0, 1e-10)
    return feat


def compute_momentum(df: pd.DataFrame, windows: list[int] | None = None) -> pd.DataFrame:
    """Advanced momentum: ROC, Stochastic oscillator, Williams %R."""
    if windows is None:
        windows = [5, 10, 21]
    feat = pd.DataFrame(index=df.index)
    for w in windows:
        feat[f"roc_{w}"] = df["Close"].pct_change(w)
    if "High" in df.columns and "Low" in df.columns:
        for w in [14, 28]:
            low_min = df["Low"].rolling(w).min()
            high_max = df["High"].rolling(w).max()
            range_val = (high_max - low_min).replace(0, 1e-10)
            feat[f"stoch_k_{w}"] = 100 * (df["Close"] - low_min) / range_val
            feat[f"williams_r_{w}"] = -100 * (high_max - df["Close"]) / range_val
    return feat


def compute_statistical(df: pd.DataFrame, window: int = 20) -> pd.DataFrame:
    """Higher-order statistical features: skewness, kurtosis, autocorrelation."""
    feat = pd.DataFrame(index=df.index)
    ret = df["Close"].pct_change()
    feat["skewness"] = ret.rolling(window).skew()
    feat["kurtosis"] = ret.rolling(window).kurt()
    feat["autocorr"] = ret.rolling(window).apply(
        lambda x: x.autocorr(lag=1) if len(x) > 2 else 0, raw=False
    )
    feat["downside_vol"] = ret.where(ret < 0, 0).rolling(window).std()
    feat["upside_vol"] = ret.where(ret > 0, 0).rolling(window).std()
    return feat


def compute_price_acceleration(df: pd.DataFrame, windows: list[int] | None = None) -> pd.DataFrame:
    """Second derivative of price: momentum of momentum."""
    if windows is None:
        windows = [5, 10, 20]
    feat = pd.DataFrame(index=df.index)
    mom1 = df["Close"].pct_change()
    for w in windows:
        mom2 = mom1 - mom1.shift(w)
        feat[f"acceleration_{w}"] = mom2
    return feat


def compute_cross_sectional(
    df: pd.DataFrame, panel: dict[str, pd.DataFrame] | None = None
) -> pd.DataFrame:
    """Cross-sectional features: relative rank and spread vs panel assets.

    Args:
        df: Primary asset OHLCV data.
        panel: Dict of {symbol: DataFrame} for panel assets.
            If None, returns empty DataFrame (no panel data).
    """
    feat = pd.DataFrame(index=df.index)
    if panel is None:
        return feat
    primary_ret = df["Close"].pct_change()
    panel_rets = {"primary": primary_ret}
    for sym, panel_df in panel.items():
        if "Close" in panel_df.columns:
            panel_rets[sym] = panel_df["Close"].pct_change()
    panel_df_all = pd.DataFrame(panel_rets)
    feat["rel_rank"] = panel_df_all.rank(axis=1).loc[:, "primary"]
    n_assets = len(panel_rets)
    feat["rel_spread"] = primary_ret - panel_df_all.drop(columns="primary").mean(axis=1)
    feat["rel_rank_norm"] = feat["rel_rank"] / n_assets
    return feat


def compute_cross_asset_ratios(
    df: pd.DataFrame,
    bond: pd.Series | None = None,
    commodity: pd.Series | None = None,
    equity_index: pd.Series | None = None,
    window: int = 20,
) -> pd.DataFrame:
    """Cross-asset ratio features: bond-equity, commodity momentum, equity strength.

    Args:
        df: Primary asset OHLCV data.
        bond: Bond price/index series (e.g. TLT closes).
        commodity: Commodity price/index series (e.g. DBC closes).
        equity_index: Broad equity index series (e.g. SPY closes).
        window: Rolling window for ratio normalization.
    """
    feat = pd.DataFrame(index=df.index)
    primary = df["Close"]

    if bond is not None:
        bond_aligned = bond.reindex(df.index).ffill()
        ratio = primary / bond_aligned
        feat["bond_equity_ratio"] = ratio
        feat["bond_equity_zscore"] = (
            (ratio - ratio.rolling(window).mean())
            / ratio.rolling(window).std().replace(0, 1e-10)
        )

    if commodity is not None:
        comm_aligned = commodity.reindex(df.index).ffill()
        comm_ret = comm_aligned.pct_change(window)
        feat["commodity_momentum"] = comm_ret

    if equity_index is not None:
        eq_aligned = equity_index.reindex(df.index).ffill()
        feat["equity_strength"] = primary / eq_aligned
        eq_ret = eq_aligned.pct_change(window)
        feat["equity_breadth_momentum"] = eq_ret

    return feat


def compute_vix_features(
    df: pd.DataFrame,
    vix: pd.Series | None = None,
    vix9d: pd.Series | None = None,
    window: int = 20,
) -> pd.DataFrame:
    """Volatility regime features from VIX data.

    Args:
        df: Primary asset OHLCV data.
        vix: VIX close series (^VIX). If None, returns empty DataFrame.
        vix9d: VIX9D close series (9-day VIX). Optional.
        window: Rolling window for VIX normalization.
    """
    feat = pd.DataFrame(index=df.index)
    if vix is None:
        return feat

    vix_aligned = vix.reindex(df.index).ffill()
    feat["vix_level"] = vix_aligned
    feat["vix_change_1d"] = vix_aligned.pct_change()
    feat["vix_change_5d"] = vix_aligned.pct_change(5)
    feat["vix_zscore"] = (
        (vix_aligned - vix_aligned.rolling(window).mean())
        / vix_aligned.rolling(window).std().replace(0, 1e-10)
    )
    feat["vix_rank_252d"] = vix_aligned.rolling(252, min_periods=63).rank(pct=True)

    if vix9d is not None:
        vix9d_aligned = vix9d.reindex(df.index).ffill()
        feat["vix_term_spread"] = vix_aligned - vix9d_aligned
        feat["vix_term_zscore"] = (
            (feat["vix_term_spread"] - feat["vix_term_spread"].rolling(window).mean())
            / feat["vix_term_spread"].rolling(window).std().replace(0, 1e-10)
        )

    return feat


def compute_macro_features(
    df: pd.DataFrame,
    rates_10y: pd.Series | None = None,
    rates_2y: pd.Series | None = None,
    fed_funds: pd.Series | None = None,
    window: int = 20,
) -> pd.DataFrame:
    """Macro features from interest rates and Fed data.

    Args:
        df: Primary asset OHLCV data.
        rates_10y: 10-year Treasury yield series (e.g. DGS10 from FRED).
        rates_2y: 2-year Treasury yield series (e.g. DGS2 from FRED).
        fed_funds: Federal funds rate series (e.g. DFF from FRED).
        window: Rolling window for normalization.
    """
    feat = pd.DataFrame(index=df.index)

    if rates_10y is not None:
        r10 = rates_10y.reindex(df.index).ffill()
        feat["rate_10y"] = r10
        feat["rate_10y_change_5d"] = r10.diff(5)
        feat["rate_10y_change_20d"] = r10.diff(window)

    if rates_2y is not None:
        r2 = rates_2y.reindex(df.index).ffill()
        feat["rate_2y"] = r2

    if rates_10y is not None and rates_2y is not None:
        r10 = rates_10y.reindex(df.index).ffill()
        r2 = rates_2y.reindex(df.index).ffill()
        spread = r10 - r2
        feat["yield_spread_10y_2y"] = spread
        feat["yield_curve_slope"] = (
            (spread - spread.rolling(window).mean())
            / spread.rolling(window).std().replace(0, 1e-10)
        )
        feat["yield_inverted"] = (spread < 0).astype(float)

    if fed_funds is not None:
        ff = fed_funds.reindex(df.index).ffill()
        feat["fed_funds_rate"] = ff
        feat["fed_funds_change_20d"] = ff.diff(window)

    return feat


class FeatureEngineer:
    """Composable feature engineering for OHLCV data.

    Computes all indicators, adds a forward-return target, drops NaN rows,
    and optionally caches results as Parquet.

    Args:
        lookback: Minimum rows to keep after NaN removal (default 20).
        indicators: List of indicator names to compute. Default: all.
            Options: returns, volatility, volume_ratio, ma_ratios, rsi,
                     macd, bollinger, true_range_atr, obv, regime,
                     momentum, statistical, price_acceleration
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
        "regime",
        "momentum",
        "statistical",
        "price_acceleration",
        "cross_sectional",
        "cross_asset_ratios",
        "vix_features",
        "macro_features",
    ]

    def __init__(
        self,
        lookback: int = 20,
        indicators: list[str] | None = None,
        panel: dict[str, pd.DataFrame] | None = None,
        bond: pd.Series | None = None,
        commodity: pd.Series | None = None,
        equity_index: pd.Series | None = None,
        vix: pd.Series | None = None,
        vix9d: pd.Series | None = None,
        rates_10y: pd.Series | None = None,
        rates_2y: pd.Series | None = None,
        fed_funds: pd.Series | None = None,
    ):
        self.lookback = lookback
        self.indicators = indicators or self.ALL_INDICATORS
        self.panel = panel
        self.bond = bond
        self.commodity = commodity
        self.equity_index = equity_index
        self.vix = vix
        self.vix9d = vix9d
        self.rates_10y = rates_10y
        self.rates_2y = rates_2y
        self.fed_funds = fed_funds

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
                cached = self.load_cache(cache_path)
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
            elif ind == "regime":
                parts.append(compute_regime(df))
            elif ind == "momentum":
                parts.append(compute_momentum(df))
            elif ind == "statistical":
                parts.append(compute_statistical(df))
            elif ind == "price_acceleration":
                parts.append(compute_price_acceleration(df))
            elif ind == "cross_sectional":
                parts.append(compute_cross_sectional(df, panel=self.panel))
            elif ind == "cross_asset_ratios":
                parts.append(compute_cross_asset_ratios(
                    df, bond=self.bond, commodity=self.commodity,
                    equity_index=self.equity_index, window=self.lookback,
                ))
            elif ind == "vix_features":
                parts.append(compute_vix_features(
                    df, vix=self.vix, vix9d=self.vix9d, window=self.lookback,
                ))
            elif ind == "macro_features":
                parts.append(compute_macro_features(
                    df, rates_10y=self.rates_10y, rates_2y=self.rates_2y,
                    fed_funds=self.fed_funds, window=self.lookback,
                ))

        features = pd.concat(parts, axis=1)

        if add_target:
            features["target"] = df["Close"].pct_change().shift(-1)

        features = features.dropna()

        if cache_path:
            data_hash = self._data_hash(df)
            features.attrs["data_hash"] = data_hash
            features.to_parquet(cache_path)
            # Store hash separately (Parquet attrs not reliably preserved)
            hash_path = Path(cache_path).with_suffix(".hash")
            hash_path.write_text(data_hash, encoding="utf-8")

        return features

    @staticmethod
    def _data_hash(df: pd.DataFrame) -> str:
        return hashlib.sha256(
            pd.util.hash_pandas_object(df).values.tobytes()
        ).hexdigest()[:16]

    @staticmethod
    def load_cache(cache_path: str | Path) -> pd.DataFrame:
        """Load features from Parquet cache, restoring hash from sidecar file."""
        cache_path = Path(cache_path)
        features = pd.read_parquet(cache_path)
        hash_path = cache_path.with_suffix(".hash")
        if hash_path.exists():
            features.attrs["data_hash"] = hash_path.read_text(encoding="utf-8").strip()
        return features

    @property
    def feature_columns(self) -> list[str]:
        """Return expected feature column names (excluding target)."""
        rng = np.random.default_rng(42)
        dummy_index = pd.date_range("2000-01-01", periods=100, freq="B")
        dummy_df = pd.DataFrame(
            {
                "Close": 100.0 + rng.standard_normal(100).cumsum(),
                "Open": 100.0 + rng.standard_normal(100).cumsum(),
                "High": 101.0 + rng.standard_normal(100).cumsum(),
                "Low": 99.0 + rng.standard_normal(100).cumsum(),
                "Volume": np.abs(rng.standard_normal(100)) * 1e6,
            },
            index=dummy_index,
        )
        features = self.transform(dummy_df, add_target=False)
        return list(features.columns)
