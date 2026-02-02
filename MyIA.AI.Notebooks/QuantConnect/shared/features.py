"""
Feature Engineering pour Trading Algorithmique

Ce module contient des fonctions pour créer des features à partir de données de marché,
utilisées principalement dans les notebooks ML (18-21).

Fonctions principales:
    - calculate_returns: Calcule retours multi-période
    - add_technical_features: Ajoute features techniques (SMA, RSI, etc.)
    - create_labels: Crée labels pour ML supervisé
    - walk_forward_split: Split train/test time-aware

Usage:
    from shared.features import calculate_returns, add_technical_features

    returns_df = calculate_returns(prices, periods=[1, 5, 20])
    features_df = add_technical_features(df, indicators={'sma': [20, 50], 'rsi': 14})
"""

import pandas as pd
import numpy as np
from typing import List, Dict, Tuple, Optional


def calculate_returns(prices: pd.Series, periods: List[int]) -> pd.DataFrame:
    """
    Calcule retours pour plusieurs périodes

    Args:
        prices: Série de prix (pd.Series avec index datetime)
        periods: Liste de périodes (ex: [1, 5, 20] pour 1-day, 5-day, 20-day)

    Returns:
        DataFrame avec colonnes 'return_1d', 'return_5d', 'return_20d', etc.

    Example:
        >>> prices = pd.Series([100, 101, 99, 102, 105])
        >>> returns = calculate_returns(prices, periods=[1, 2])
        >>> print(returns.columns)
        ['return_1d', 'return_2d']
    """
    returns_df = pd.DataFrame(index=prices.index)

    for period in periods:
        col_name = f'return_{period}d'
        returns_df[col_name] = prices.pct_change(periods=period)

    return returns_df


def add_technical_features(df: pd.DataFrame,
                          indicators: Dict[str, any],
                          price_col: str = 'close') -> pd.DataFrame:
    """
    Ajoute indicateurs techniques comme features

    Args:
        df: DataFrame avec colonnes OHLCV
        indicators: Dict d'indicateurs à calculer
            {
                'sma': [20, 50],      # SMA avec périodes 20 et 50
                'ema': [12, 26],      # EMA
                'rsi': 14,            # RSI avec période 14
                'macd': (12, 26, 9),  # MACD
                'bb': (20, 2)         # Bollinger Bands (période, std)
            }
        price_col: Nom colonne prix (default: 'close')

    Returns:
        DataFrame original avec features techniques ajoutées

    Example:
        >>> df = pd.DataFrame({'close': [100, 101, 99, 102, 105]})
        >>> df = add_technical_features(df, {'sma': [3], 'rsi': 3})
        >>> print('sma_3' in df.columns and 'rsi_3' in df.columns)
        True
    """
    result = df.copy()
    prices = result[price_col]

    # SMA (Simple Moving Average)
    if 'sma' in indicators:
        for period in indicators['sma']:
            result[f'sma_{period}'] = prices.rolling(window=period).mean()

    # EMA (Exponential Moving Average)
    if 'ema' in indicators:
        for period in indicators['ema']:
            result[f'ema_{period}'] = prices.ewm(span=period, adjust=False).mean()

    # RSI (Relative Strength Index)
    if 'rsi' in indicators:
        period = indicators['rsi']
        delta = prices.diff()
        gain = (delta.where(delta > 0, 0)).rolling(window=period).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(window=period).mean()
        rs = gain / loss
        result[f'rsi_{period}'] = 100 - (100 / (1 + rs))

    # MACD (Moving Average Convergence Divergence)
    if 'macd' in indicators:
        fast, slow, signal = indicators['macd']
        ema_fast = prices.ewm(span=fast, adjust=False).mean()
        ema_slow = prices.ewm(span=slow, adjust=False).mean()
        macd_line = ema_fast - ema_slow
        signal_line = macd_line.ewm(span=signal, adjust=False).mean()
        result['macd'] = macd_line
        result['macd_signal'] = signal_line
        result['macd_hist'] = macd_line - signal_line

    # Bollinger Bands
    if 'bb' in indicators:
        period, num_std = indicators['bb']
        sma = prices.rolling(window=period).mean()
        std = prices.rolling(window=period).std()
        result['bb_upper'] = sma + (std * num_std)
        result['bb_middle'] = sma
        result['bb_lower'] = sma - (std * num_std)
        result['bb_width'] = result['bb_upper'] - result['bb_lower']

    return result


def create_labels(returns: pd.Series,
                 threshold: float = 0.0,
                 method: str = 'binary') -> pd.Series:
    """
    Crée labels pour ML supervisé

    Args:
        returns: Série de retours (forward returns généralement)
        threshold: Seuil pour classification (default: 0.0)
        method: 'binary' (up/down), 'ternary' (up/neutral/down), ou 'regression'

    Returns:
        Series de labels
        - binary: 1 (up), 0 (down)
        - ternary: 1 (up), 0 (neutral), -1 (down)
        - regression: retours bruts

    Example:
        >>> returns = pd.Series([0.01, -0.005, 0.02, -0.01])
        >>> labels = create_labels(returns, threshold=0.0, method='binary')
        >>> print(labels.tolist())
        [1, 0, 1, 0]
    """
    if method == 'binary':
        return (returns > threshold).astype(int)

    elif method == 'ternary':
        labels = pd.Series(0, index=returns.index)
        labels[returns > threshold] = 1
        labels[returns < -threshold] = -1
        return labels

    elif method == 'regression':
        return returns

    else:
        raise ValueError(f"Unknown method: {method}")


def walk_forward_split(df: pd.DataFrame,
                      train_size: float = 0.7,
                      n_splits: int = 1) -> List[Tuple[pd.DataFrame, pd.DataFrame]]:
    """
    Split time series avec walk-forward validation

    Args:
        df: DataFrame avec index datetime
        train_size: Ratio train (default: 0.7 = 70% train, 30% test)
        n_splits: Nombre de splits (default: 1)

    Returns:
        Liste de tuples (train_df, test_df)

    Example:
        >>> df = pd.DataFrame({'price': range(100)},
        ...                   index=pd.date_range('2020-01-01', periods=100))
        >>> splits = walk_forward_split(df, train_size=0.7, n_splits=1)
        >>> len(splits[0][0]), len(splits[0][1])
        (70, 30)
    """
    if not isinstance(df.index, pd.DatetimeIndex):
        raise ValueError("DataFrame must have DatetimeIndex")

    splits = []

    if n_splits == 1:
        # Single split
        split_idx = int(len(df) * train_size)
        train = df.iloc[:split_idx]
        test = df.iloc[split_idx:]
        splits.append((train, test))

    else:
        # Multiple rolling splits
        total_size = len(df)
        test_size = int(total_size * (1 - train_size))
        train_initial_size = int(total_size * train_size)

        for i in range(n_splits):
            if i == 0:
                train_start = 0
                train_end = train_initial_size
            else:
                # Expand training window
                train_start = 0
                train_end = train_initial_size + (i * test_size)

            test_start = train_end
            test_end = test_start + test_size

            if test_end > total_size:
                break

            train = df.iloc[train_start:train_end]
            test = df.iloc[test_start:test_end]
            splits.append((train, test))

    return splits


def add_lagged_features(df: pd.DataFrame,
                       columns: List[str],
                       lags: List[int]) -> pd.DataFrame:
    """
    Ajoute features laggées (valeurs précédentes)

    Args:
        df: DataFrame
        columns: Colonnes à lagger
        lags: Liste de lags (ex: [1, 2, 5] pour t-1, t-2, t-5)

    Returns:
        DataFrame avec features laggées ajoutées

    Example:
        >>> df = pd.DataFrame({'price': [100, 101, 102, 103]})
        >>> df = add_lagged_features(df, columns=['price'], lags=[1, 2])
        >>> print('price_lag_1' in df.columns and 'price_lag_2' in df.columns)
        True
    """
    result = df.copy()

    for col in columns:
        if col not in df.columns:
            continue

        for lag in lags:
            result[f'{col}_lag_{lag}'] = df[col].shift(lag)

    return result


def feature_importance_scores(model, feature_names: List[str]) -> pd.DataFrame:
    """
    Extrait feature importance depuis modèle ML

    Args:
        model: Modèle scikit-learn ou compatible (doit avoir .feature_importances_)
        feature_names: Noms des features

    Returns:
        DataFrame trié par importance (décroissant)

    Example:
        >>> from sklearn.ensemble import RandomForestClassifier
        >>> import numpy as np
        >>> X = np.random.rand(100, 5)
        >>> y = np.random.randint(0, 2, 100)
        >>> model = RandomForestClassifier(n_estimators=10, random_state=42)
        >>> model.fit(X, y)
        >>> importance = feature_importance_scores(model, [f'f{i}' for i in range(5)])
        >>> len(importance)
        5
    """
    if not hasattr(model, 'feature_importances_'):
        raise ValueError("Model must have .feature_importances_ attribute")

    importance_df = pd.DataFrame({
        'feature': feature_names,
        'importance': model.feature_importances_
    }).sort_values('importance', ascending=False)

    return importance_df


if __name__ == '__main__':
    # Tests rapides
    print("Testing features.py...")

    # Test calculate_returns
    prices = pd.Series([100, 101, 99, 102, 105],
                      index=pd.date_range('2020-01-01', periods=5))
    returns = calculate_returns(prices, periods=[1, 2])
    print(f"✓ calculate_returns: {returns.shape}")

    # Test add_technical_features
    df = pd.DataFrame({'close': [100, 101, 99, 102, 105]})
    df_with_features = add_technical_features(df, {'sma': [3], 'rsi': 3})
    print(f"✓ add_technical_features: {df_with_features.shape}")

    # Test create_labels
    returns_series = pd.Series([0.01, -0.005, 0.02, -0.01])
    labels = create_labels(returns_series, method='binary')
    print(f"✓ create_labels: {labels.tolist()}")

    # Test walk_forward_split
    df_ts = pd.DataFrame({'price': range(100)},
                        index=pd.date_range('2020-01-01', periods=100))
    splits = walk_forward_split(df_ts, train_size=0.7)
    print(f"✓ walk_forward_split: train={len(splits[0][0])}, test={len(splits[0][1])}")

    print("\nAll tests passed! ✓")
