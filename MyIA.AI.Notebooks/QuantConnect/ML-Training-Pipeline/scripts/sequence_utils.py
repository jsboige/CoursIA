"""Shared sequence building and normalization for time-series ML models.

Provides build_sequences (sliding window) and normalize_sequences (z-score
using training statistics only, preventing test-set leakage).

Previously duplicated across 8 training scripts. Unified here for
consistency and deduplication.
"""

from __future__ import annotations

import numpy as np
import pandas as pd


def build_sequences(
    features: pd.DataFrame,
    seq_len: int = 20,
    pred_len: int = 1,
    target_col: str = "target",
) -> tuple[np.ndarray, np.ndarray, list[str]]:
    """Build sliding-window sequences from a feature DataFrame.

    Parameters
    ----------
    features : DataFrame
        Feature matrix with a target column.
    seq_len : int
        Input sequence length (lookback window).
    pred_len : int
        Prediction horizon. When 1, produces scalar targets (seq2one).
        When >1, produces multi-step targets (seq2seq).
    target_col : str
        Name of the target column to exclude from features.

    Returns
    -------
    X : ndarray of shape (n_samples, seq_len, n_features), float32
    y : ndarray of shape (n_samples,) or (n_samples, pred_len), float32
    feature_cols : list of str
    """
    feature_cols = [c for c in features.columns if c != target_col]
    data = features[feature_cols].values
    targets = features[target_col].values

    X, y = [], []
    if pred_len == 1:
        # seq2one: scalar targets (backward-compatible with LSTM/Transformer)
        for i in range(seq_len, len(data)):
            X.append(data[i - seq_len : i])
            y.append(targets[i])
    else:
        # seq2seq: multi-step targets
        for i in range(seq_len, len(data) - pred_len + 1):
            X.append(data[i - seq_len : i])
            y.append(targets[i : i + pred_len])

    return np.array(X, dtype=np.float32), np.array(y, dtype=np.float32), feature_cols


def normalize_sequences(
    X_train: np.ndarray,
    X_test: np.ndarray,
    X_val: np.ndarray | None = None,
) -> tuple:
    """Z-normalize features using training statistics only (anti-leakage).

    Parameters
    ----------
    X_train : ndarray
        Training data (used to compute mean and std).
    X_test : ndarray
        Test data to normalize.
    X_val : ndarray or None
        Optional validation data to normalize.

    Returns
    -------
    If X_val is None:
        (X_train_norm, X_test_norm, mean, std)
    If X_val is provided:
        (X_train_norm, X_test_norm, X_val_norm, mean, std)
    """
    mean = X_train.mean(axis=(0, 1), keepdims=True)
    std = X_train.std(axis=(0, 1), keepdims=True)
    std = np.where(std < 1e-8, 1.0, std)

    result = [
        (X_train - mean) / std,
        (X_test - mean) / std,
        mean.squeeze(),
        std.squeeze(),
    ]
    if X_val is not None:
        result.insert(2, (X_val - mean) / std)
        return tuple(result)
    return tuple(result)
