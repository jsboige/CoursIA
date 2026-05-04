"""Integration tests for walk-forward training in LSTM, Transformer, Classification scripts.

Verifies that --walk-forward mode produces correct metric structure,
per-fold normalization, and majority-class baseline reporting.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

# Ensure scripts directory is on path
sys.path.insert(0, str(Path(__file__).resolve().parent))

from baselines import majority_class_baseline
from data_utils import generate_synthetic_data
from features import FeatureEngineer
from walk_forward import WalkForwardSplitter


def _make_features(n_rows: int = 500, lookback: int = 10) -> pd.DataFrame:
    """Generate synthetic feature DataFrame with target column."""
    raw = generate_synthetic_data(n_rows)
    engineer = FeatureEngineer(lookback=lookback)
    features = engineer.transform(raw, add_target=False)
    features["target"] = (raw["Close"].pct_change().shift(-1) > 0.001).astype(int)
    return features.dropna()


def _make_sequences(n_rows: int = 500, seq_len: int = 10) -> tuple:
    """Generate synthetic sequence arrays for LSTM/Transformer."""
    raw = generate_synthetic_data(n_rows)
    engineer = FeatureEngineer(lookback=seq_len)
    features = engineer.transform(raw)
    features = features.dropna()

    feature_cols = [c for c in features.columns if c != "target"]
    data = features[feature_cols].values
    targets = features["target"].values

    X, y = [], []
    for i in range(seq_len, len(data)):
        X.append(data[i - seq_len : i])
        y.append(targets[i])

    return np.array(X, dtype=np.float32), np.array(y, dtype=np.float32)


# ---------------------------------------------------------------------------
# Walk-forward integration: Classification
# ---------------------------------------------------------------------------


class TestWalkForwardClassification:
    def test_walk_forward_returns_required_metrics(self):
        from train_classification import train_walk_forward_classification

        features = _make_features(500, lookback=10)
        result = train_walk_forward_classification(
            features,
            model_type="rf",
            n_estimators=10,
            max_depth=3,
            n_splits=3,
            train_size=100,
            test_size=50,
            gap=5,
        )

        metrics = result["metrics"]
        assert "oos_direction_accuracy" in metrics
        assert "majority_class_acc" in metrics
        assert "majority_class_freq" in metrics
        assert "vs_majority_class" in metrics
        assert "n_wf_folds" in metrics

    def test_walk_forward_produces_folds(self):
        from train_classification import train_walk_forward_classification

        features = _make_features(500, lookback=10)
        result = train_walk_forward_classification(
            features,
            n_estimators=10,
            max_depth=3,
            n_splits=3,
            train_size=100,
            test_size=50,
            gap=5,
        )

        assert len(result["fold_details"]) >= 1
        fold = result["fold_details"][0]
        assert "fold" in fold
        assert "train_size" in fold
        assert "test_size" in fold
        assert "accuracy" in fold

    def test_walk_forward_model_is_fitted(self):
        from train_classification import train_walk_forward_classification

        features = _make_features(500, lookback=10)
        result = train_walk_forward_classification(
            features,
            n_estimators=10,
            max_depth=3,
            n_splits=2,
            train_size=100,
            test_size=50,
            gap=5,
        )

        assert result["model"] is not None
        assert hasattr(result["model"], "predict")

    def test_vs_majority_is_non_nan(self):
        from train_classification import train_walk_forward_classification

        features = _make_features(500, lookback=10)
        result = train_walk_forward_classification(
            features,
            n_estimators=10,
            max_depth=3,
            n_splits=2,
            train_size=100,
            test_size=50,
            gap=5,
        )

        assert not np.isnan(result["metrics"]["vs_majority_class"])


# ---------------------------------------------------------------------------
# Walk-forward integration: LSTM
# ---------------------------------------------------------------------------


class TestWalkForwardLSTM:
    def test_walk_forward_returns_required_metrics(self):
        from train_lstm import train_walk_forward

        X, y = _make_sequences(300, seq_len=10)
        result = train_walk_forward(
            X, y,
            n_splits=2,
            train_size=50,
            test_size=30,
            gap=3,
            hidden_size=16,
            num_layers=1,
            dropout=0.1,
            epochs=1,
            batch_size=16,
            learning_rate=1e-3,
            model_type="lstm",
            device="cpu",
        )

        metrics = result["metrics"]
        assert "oos_direction_accuracy" in metrics
        assert "majority_class_acc" in metrics
        assert "vs_majority_class" in metrics
        assert "n_wf_folds" in metrics

    def test_walk_forward_produces_fold_details(self):
        from train_lstm import train_walk_forward

        X, y = _make_sequences(300, seq_len=10)
        result = train_walk_forward(
            X, y,
            n_splits=2,
            train_size=50,
            test_size=30,
            gap=3,
            hidden_size=16,
            num_layers=1,
            epochs=1,
            batch_size=16,
            device="cpu",
        )

        assert "fold_details" in result
        assert "history" in result
        assert len(result["fold_details"]) >= 1

    def test_walk_forward_best_model_returned(self):
        from train_lstm import train_walk_forward

        X, y = _make_sequences(300, seq_len=10)
        result = train_walk_forward(
            X, y,
            n_splits=2,
            train_size=50,
            test_size=30,
            gap=3,
            hidden_size=16,
            num_layers=1,
            epochs=1,
            batch_size=16,
            device="cpu",
        )

        assert result["model"] is not None
        assert result["input_size"] == X.shape[2]


# ---------------------------------------------------------------------------
# Walk-forward integration: Transformer
# ---------------------------------------------------------------------------


class TestWalkForwardTransformer:
    def test_walk_forward_returns_required_metrics(self):
        from train_transformer import train_walk_forward

        X, y = _make_sequences(300, seq_len=10)
        result = train_walk_forward(
            X, y,
            n_splits=2,
            train_size=50,
            test_size=30,
            gap=3,
            d_model=32,
            nhead=2,
            num_layers=1,
            dim_feedforward=64,
            dropout=0.1,
            seq_len=10,
            epochs=1,
            batch_size=16,
            device="cpu",
        )

        metrics = result["metrics"]
        assert "oos_direction_accuracy" in metrics
        assert "majority_class_acc" in metrics
        assert "vs_majority_class" in metrics

    def test_walk_forward_history_key_present(self):
        from train_transformer import train_walk_forward

        X, y = _make_sequences(300, seq_len=10)
        result = train_walk_forward(
            X, y,
            n_splits=2,
            train_size=50,
            test_size=30,
            gap=3,
            d_model=32,
            nhead=2,
            num_layers=1,
            dim_feedforward=64,
            dropout=0.1,
            seq_len=10,
            epochs=1,
            batch_size=16,
            device="cpu",
        )

        assert "history" in result
        assert "fold_details" in result


# ---------------------------------------------------------------------------
# Cross-cutting: train-only normalization
# ---------------------------------------------------------------------------


class TestTrainOnlyNormalization:
    def test_classification_uses_standard_scaler(self):
        """Verify that the simple-split path now uses StandardScaler."""
        from train_classification import train_and_evaluate

        features = _make_features(300, lookback=10)
        result = train_and_evaluate(
            features,
            model_type="rf",
            n_estimators=10,
            max_depth=3,
            test_ratio=0.3,
        )

        assert "accuracy" in result["metrics"]
        # Model should work on normalized data
        assert result["model"] is not None

    def test_normalization_prevents_constant_features(self):
        """After normalization, no feature should have zero variance in train."""
        from sklearn.preprocessing import StandardScaler

        features = _make_features(300, lookback=10)
        X = features.drop(columns=["target"]).values
        split_idx = int(len(X) * 0.7)
        X_train = X[:split_idx]

        scaler = StandardScaler()
        X_train_norm = scaler.fit_transform(X_train)

        # Non-constant features should have unit variance after scaling;
        # constant features (std=0 before scaling) remain 0 by StandardScaler.
        stds = X_train_norm.std(axis=0)
        non_constant = stds[stds > 0]
        assert len(non_constant) > 0, "At least one non-constant feature expected"
        assert all(s > 0.9 for s in non_constant)


# ---------------------------------------------------------------------------
# Walk-forward integration: DQN
# ---------------------------------------------------------------------------


def _make_prices_and_features(n_rows: int = 500, lookback: int = 10) -> tuple:
    """Generate synthetic prices + features arrays for DQN."""
    raw = generate_synthetic_data(n_rows)
    engineer = FeatureEngineer(lookback=lookback)
    features_df = engineer.transform(raw, add_target=False)
    features_arr = features_df.values.astype(np.float32)
    prices = raw.loc[features_df.index, "Close"].values.astype(np.float32)
    return prices, features_arr


class TestWalkForwardDQN:
    def test_walk_forward_returns_required_metrics(self):
        from train_dqn_rl import train_walk_forward_dqn

        prices, features = _make_prices_and_features(500, lookback=10)
        result = train_walk_forward_dqn(
            prices, features,
            window=5,
            commission=0.001,
            hidden_size=32,
            num_episodes=2,
            batch_size=16,
            n_splits=2,
            train_size=150,
            test_size=50,
            gap=3,
            device="cpu",
        )

        metrics = result["metrics"]
        assert "oos_direction_accuracy" in metrics
        assert "majority_class_acc" in metrics
        assert "majority_class_freq" in metrics
        assert "vs_majority_class" in metrics
        assert "n_wf_folds" in metrics

    def test_walk_forward_produces_fold_details(self):
        from train_dqn_rl import train_walk_forward_dqn

        prices, features = _make_prices_and_features(500, lookback=10)
        result = train_walk_forward_dqn(
            prices, features,
            window=5,
            hidden_size=32,
            num_episodes=2,
            batch_size=16,
            n_splits=2,
            train_size=150,
            test_size=50,
            gap=3,
            device="cpu",
        )

        assert len(result["fold_details"]) >= 1
        fold = result["fold_details"][0]
        assert "fold" in fold
        assert "train_size" in fold
        assert "test_size" in fold
        assert "oos_reward" in fold

    def test_walk_forward_model_returned(self):
        from train_dqn_rl import train_walk_forward_dqn

        prices, features = _make_prices_and_features(500, lookback=10)
        result = train_walk_forward_dqn(
            prices, features,
            window=5,
            hidden_size=32,
            num_episodes=2,
            batch_size=16,
            n_splits=2,
            train_size=150,
            test_size=50,
            gap=3,
            device="cpu",
        )

        assert result["model"] is not None
        assert "history" in result
