"""Tests for train_regime_classifier module."""

import numpy as np
import pandas as pd
import pytest
import torch

from train_regime_classifier import (
    RegimeLSTM,
    RegimeTransformer,
    create_model,
    compute_regime_features,
    prepare_regime_data,
    train_and_evaluate,
    run_multi_seed,
    MODEL_REGISTRY,
)


@pytest.fixture
def synthetic_closes():
    """10-asset synthetic prices, 500 days with regime-like volatility clustering."""
    np.random.seed(42)
    T, N = 500, 4
    symbols = ["BTC-USD", "ETH-USD", "LTC-USD", "XRP-USD"]
    returns = np.random.randn(T, N).astype(np.float32) * 0.02
    # Create volatility regimes
    vol_state = np.zeros(T)
    for t in range(1, T):
        if np.random.rand() < 0.02:
            vol_state[t] = 1 - vol_state[t - 1]
        else:
            vol_state[t] = vol_state[t - 1]
    returns *= (1 + vol_state[:, None] * 2)
    closes = (1 + pd.DataFrame(returns, columns=symbols)).cumprod() * 100
    return closes


@pytest.fixture
def synthetic_labels(synthetic_closes):
    """Generate simple regime labels (3-state via volatility percentile)."""
    closes = synthetic_closes
    mean_price = closes.mean(axis=1)
    ret = mean_price.pct_change().dropna()
    vol = ret.rolling(20).std().dropna()
    # 3 states based on volatility terciles
    q33, q66 = np.percentile(vol, [33, 66])
    labels = np.zeros(len(closes), dtype=np.int64)
    for i in range(len(vol)):
        idx = i + len(closes) - len(vol)
        if vol.iloc[i] < q33:
            labels[idx] = 0
        elif vol.iloc[i] < q66:
            labels[idx] = 1
        else:
            labels[idx] = 2
    return labels


class TestModelRegistry:
    def test_all_models_registered(self):
        assert "lstm" in MODEL_REGISTRY
        assert "transformer" in MODEL_REGISTRY

    def test_create_lstm(self):
        model = create_model("lstm", n_features=10, n_classes=3, d_model=32, n_layers=2)
        assert isinstance(model, RegimeLSTM)

    def test_create_transformer(self):
        model = create_model(
            "transformer", n_features=10, n_classes=3, d_model=32, n_layers=2, n_heads=4,
        )
        assert isinstance(model, RegimeTransformer)

    def test_unknown_model_raises(self):
        with pytest.raises(ValueError, match="Unknown model"):
            create_model("gru", n_features=10, n_classes=3)


class TestModelForward:
    def test_lstm_forward(self):
        model = RegimeLSTM(n_features=10, n_classes=3, d_model=32, n_layers=2)
        x = torch.randn(8, 60, 10)
        out = model(x)
        assert out.shape == (8, 3)

    def test_transformer_forward(self):
        model = RegimeTransformer(
            n_features=10, n_classes=3, d_model=32, n_layers=2, n_heads=4,
        )
        x = torch.randn(8, 60, 10)
        out = model(x)
        assert out.shape == (8, 3)


class TestFeatures:
    def test_compute_features_shape(self, synthetic_closes):
        features = compute_regime_features(synthetic_closes, lookback=20)
        assert features.shape[0] < len(synthetic_closes)  # NaN dropped
        assert features.shape[1] > 0

    def test_no_nan(self, synthetic_closes):
        features = compute_regime_features(synthetic_closes, lookback=20)
        assert not features.isna().any().any()


class TestPrepareData:
    def test_output_shapes(self, synthetic_closes, synthetic_labels):
        features = compute_regime_features(synthetic_closes, lookback=20)
        X, y = prepare_regime_data(
            features, synthetic_labels, synthetic_closes.index,
            seq_len=30, horizon=2,
        )
        assert X.ndim == 3  # (N, seq_len, F)
        assert X.shape[1] == 30
        assert y.ndim == 1
        assert len(X) == len(y)
        assert set(np.unique(y)).issubset({0, 1, 2})

    def test_horizon_shift(self, synthetic_closes, synthetic_labels):
        features = compute_regime_features(synthetic_closes, lookback=20)
        X1, y1 = prepare_regime_data(
            features, synthetic_labels, synthetic_closes.index,
            seq_len=30, horizon=1,
        )
        X3, y3 = prepare_regime_data(
            features, synthetic_labels, synthetic_closes.index,
            seq_len=30, horizon=3,
        )
        # Longer horizon = fewer samples
        assert len(X3) < len(X1)


class TestTrainAndEvaluate:
    def test_dry_run_lstm(self, synthetic_closes, synthetic_labels):
        features = compute_regime_features(synthetic_closes, lookback=20)
        X, y = prepare_regime_data(
            features, synthetic_labels, synthetic_closes.index,
            seq_len=30, horizon=2,
        )
        n = len(X)
        split = int(n * 0.8)
        result = train_and_evaluate(
            X[:split], y[:split],
            X[split:], y[split:],
            model_type="lstm",
            d_model=16, n_layers=1,
            epochs=3, batch_size=16,
            device="cpu",
        )
        assert "metrics" in result
        assert "accuracy" in result["metrics"]
        assert 0 <= result["metrics"]["accuracy"] <= 1

    def test_dry_run_transformer(self, synthetic_closes, synthetic_labels):
        features = compute_regime_features(synthetic_closes, lookback=20)
        X, y = prepare_regime_data(
            features, synthetic_labels, synthetic_closes.index,
            seq_len=30, horizon=2,
        )
        n = len(X)
        split = int(n * 0.8)
        result = train_and_evaluate(
            X[:split], y[:split],
            X[split:], y[split:],
            model_type="transformer",
            d_model=16, n_layers=1, n_heads=2,
            epochs=3, batch_size=16,
            device="cpu",
        )
        assert result["metrics"]["accuracy"] > 0


class TestMultiSeed:
    def test_multi_seed_minimum(self, synthetic_closes, synthetic_labels):
        features = compute_regime_features(synthetic_closes, lookback=20)
        X, y = prepare_regime_data(
            features, synthetic_labels, synthetic_closes.index,
            seq_len=30, horizon=2,
        )
        summary = run_multi_seed(
            X, y,
            seeds=[42, 123, 456, 789],
            model_type="lstm",
            d_model=16, n_layers=1,
            epochs=2, batch_size=16,
            device="cpu",
        )
        assert summary["n_seeds"] == 4
        assert "mean_accuracy" in summary
        assert "edge" in summary
        assert "beats_majority" in summary
        assert len(summary["per_seed"]) == 4

    def test_multi_seed_requires_4(self, synthetic_closes, synthetic_labels):
        features = compute_regime_features(synthetic_closes, lookback=20)
        X, y = prepare_regime_data(
            features, synthetic_labels, synthetic_closes.index,
            seq_len=30, horizon=2,
        )
        with pytest.raises(AssertionError, match=">=4"):
            run_multi_seed(
                X, y,
                seeds=[42, 123],
                model_type="lstm",
                d_model=16, n_layers=1,
                epochs=2, batch_size=16,
                device="cpu",
            )
