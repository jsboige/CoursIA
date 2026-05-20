"""Tests for moe_experts.py — MoE router with regime-aware routing."""

import numpy as np
import pandas as pd
import pytest
from sklearn.datasets import make_classification

from moe_experts import (
    ExpertConfig,
    ExpertStats,
    MoEConfig,
    MoERouter,
    create_expert,
    train_moe_walk_forward,
    _PytorchExpertWrapper,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def simple_data():
    """3-regime synthetic dataset with clear separation."""
    np.random.seed(42)
    n = 300
    X = np.random.randn(n, 5)
    regimes = np.array(["bull"] * 100 + ["bear"] * 100 + ["neutral"] * 100)
    # Bull regime: class 1 more likely when feature 0 > 0
    X[:100, 0] += 1.0
    # Bear regime: class 0 more likely when feature 0 < 0
    X[100:200, 0] -= 1.0
    y = (X[:, 0] > 0).astype(int)
    return X, y, regimes


@pytest.fixture
def imbalanced_data():
    """Dataset with one regime having very few samples."""
    np.random.seed(42)
    n = 200
    X = np.random.randn(n, 5)
    regimes = np.array(
        ["bull"] * 90 + ["bear"] * 90 + ["volatile"] * 20
    )
    y = (X[:, 0] > 0).astype(int)
    return X, y, regimes


# ---------------------------------------------------------------------------
# ExpertConfig / create_expert
# ---------------------------------------------------------------------------

class TestExpertConfig:
    def test_default_config(self):
        cfg = ExpertConfig(regime="bull")
        assert cfg.regime == "bull"
        assert cfg.model_type == "mlp"
        assert cfg.hidden_sizes == (64, 32)
        assert cfg.max_iter == 200

    def test_custom_config(self):
        cfg = ExpertConfig(regime="bear", hidden_sizes=(128,), max_iter=50)
        assert cfg.hidden_sizes == (128,)
        assert cfg.max_iter == 50

    def test_create_expert_mlp(self):
        cfg = ExpertConfig(regime="test", model_type="mlp")
        model = create_expert(cfg)
        assert hasattr(model, "fit")
        assert hasattr(model, "predict")
        assert hasattr(model, "predict_proba")

    def test_create_expert_unknown_type(self):
        cfg = ExpertConfig(regime="test", model_type="nonexistent")
        with pytest.raises(ValueError, match="Unknown model type"):
            create_expert(cfg)

    def test_expert_fit_predict(self):
        cfg = ExpertConfig(regime="test", max_iter=50)
        model = create_expert(cfg)
        X, y = make_classification(n_samples=100, n_features=5, random_state=42)
        model.fit(X, y)
        preds = model.predict(X)
        assert preds.shape == (100,)
        assert set(preds).issubset({0, 1})

    def test_create_expert_lstm(self):
        cfg = ExpertConfig(
            regime="test", model_type="lstm", max_iter=5,
            extra={"seq_len": 10, "hidden_size": 32, "num_layers": 1},
        )
        model = create_expert(cfg)
        assert hasattr(model, "fit")
        assert hasattr(model, "predict")
        assert hasattr(model, "predict_proba")

    def test_create_expert_transformer(self):
        cfg = ExpertConfig(
            regime="test", model_type="transformer", max_iter=5,
            extra={
                "seq_len": 10, "d_model": 32, "nhead": 4,
                "num_layers": 1, "hidden_size": 32,
            },
        )
        model = create_expert(cfg)
        assert hasattr(model, "fit")

    def test_lstm_expert_fit_predict(self):
        np.random.seed(42)
        n = 200
        X = np.random.randn(n, 10).astype(np.float32)
        y = (X[:, 0] > 0).astype(int)
        cfg = ExpertConfig(
            regime="test", model_type="lstm", max_iter=10,
            extra={"seq_len": 10, "hidden_size": 32, "num_layers": 1, "batch_size": 32},
        )
        model = create_expert(cfg)
        model.fit(X, y)
        preds = model.predict(X)
        assert preds.shape == (n,)
        assert set(preds).issubset({0, 1})
        proba = model.predict_proba(X)
        assert proba.shape == (n, 2)

    def test_transformer_expert_fit_predict(self):
        np.random.seed(42)
        n = 200
        X = np.random.randn(n, 10).astype(np.float32)
        y = (X[:, 0] > 0).astype(int)
        cfg = ExpertConfig(
            regime="test", model_type="transformer", max_iter=10,
            extra={
                "seq_len": 10, "d_model": 32, "nhead": 4,
                "num_layers": 1, "hidden_size": 32, "batch_size": 32,
            },
        )
        model = create_expert(cfg)
        model.fit(X, y)
        preds = model.predict(X)
        assert preds.shape == (n,)
        proba = model.predict_proba(X)
        assert proba.shape == (n, 2)


# ---------------------------------------------------------------------------
# MoEConfig
# ---------------------------------------------------------------------------

class TestMoEConfig:
    def test_default_config(self):
        cfg = MoEConfig()
        assert "bull" in cfg.regimes
        assert "bear" in cfg.regimes
        assert cfg.expert_type == "mlp"
        assert cfg.min_samples_per_expert == 50

    def test_custom_regimes(self):
        cfg = MoEConfig(regimes=["bull", "bear"])
        assert len(cfg.regimes) == 2


# ---------------------------------------------------------------------------
# MoERouter — fit
# ---------------------------------------------------------------------------

class TestMoERouterFit:
    def test_fit_all_regimes(self, simple_data):
        X, y, regimes = simple_data
        config = MoEConfig(min_samples_per_expert=30, max_iter=50)
        router = MoERouter(config)
        router.fit(X, y, regimes)

        assert router._fitted
        assert len(router.regimes) == 3
        assert all(s.fitted for s in router.stats.values())

    def test_fit_skips_small_regime(self, imbalanced_data):
        X, y, regimes = imbalanced_data
        config = MoEConfig(min_samples_per_expert=50, max_iter=50)
        router = MoERouter(config)
        router.fit(X, y, regimes)

        assert "bull" in router._experts
        assert "bear" in router._experts
        assert "volatile" not in router._experts
        assert router.stats["volatile"].fitted is False

    def test_fit_with_series_regime_labels(self, simple_data):
        X, y, regimes = simple_data
        regimes_series = pd.Series(regimes)
        config = MoEConfig(min_samples_per_expert=30, max_iter=50)
        router = MoERouter(config)
        router.fit(X, y, regimes_series)
        assert router._fitted

    def test_fit_returns_self(self, simple_data):
        X, y, regimes = simple_data
        router = MoERouter(MoEConfig(min_samples_per_expert=30, max_iter=50))
        result = router.fit(X, y, regimes)
        assert result is router

    def test_stats_populated(self, simple_data):
        X, y, regimes = simple_data
        config = MoEConfig(min_samples_per_expert=30, max_iter=50)
        router = MoERouter(config)
        router.fit(X, y, regimes)

        for regime in ["bull", "bear", "neutral"]:
            assert regime in router.stats
            assert router.stats[regime].n_train > 0
            assert router.stats[regime].fitted is True
            assert 0 <= router.stats[regime].train_accuracy <= 1


# ---------------------------------------------------------------------------
# MoERouter — predict
# ---------------------------------------------------------------------------

class TestMoERouterPredict:
    def test_predict_shape(self, simple_data):
        X, y, regimes = simple_data
        config = MoEConfig(min_samples_per_expert=30, max_iter=50)
        router = MoERouter(config)
        router.fit(X, y, regimes)
        preds = router.predict(X, regimes)
        assert preds.shape == (len(X),)

    def test_predict_binary_values(self, simple_data):
        X, y, regimes = simple_data
        config = MoEConfig(min_samples_per_expert=30, max_iter=50)
        router = MoERouter(config)
        router.fit(X, y, regimes)
        preds = router.predict(X, regimes)
        assert set(preds).issubset({0, 1})

    def test_predict_proba_shape(self, simple_data):
        X, y, regimes = simple_data
        config = MoEConfig(min_samples_per_expert=30, max_iter=50)
        router = MoERouter(config)
        router.fit(X, y, regimes)
        proba = router.predict_proba(X, regimes)
        assert proba.shape == (len(X), 2)
        assert np.allclose(proba.sum(axis=1), 1.0, atol=1e-6)

    def test_predict_unseen_regime_uses_fallback(self):
        np.random.seed(42)
        X = np.random.randn(200, 5)
        y = (X[:, 0] > 0).astype(int)
        train_regimes = np.array(["bull"] * 100 + ["bear"] * 100)
        test_regimes = np.array(["volatile"] * 50)

        config = MoEConfig(
            min_samples_per_expert=30,
            max_iter=50,
            fallback_regime="bull",
        )
        router = MoERouter(config)
        router.fit(X, y, train_regimes)
        preds = router.predict(X[:50], test_regimes)
        assert preds.shape == (50,)


# ---------------------------------------------------------------------------
# MoERouter — evaluate
# ---------------------------------------------------------------------------

class TestMoERouterEvaluate:
    def test_evaluate_overall_accuracy(self, simple_data):
        X, y, regimes = simple_data
        config = MoEConfig(min_samples_per_expert=30, max_iter=50)
        router = MoERouter(config)
        router.fit(X, y, regimes)
        result = router.evaluate(X, y, regimes)

        assert "overall_accuracy" in result
        assert 0 <= result["overall_accuracy"] <= 1
        assert result["n_samples"] == len(X)

    def test_evaluate_per_regime(self, simple_data):
        X, y, regimes = simple_data
        config = MoEConfig(min_samples_per_expert=30, max_iter=50)
        router = MoERouter(config)
        router.fit(X, y, regimes)
        result = router.evaluate(X, y, regimes)

        for regime in ["bull", "bear", "neutral"]:
            assert regime in result["per_regime"]
            assert result["per_regime"][regime]["n_samples"] > 0
            assert "accuracy" in result["per_regime"][regime]

    def test_evaluate_updates_stats(self, simple_data):
        X, y, regimes = simple_data
        config = MoEConfig(min_samples_per_expert=30, max_iter=50)
        router = MoERouter(config)
        router.fit(X, y, regimes)
        router.evaluate(X, y, regimes)

        for regime in ["bull", "bear", "neutral"]:
            assert router.stats[regime].n_test > 0
            assert router.stats[regime].test_accuracy >= 0


# ---------------------------------------------------------------------------
# MoERouter — fallback logic
# ---------------------------------------------------------------------------

class TestMoERouterFallback:
    def test_fallback_to_configured_regime(self):
        np.random.seed(42)
        X = np.random.randn(100, 5)
        y = (X[:, 0] > 0).astype(int)
        regimes = np.array(["bull"] * 100)

        config = MoEConfig(
            min_samples_per_expert=30,
            max_iter=50,
            fallback_regime="bull",
        )
        router = MoERouter(config)
        router.fit(X, y, regimes)

        expert = router._resolve_expert("nonexistent_regime")
        assert expert is not None

    def test_fallback_to_first_available(self):
        np.random.seed(42)
        X = np.random.randn(100, 5)
        y = (X[:, 0] > 0).astype(int)
        regimes = np.array(["bear"] * 100)

        config = MoEConfig(
            min_samples_per_expert=30,
            max_iter=50,
            fallback_regime="bull",
        )
        router = MoERouter(config)
        router.fit(X, y, regimes)

        expert = router._resolve_expert("nonexistent")
        assert expert is not None

    def test_no_experts_returns_none(self):
        router = MoERouter()
        assert router._resolve_expert("bull") is None


# ---------------------------------------------------------------------------
# Walk-forward training
# ---------------------------------------------------------------------------

class TestWalkForward:
    def test_walk_forward_returns_folds(self):
        np.random.seed(42)
        n = 500
        X = np.random.randn(n, 5)
        y = (X[:, 0] > 0).astype(int)
        regimes = np.random.choice(["bull", "bear"], n)

        config = MoEConfig(min_samples_per_expert=30, max_iter=50)
        results = train_moe_walk_forward(X, y, regimes, n_folds=3, config=config)

        assert len(results) == 3
        for r in results:
            assert "fold" in r
            assert "overall_accuracy" in r
            assert r["n_test"] > 0
            assert 0 <= r["overall_accuracy"] <= 1

    def test_walk_forward_expanding_window(self):
        np.random.seed(42)
        n = 600
        X = np.random.randn(n, 5)
        y = (X[:, 0] > 0).astype(int)
        regimes = np.random.choice(["bull", "bear", "neutral"], n)

        config = MoEConfig(min_samples_per_expert=50, max_iter=50)
        results = train_moe_walk_forward(X, y, regimes, n_folds=4, config=config)

        for i in range(1, len(results)):
            assert results[i]["n_train"] > results[i - 1]["n_train"]


# ---------------------------------------------------------------------------
# LSTM/Transformer MoE integration
# ---------------------------------------------------------------------------

class TestMoEWithLSTMExperts:
    def test_moe_lstm_fit_and_predict(self, simple_data):
        X, y, regimes = simple_data
        config = MoEConfig(
            expert_type="lstm",
            min_samples_per_expert=30,
            max_iter=10,
            seq_len=10,
            hidden_sizes=(32,),
            num_layers=1,
            batch_size=32,
        )
        router = MoERouter(config)
        router.fit(X, y, regimes)
        assert router._fitted
        preds = router.predict(X, regimes)
        assert preds.shape == (len(X),)
        assert set(preds).issubset({0, 1})

    def test_moe_lstm_evaluate(self, simple_data):
        X, y, regimes = simple_data
        config = MoEConfig(
            expert_type="lstm",
            min_samples_per_expert=30,
            max_iter=10,
            seq_len=10,
            hidden_sizes=(32,),
            num_layers=1,
            batch_size=32,
        )
        router = MoERouter(config)
        router.fit(X, y, regimes)
        result = router.evaluate(X, y, regimes)
        assert 0 <= result["overall_accuracy"] <= 1
        assert result["n_regimes"] >= 1


class TestMoEWithTransformerExperts:
    def test_moe_transformer_fit_and_predict(self, simple_data):
        X, y, regimes = simple_data
        config = MoEConfig(
            expert_type="transformer",
            min_samples_per_expert=30,
            max_iter=10,
            seq_len=10,
            d_model=32,
            nhead=4,
            num_layers=1,
            hidden_sizes=(32,),
            batch_size=32,
        )
        router = MoERouter(config)
        router.fit(X, y, regimes)
        assert router._fitted
        preds = router.predict(X, regimes)
        assert preds.shape == (len(X),)

    def test_moe_transformer_walk_forward(self):
        np.random.seed(42)
        n = 400
        X = np.random.randn(n, 8).astype(np.float32)
        y = (X[:, 0] > 0).astype(int)
        regimes = np.random.choice(["bull", "bear"], n)

        config = MoEConfig(
            expert_type="transformer",
            min_samples_per_expert=30,
            max_iter=5,
            seq_len=10,
            d_model=32,
            nhead=4,
            num_layers=1,
            hidden_sizes=(32,),
            batch_size=32,
        )
        results = train_moe_walk_forward(X, y, regimes, n_folds=2, config=config)
        assert len(results) == 2
        for r in results:
            assert 0 <= r["overall_accuracy"] <= 1
