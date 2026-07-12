"""Tests for train_classification.py -- CPU-only smoke tests."""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from train_classification import save_checkpoint, train_and_evaluate


class TestTrainAndEvaluate:
    def _make_features(self, n=200, n_cols=5):
        cols = {f"f{i}": np.random.randn(n) for i in range(n_cols)}
        cols["target"] = np.random.choice([0, 1], size=n)
        return pd.DataFrame(cols)

    def test_rf_output_keys(self):
        features = self._make_features()
        result = train_and_evaluate(features, model_type="rf", n_estimators=10, max_depth=3)
        assert "model" in result
        assert "metrics" in result
        assert "feature_names" in result

    def test_rf_metrics_range(self):
        features = self._make_features()
        result = train_and_evaluate(features, model_type="rf", n_estimators=10, max_depth=3)
        m = result["metrics"]
        assert 0.0 <= m["accuracy"] <= 1.0
        assert 0.0 <= m["f1"] <= 1.0
        assert m["train_samples"] > 0
        assert m["test_samples"] > 0

    def test_xgb_fallback_to_rf(self):
        features = self._make_features()
        result = train_and_evaluate(features, model_type="xgb", n_estimators=10, max_depth=3)
        assert result["metrics"]["accuracy"] is not None

    def test_test_ratio_respected(self):
        features = self._make_features(n=100)
        result = train_and_evaluate(features, model_type="rf", n_estimators=10, test_ratio=0.3)
        m = result["metrics"]
        total = m["train_samples"] + m["test_samples"]
        assert abs(m["test_samples"] / total - 0.3) < 0.05

    def test_feature_names_excludes_target(self):
        features = self._make_features()
        result = train_and_evaluate(features, model_type="rf", n_estimators=10)
        assert "target" not in result["feature_names"]


class TestSaveCheckpoint:
    def test_creates_files(self, tmp_path):
        from sklearn.ensemble import RandomForestClassifier

        X = np.random.randn(50, 3)
        y = np.random.choice([0, 1], 50)
        model = RandomForestClassifier(n_estimators=5, random_state=42)
        model.fit(X, y)

        metrics = {"accuracy": 0.5}
        hyperparams = {"model_type": "rf", "n_estimators": 5}
        data_hash = "test-hash"

        ckpt_path = save_checkpoint(model, metrics, hyperparams, data_hash, tmp_path)

        assert (ckpt_path / "model.joblib").exists()
        assert (ckpt_path / "metadata.json").exists()

        import json

        meta = json.loads((ckpt_path / "metadata.json").read_text())
        assert meta["model_type"] == "rf"
        assert meta["data_hash"] == "test-hash"

    def test_metadata_fields(self, tmp_path):
        from sklearn.ensemble import RandomForestClassifier

        X = np.random.randn(20, 2)
        y = np.random.choice([0, 1], 20)
        model = RandomForestClassifier(n_estimators=3, random_state=42)
        model.fit(X, y)

        metrics = {"accuracy": 0.6, "f1": 0.55}
        hyperparams = {"model_type": "rf"}

        ckpt_path = save_checkpoint(model, metrics, hyperparams, "hash123", tmp_path)

        import json

        meta = json.loads((ckpt_path / "metadata.json").read_text())
        assert "timestamp" in meta
        assert meta["metrics"]["accuracy"] == 0.6
        assert "model.joblib" in meta["files"]
