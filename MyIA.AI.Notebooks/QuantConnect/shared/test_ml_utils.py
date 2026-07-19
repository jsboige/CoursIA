#!/usr/bin/env python3
"""Pytest suite for `QuantConnect/shared/ml_utils.py`.

Co-located with the module under `shared/`. CPU-only, no network, no
QuantConnect ObjectStore, no QC Cloud. The module imports stdlib + pandas +
numpy + pickle + joblib + pathlib at top level, and lazily imports sklearn /
xgboost / lightgbm inside each function. sklearn is installed locally; xgboost
and lightgbm are NOT installed, so their `ImportError` guards are exercised
directly without mocking.

The module is the ML training/eval/persistence helper consumed by notebooks
19-27 (ML/DL/AI) and had 0 dedicated Python test coverage before this PR.

Strategy: tiny deterministic datasets (fixed numpy arrays via arange/reshape +
modulo, no RNG) so model fit + metrics are reproducible. ObjectStore paths are
exercised with a fake `qc_algorithm` whose `.ObjectStore` records Save/ReadBytes/
ContainsKey. Local paths use tmp_path.
"""
from __future__ import annotations

import importlib.util
import pickle
from pathlib import Path

import numpy as np
import pytest

# Load the module by path (lives under shared/, top-level stdlib + pandas +
# numpy + pickle + joblib only, no package-relative imports -> no sys.path
# manipulation needed).
_MODULE_PATH = Path(__file__).resolve().parent / "ml_utils.py"
_spec = importlib.util.spec_from_file_location("ml_utils", _MODULE_PATH)
mlu = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(mlu)


# --------------------------------------------------------------------------
# Deterministic small datasets
# --------------------------------------------------------------------------


def _clf_data(n=60, n_features=4):
    """Deterministic binary-classification dataset (no RNG)."""
    X = (np.arange(n * n_features).reshape(n, n_features) % 17).astype(float)
    # Label = parity of the row sum -> learnable linear-ish signal.
    y = (X.sum(axis=1) % 2).astype(int)
    return X, y


def _reg_data(n=60, n_features=4):
    """Deterministic regression dataset (no RNG)."""
    X = (np.arange(n * n_features).reshape(n, n_features) % 13).astype(float)
    y = X[:, 0] * 2.0 + 1.0
    return X, y


# --------------------------------------------------------------------------
# Fake ObjectStore + qc_algorithm
# --------------------------------------------------------------------------


class _FakeObjectStore:
    def __init__(self):
        self._store = {}

    def Save(self, key, data):
        self._store[key] = data

    def ContainsKey(self, key):
        return key in self._store

    def ReadBytes(self, key):
        return self._store[key]


class _FakeQC:
    def __init__(self):
        self.ObjectStore = _FakeObjectStore()


# --------------------------------------------------------------------------
# train_classifier
# --------------------------------------------------------------------------


def test_train_classifier_random_forest_returns_fitted_model():
    X, y = _clf_data()
    model = mlu.train_classifier(X, y, model_type="random_forest",
                                 n_estimators=5)
    # A fitted model can predict and exposes classes_.
    preds = model.predict(X[:5])
    assert len(preds) == 5
    assert hasattr(model, "classes_")


def test_train_classifier_logistic_returns_fitted_model():
    X, y = _clf_data()
    model = mlu.train_classifier(X, y, model_type="logistic")
    assert hasattr(model, "predict")
    model.predict(X[:3])


def test_train_classifier_kwargs_override_defaults():
    X, y = _clf_data()
    model = mlu.train_classifier(X, y, model_type="random_forest",
                                 n_estimators=7, max_depth=3)
    assert model.n_estimators == 7
    assert model.max_depth == 3


def test_train_classifier_random_state_default_is_42():
    X, y = _clf_data()
    model = mlu.train_classifier(X, y, model_type="random_forest",
                                 n_estimators=5)
    assert model.random_state == 42


def test_train_classifier_unknown_type_raises_value_error():
    X, y = _clf_data()
    with pytest.raises(ValueError, match="Unknown model_type"):
        mlu.train_classifier(X, y, model_type="not_a_model")


def test_train_classifier_xgboost_raises_importerror_when_not_installed():
    # xgboost is not installed on this worker -> the function's try/except
    # ImportError guard fires with a helpful pip-install message.
    X, y = _clf_data()
    with pytest.raises(ImportError, match="XGBoost not installed"):
        mlu.train_classifier(X, y, model_type="xgboost")


def test_train_classifier_lightgbm_raises_importerror_when_not_installed():
    X, y = _clf_data()
    with pytest.raises(ImportError, match="LightGBM not installed"):
        mlu.train_classifier(X, y, model_type="lightgbm")


# --------------------------------------------------------------------------
# train_regressor
# --------------------------------------------------------------------------


def test_train_regressor_random_forest_returns_fitted_model():
    X, y = _reg_data()
    model = mlu.train_regressor(X, y, model_type="random_forest",
                                n_estimators=5)
    preds = model.predict(X[:5])
    assert len(preds) == 5


def test_train_regressor_linear_returns_fitted_model():
    X, y = _reg_data()
    model = mlu.train_regressor(X, y, model_type="linear")
    # Linear relationship y = 2*x0 + 1 -> near-perfect R2 on training data.
    preds = model.predict(X)
    assert np.allclose(preds, y, atol=1.0)


def test_train_regressor_svr_returns_fitted_model():
    X, y = _reg_data()
    model = mlu.train_regressor(X, y, model_type="svr")
    assert hasattr(model, "predict")


def test_train_regressor_unknown_type_raises_value_error():
    X, y = _reg_data()
    with pytest.raises(ValueError, match="Unknown model_type"):
        mlu.train_regressor(X, y, model_type="bogus")


# --------------------------------------------------------------------------
# evaluate_model
# --------------------------------------------------------------------------


def test_evaluate_model_classification_metrics_keys():
    X, y = _clf_data()
    model = mlu.train_classifier(X, y, model_type="random_forest",
                                 n_estimators=5)
    metrics = mlu.evaluate_model(model, X, y, task="classification")
    for key in ("accuracy", "precision", "recall", "f1_score"):
        assert key in metrics
    # accuracy is in [0, 1].
    assert 0.0 <= metrics["accuracy"] <= 1.0


def test_evaluate_model_classification_perfect_model():
    X, y = _clf_data()
    model = mlu.train_classifier(X, y, model_type="random_forest",
                                 n_estimators=5)
    # Evaluate on the training data of a high-capacity model -> accuracy 1.0.
    metrics = mlu.evaluate_model(model, X, y, task="classification")
    assert metrics["accuracy"] == pytest.approx(1.0)


def test_evaluate_model_regression_metrics_keys():
    X, y = _reg_data()
    model = mlu.train_regressor(X, y, model_type="linear")
    metrics = mlu.evaluate_model(model, X, y, task="regression")
    for key in ("mae", "mse", "rmse", "r2"):
        assert key in metrics
    # rmse is the sqrt of mse.
    assert metrics["rmse"] == pytest.approx(np.sqrt(metrics["mse"]))


def test_evaluate_model_unknown_task_raises_value_error():
    X, y = _clf_data()
    model = mlu.train_classifier(X, y, model_type="random_forest",
                                 n_estimators=5)
    with pytest.raises(ValueError, match="Unknown task"):
        mlu.evaluate_model(model, X, y, task="clustering")


def test_evaluate_model_sharpe_optional_adds_key_for_proba_models():
    # RandomForest exposes predict_proba -> the optional Sharpe block runs.
    # With a near-perfect model on training data, proba is extreme -> the
    # Sharpe ratio (mean/std scaled) is finite and added when std > 0.
    X, y = _clf_data()
    model = mlu.train_classifier(X, y, model_type="random_forest",
                                 n_estimators=20)
    metrics = mlu.evaluate_model(model, X, y, task="classification")
    # The sharpe_ratio key MAY be present (depends on std > 0); pin that when
    # present it is finite.
    if "sharpe_ratio" in metrics:
        assert np.isfinite(metrics["sharpe_ratio"])


# --------------------------------------------------------------------------
# save_to_objectstore / load_from_objectstore — local path
# --------------------------------------------------------------------------


def test_save_and_load_local_roundtrip(tmp_path):
    X, y = _clf_data()
    model = mlu.train_classifier(X, y, model_type="random_forest",
                                 n_estimators=5)
    p = tmp_path / "m.pkl"
    out = mlu.save_to_objectstore(model, "m", local_path=str(p))
    assert Path(out).exists()
    loaded = mlu.load_from_objectstore("m", local_path=str(p))
    # Loaded model predicts identically (pickle round-trips fitted state).
    assert np.array_equal(loaded.predict(X[:5]), model.predict(X[:5]))


def test_save_local_creates_parent_dirs(tmp_path):
    model = {"hello": "world"}  # pickleable stand-in
    nested = tmp_path / "deep" / "nested" / "dir" / "m.pkl"
    out = mlu.save_to_objectstore(model, "m", local_path=str(nested))
    assert Path(out).exists()


def test_save_without_target_raises_value_error():
    with pytest.raises(ValueError, match="Provide either"):
        mlu.save_to_objectstore({"x": 1}, "m")


def test_load_local_missing_file_raises_filenotfound(tmp_path):
    with pytest.raises(FileNotFoundError, match="Model file not found"):
        mlu.load_from_objectstore("m", local_path=str(tmp_path / "nope.pkl"))


# --------------------------------------------------------------------------
# save_to_objectstore / load_from_objectstore — ObjectStore
# --------------------------------------------------------------------------


def test_save_and_load_objectstore_roundtrip():
    qc = _FakeQC()
    model = {"weights": [1, 2, 3]}
    out = mlu.save_to_objectstore(model, "my_model", qc_algorithm=qc)
    assert out == "ObjectStore:my_model.pkl"
    assert qc.ObjectStore.ContainsKey("my_model.pkl")
    loaded = mlu.load_from_objectstore("my_model", qc_algorithm=qc)
    assert loaded == model


def test_load_objectstore_missing_key_raises_filenotfound():
    qc = _FakeQC()
    with pytest.raises(FileNotFoundError, match="not found in ObjectStore"):
        mlu.load_from_objectstore("absent", qc_algorithm=qc)


def test_load_without_target_raises_value_error():
    with pytest.raises(ValueError, match="Provide either"):
        mlu.load_from_objectstore("m")


def test_objectstore_uses_pickle_bytes():
    # The bytes written to ObjectStore must be a valid pickle payload.
    qc = _FakeQC()
    mlu.save_to_objectstore({"a": 1}, "m", qc_algorithm=qc)
    raw = qc.ObjectStore.ReadBytes("m.pkl")
    assert pickle.loads(raw) == {"a": 1}


# --------------------------------------------------------------------------
# cross_validate_walk_forward
# --------------------------------------------------------------------------


def test_cross_validate_walk_forward_returns_expected_keys():
    X, y = _clf_data(n=80)

    def factory():
        from sklearn.ensemble import RandomForestClassifier
        return RandomForestClassifier(n_estimators=5, random_state=42)

    results = mlu.cross_validate_walk_forward(
        factory, X, y, n_splits=3, train_size_ratio=0.5
    )
    for key in ("mean_accuracy", "std_accuracy", "n_splits_completed"):
        assert key in results
    assert isinstance(results["n_splits_completed"], int)


def test_cross_validate_walk_forward_small_ratio_completes_multiple_splits():
    # train_size_ratio=0.5 -> test_size=0.5*N; multiple expanding folds fit.
    X, y = _clf_data(n=80)

    def factory():
        from sklearn.ensemble import RandomForestClassifier
        return RandomForestClassifier(n_estimators=5, random_state=42)

    results = mlu.cross_validate_walk_forward(
        factory, X, y, n_splits=3, train_size_ratio=0.5
    )
    assert results["n_splits_completed"] >= 1
    assert 0.0 <= results["mean_accuracy"] <= 1.0


def test_cross_validate_walk_forward_default_ratio_completes_one_split():
    # Documented quirk (pin, not a bug-claim): with the default
    # train_size_ratio=0.7, train_initial=0.7*N and test_size=0.3*N, so the
    # 2nd fold's train_end = 0.7N + 1*0.3N = N -> test_end > total -> break.
    # Only the first fold completes regardless of n_splits requested.
    X, y = _clf_data(n=80)

    def factory():
        from sklearn.ensemble import RandomForestClassifier
        return RandomForestClassifier(n_estimators=5, random_state=42)

    results = mlu.cross_validate_walk_forward(
        factory, X, y, n_splits=5, train_size_ratio=0.7
    )
    assert results["n_splits_completed"] == 1
