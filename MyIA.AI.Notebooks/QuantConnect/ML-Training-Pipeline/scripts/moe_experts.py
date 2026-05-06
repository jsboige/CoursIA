"""
Mixture-of-Experts (MoE) with regime-aware routing for financial prediction.

Each market regime (bull/bear/neutral/volatile) gets its own expert model.
A router classifies the current regime and delegates prediction to the
corresponding expert. This specialization makes each expert's task simpler
than a single model trying to learn all regimes simultaneously.

Architecture:
    1. Regime detector → label each timestep
    2. Per-regime expert (LSTM/GRU/MLP) trained only on its regime's data
    3. Router dispatches new samples to the appropriate expert
    4. Ensemble combines experts with optional gating

Used by:
    - Issue #754 Phase B: MoE+régimes approach to beat majority baseline
    - Walk-forward training with regime-aware expert specialization
    - eval_moe.py for backtesting regime-conditioned strategies

References:
    - Jacobs et al. (1991), "Adaptive Mixtures of Local Experts"
    - Fedus et al. (2022), "A Review of Sparse Expert Models in Deep Learning"
    - Hands-On AI Trading, Pik et al., Wiley 2025 — regime-aware strategies
"""

from __future__ import annotations

import numpy as np
import pandas as pd
from dataclasses import dataclass, field
from typing import Protocol
import logging

log = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Expert protocol — any model implementing fit/predict
# ---------------------------------------------------------------------------

class ExpertModel(Protocol):
    """Minimal interface for an expert model."""

    def fit(self, X: np.ndarray, y: np.ndarray) -> "ExpertModel": ...

    def predict(self, X: np.ndarray) -> np.ndarray: ...

    def predict_proba(self, X: np.ndarray) -> np.ndarray: ...


@dataclass
class ExpertConfig:
    """Configuration for a single regime expert."""

    regime: str
    model_type: str = "mlp"
    hidden_sizes: tuple[int, ...] = (64, 32)
    max_iter: int = 200
    random_state: int = 42


@dataclass
class MoEConfig:
    """Configuration for the MoE router + experts."""

    regimes: list[str] = field(
        default_factory=lambda: ["bull", "bear", "neutral", "volatile"]
    )
    expert_type: str = "mlp"
    hidden_sizes: tuple[int, ...] = (64, 32)
    max_iter: int = 200
    min_samples_per_expert: int = 50
    fallback_regime: str = "neutral"
    random_state: int = 42
    regime_method: str = "price"


# ---------------------------------------------------------------------------
# Expert factory — create sklearn-compatible models
# ---------------------------------------------------------------------------

def create_expert(config: ExpertConfig) -> ExpertModel:
    """Create an expert model from config.

    Supports: mlp (sklearn MLPClassifier), logistic, rf.
    """
    from sklearn.neural_network import MLPClassifier
    from sklearn.preprocessing import StandardScaler
    from sklearn.pipeline import Pipeline

    model_map = {
        "mlp": lambda: Pipeline([
            ("scaler", StandardScaler()),
            ("clf", MLPClassifier(
                hidden_layer_sizes=config.hidden_sizes,
                max_iter=config.max_iter,
                random_state=config.random_state,
                early_stopping=True,
                validation_fraction=0.15,
            )),
        ]),
    }

    if config.model_type not in model_map:
        raise ValueError(
            f"Unknown model type: {config.model_type}. "
            f"Available: {list(model_map.keys())}"
        )

    return model_map[config.model_type]()


# ---------------------------------------------------------------------------
# MoE Router
# ---------------------------------------------------------------------------

@dataclass
class ExpertStats:
    """Training statistics for a single expert."""

    regime: str
    n_train: int = 0
    n_test: int = 0
    train_accuracy: float = 0.0
    test_accuracy: float = 0.0
    fitted: bool = False


class MoERouter:
    """Mixture-of-Experts with regime-aware routing.

    Workflow:
        1. Call fit() with features, labels, and regime labels
        2. Each regime gets its own expert model trained on regime-filtered data
        3. Call predict() — routes each sample to its regime's expert
        4. Call predict_proba() — same routing with probability outputs

    Parameters
    ----------
    config : MoEConfig
        Router and expert configuration.
    """

    def __init__(self, config: MoEConfig | None = None):
        self.config = config or MoEConfig()
        self._experts: dict[str, ExpertModel] = {}
        self._stats: dict[str, ExpertStats] = {}
        self._regime_names: list[str] = []
        self._fitted = False

    @property
    def regimes(self) -> list[str]:
        """List of regimes with trained experts."""
        return list(self._experts.keys())

    @property
    def stats(self) -> dict[str, ExpertStats]:
        """Per-expert training statistics."""
        return dict(self._stats)

    def _make_expert(self, regime: str) -> ExpertModel:
        cfg = ExpertConfig(
            regime=regime,
            model_type=self.config.expert_type,
            hidden_sizes=self.config.hidden_sizes,
            max_iter=self.config.max_iter,
            random_state=self.config.random_state,
        )
        return create_expert(cfg)

    def fit(
        self,
        X: np.ndarray,
        y: np.ndarray,
        regime_labels: np.ndarray | pd.Series,
    ) -> "MoERouter":
        """Train one expert per regime.

        Parameters
        ----------
        X : np.ndarray, shape (N, D)
            Feature matrix.
        y : np.ndarray, shape (N,)
            Target labels.
        regime_labels : array-like, shape (N,)
            Regime label for each sample.

        Returns
        -------
        self
        """
        regime_labels = np.asarray(regime_labels)
        unique_regimes = np.unique(regime_labels)
        self._regime_names = list(unique_regimes)
        self._experts.clear()
        self._stats.clear()

        for regime in unique_regimes:
            mask = regime_labels == regime
            X_regime = X[mask]
            y_regime = y[mask]
            n_samples = len(X_regime)

            if n_samples < self.config.min_samples_per_expert:
                log.warning(
                    f"Regime '{regime}': only {n_samples} samples "
                    f"(min={self.config.min_samples_per_expert}), skipping"
                )
                self._stats[regime] = ExpertStats(
                    regime=regime, n_train=n_samples, fitted=False
                )
                continue

            expert = self._make_expert(regime)
            try:
                expert.fit(X_regime, y_regime)
                train_acc = float(np.mean(expert.predict(X_regime) == y_regime))
                self._experts[regime] = expert
                self._stats[regime] = ExpertStats(
                    regime=regime,
                    n_train=n_samples,
                    train_accuracy=train_acc,
                    fitted=True,
                )
                log.info(
                    f"Expert '{regime}': trained on {n_samples} samples, "
                    f"train_acc={train_acc:.3f}"
                )
            except Exception as e:
                log.error(f"Expert '{regime}' training failed: {e}")
                self._stats[regime] = ExpertStats(
                    regime=regime, n_train=n_samples, fitted=False
                )

        n_fitted = sum(1 for s in self._stats.values() if s.fitted)
        log.info(
            f"MoE fitted: {n_fitted}/{len(unique_regimes)} experts trained"
        )
        self._fitted = True
        return self

    def _resolve_expert(self, regime: str) -> ExpertModel | None:
        """Get expert for regime, falling back to fallback_regime."""
        if regime in self._experts:
            return self._experts[regime]
        if self.config.fallback_regime in self._experts:
            return self._experts[self.config.fallback_regime]
        if self._experts:
            return next(iter(self._experts.values()))
        return None

    def predict(
        self,
        X: np.ndarray,
        regime_labels: np.ndarray | pd.Series,
    ) -> np.ndarray:
        """Predict using regime-routed experts.

        Parameters
        ----------
        X : np.ndarray, shape (N, D)
            Feature matrix.
        regime_labels : array-like, shape (N,)
            Regime label for each sample.

        Returns
        -------
        np.ndarray of predicted labels, shape (N,).
        """
        regime_labels = np.asarray(regime_labels)
        predictions = np.zeros(len(X), dtype=int)

        for regime in np.unique(regime_labels):
            mask = regime_labels == regime
            expert = self._resolve_expert(regime)
            if expert is not None:
                predictions[mask] = expert.predict(X[mask])
            else:
                predictions[mask] = 0

        return predictions

    def predict_proba(
        self,
        X: np.ndarray,
        regime_labels: np.ndarray | pd.Series,
    ) -> np.ndarray:
        """Predict probabilities using regime-routed experts.

        Parameters
        ----------
        X : np.ndarray, shape (N, D)
            Feature matrix.
        regime_labels : array-like, shape (N,)
            Regime label for each sample.

        Returns
        -------
        np.ndarray of probabilities, shape (N, n_classes).
        """
        regime_labels = np.asarray(regime_labels)
        all_proba = None

        for regime in np.unique(regime_labels):
            mask = regime_labels == regime
            expert = self._resolve_expert(regime)
            if expert is not None:
                proba = expert.predict_proba(X[mask])
            else:
                n_classes = max(2, len(set(int(v) for v in regime_labels)))
                proba = np.ones((mask.sum(), n_classes)) / n_classes

            if all_proba is None:
                all_proba = np.zeros((len(X), proba.shape[1]))
            all_proba[mask] = proba

        return all_proba

    def evaluate(
        self,
        X: np.ndarray,
        y: np.ndarray,
        regime_labels: np.ndarray | pd.Series,
    ) -> dict:
        """Evaluate MoE performance with per-regime breakdown.

        Returns
        -------
        dict with overall + per-regime accuracy, sample counts.
        """
        regime_labels = np.asarray(regime_labels)
        predictions = self.predict(X, regime_labels)
        overall_acc = float(np.mean(predictions == y))

        per_regime = {}
        for regime in np.unique(regime_labels):
            mask = regime_labels == regime
            if mask.sum() > 0:
                regime_acc = float(np.mean(predictions[mask] == y[mask]))
                per_regime[regime] = {
                    "accuracy": regime_acc,
                    "n_samples": int(mask.sum()),
                    "n_correct": int(np.sum(predictions[mask] == y[mask])),
                }
                if regime in self._stats:
                    self._stats[regime].n_test = int(mask.sum())
                    self._stats[regime].test_accuracy = regime_acc

        return {
            "overall_accuracy": overall_acc,
            "n_samples": len(X),
            "n_regimes": len(per_regime),
            "per_regime": per_regime,
            "experts_fitted": sum(1 for s in self._stats.values() if s.fitted),
        }


# ---------------------------------------------------------------------------
# Walk-forward MoE training
# ---------------------------------------------------------------------------

def train_moe_walk_forward(
    features: np.ndarray,
    targets: np.ndarray,
    regime_labels: np.ndarray | pd.Series,
    n_folds: int = 5,
    config: MoEConfig | None = None,
) -> list[dict]:
    """Walk-forward MoE training with expanding window.

    For each fold:
    1. Train experts on expanding window up to fold boundary
    2. Predict on out-of-sample fold period
    3. Record per-regime and overall accuracy

    Parameters
    ----------
    features : np.ndarray, shape (N, D)
        Feature matrix.
    targets : np.ndarray, shape (N,)
        Target labels.
    regime_labels : array-like, shape (N,)
        Regime labels for each sample.
    n_folds : int
        Number of walk-forward folds.
    config : MoEConfig, optional
        MoE configuration. Uses defaults if None.

    Returns
    -------
    list of dicts, one per fold, with train/test indices, accuracy, stats.
    """
    regime_labels = np.asarray(regime_labels)
    n = len(features)
    fold_size = n // (n_folds + 1)
    results = []

    for fold in range(n_folds):
        train_end = fold_size * (fold + 1)
        test_end = min(train_end + fold_size, n)

        if test_end <= train_end:
            break

        X_train, y_train = features[:train_end], targets[:train_end]
        X_test, y_test = features[train_end:test_end], targets[train_end:test_end]
        regime_train = regime_labels[:train_end]
        regime_test = regime_labels[train_end:test_end]

        router = MoERouter(config)
        router.fit(X_train, y_train, regime_train)

        eval_result = router.evaluate(X_test, y_test, regime_test)
        results.append({
            "fold": fold,
            "train_end": train_end,
            "test_end": test_end,
            "n_train": train_end,
            "n_test": test_end - train_end,
            **eval_result,
        })

        log.info(
            f"Fold {fold}: train={train_end}, test={test_end - train_end}, "
            f"acc={eval_result['overall_accuracy']:.3f}"
        )

    return results
