"""Walk-forward backtesting orchestrator.

Wraps WalkForwardSplitter with strategy evaluation, multi-seed support,
and result aggregation. Designed for 300-500 LOC — no over-engineering.
"""

from __future__ import annotations

import json
import logging
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Protocol

import numpy as np
import pandas as pd

from walk_forward import WalkForwardSplitter

log = logging.getLogger(__name__)


class Strategy(Protocol):
    """Minimal interface for a trainable strategy."""

    def fit(self, X_train: np.ndarray, y_train: np.ndarray, seed: int = 42) -> None: ...
    def predict(self, X_test: np.ndarray) -> np.ndarray: ...


@dataclass
class FoldResult:
    """Result from a single walk-forward fold."""
    fold: int
    train_size: int
    test_size: int
    metrics: dict[str, float]
    seed: int = 42


@dataclass
class WalkForwardResult:
    """Aggregated walk-forward results across folds (single seed)."""
    seed: int
    n_folds: int
    fold_results: list[FoldResult] = field(default_factory=list)
    elapsed_s: float = 0.0

    @property
    def mean_metrics(self) -> dict[str, float]:
        if not self.fold_results:
            return {}
        keys = self.fold_results[0].metrics.keys()
        return {
            k: float(np.mean([f.metrics[k] for f in self.fold_results if k in f.metrics]))
            for k in keys
        }

    @property
    def std_metrics(self) -> dict[str, float]:
        if not self.fold_results:
            return {}
        keys = self.fold_results[0].metrics.keys()
        return {
            k: float(np.std([f.metrics[k] for f in self.fold_results if k in f.metrics]))
            for k in keys
        }

    def to_dict(self) -> dict:
        return {
            "seed": self.seed,
            "n_folds": self.n_folds,
            "mean_metrics": self.mean_metrics,
            "std_metrics": self.std_metrics,
            "elapsed_s": round(self.elapsed_s, 2),
            "folds": [
                {"fold": f.fold, "train_size": f.train_size,
                 "test_size": f.test_size, "metrics": f.metrics, "seed": f.seed}
                for f in self.fold_results
            ],
        }


MetricFn = Callable[[np.ndarray, np.ndarray], dict[str, float]]


def default_classification_metrics(y_true: np.ndarray, y_pred: np.ndarray) -> dict[str, float]:
    """Direction accuracy + baseline comparison."""
    acc = float(np.mean(y_true == y_pred))
    majority_class = int(np.mean(y_true) > 0.5)
    majority_acc = float(np.mean(y_true == majority_class))
    return {
        "dir_acc": acc,
        "majority_acc": majority_acc,
        "edge": acc - majority_acc,
    }


def default_regression_metrics(y_true: np.ndarray, y_pred: np.ndarray) -> dict[str, float]:
    """MSE, MAE, directional accuracy for regression targets."""
    mse = float(np.mean((y_true - y_pred) ** 2))
    mae = float(np.mean(np.abs(y_true - y_pred)))
    dir_acc = float(np.mean(np.sign(y_pred) == np.sign(y_true)))
    return {"mse": mse, "mae": mae, "dir_acc": dir_acc}


class WalkForwardBacktest:
    """Orchestrates walk-forward evaluation of a strategy.

    Parameters
    ----------
    strategy_factory : callable
        Factory that returns a new Strategy instance. Called once per fold
        to avoid state leakage. Signature: ``() -> Strategy``.
    X : np.ndarray, shape (N, D)
        Feature matrix.
    y : np.ndarray, shape (N,)
        Target array.
    n_folds : int
        Number of walk-forward folds.
    window_type : str
        "expanding" (default) or "rolling".
    train_size : int or None
        Fixed training window for rolling. None = expanding.
    gap : int
        Observations between train end and test start (leakage prevention).
    metric_fn : callable or None
        Custom metric function. Defaults to classification metrics.
    """

    def __init__(
        self,
        strategy_factory: Callable[[], Strategy],
        X: np.ndarray,
        y: np.ndarray,
        n_folds: int = 5,
        window_type: str = "expanding",
        train_size: int | None = None,
        gap: int = 0,
        metric_fn: MetricFn | None = None,
    ) -> None:
        self.strategy_factory = strategy_factory
        self.X = np.asarray(X, dtype=np.float32)
        self.y = np.asarray(y)
        self.n_folds = n_folds
        self.window_type = window_type
        self.train_size = train_size if window_type == "rolling" else None
        self.gap = gap
        self.metric_fn = metric_fn or default_classification_metrics

    def run(self, seed: int = 42) -> WalkForwardResult:
        """Execute walk-forward backtest for a single seed."""
        splitter = WalkForwardSplitter(
            n_splits=self.n_folds,
            train_size=self.train_size,
            gap=self.gap,
        )

        result = WalkForwardResult(seed=seed, n_folds=0)
        t0 = time.time()

        for fold_idx, (train_idx, test_idx) in enumerate(splitter.split(self.X)):
            X_train, X_test = self.X[train_idx], self.X[test_idx]
            y_train, y_test = self.y[train_idx], self.y[test_idx]

            strategy = self.strategy_factory()
            strategy.fit(X_train, y_train, seed=seed)
            y_pred = strategy.predict(X_test)

            metrics = self.metric_fn(y_test, y_pred)
            result.fold_results.append(FoldResult(
                fold=fold_idx,
                train_size=len(train_idx),
                test_size=len(test_idx),
                metrics=metrics,
                seed=seed,
            ))

        result.n_folds = len(result.fold_results)
        result.elapsed_s = time.time() - t0
        return result

    def run_multi_seed(
        self,
        seeds: list[int] | None = None,
    ) -> list[WalkForwardResult]:
        """Run walk-forward across multiple seeds for statistical validation.

        Default seeds follow the project convention: [0, 1, 7, 42, 99].
        """
        seeds = seeds or [0, 1, 7, 42, 99]
        results = []
        for seed in seeds:
            log.info(f"Walk-forward seed={seed}, folds={self.n_folds}")
            r = self.run(seed=seed)
            results.append(r)
        return results

    def run_multi_asset(
        self,
        assets: dict[str, tuple[np.ndarray, np.ndarray]],
        seeds: list[int] | None = None,
    ) -> dict[str, list[WalkForwardResult]]:
        """Run walk-forward across multiple assets and seeds.

        Parameters
        ----------
        assets : dict mapping symbol -> (X, y) arrays.
        seeds : list of random seeds per asset.

        Returns
        -------
        dict mapping symbol -> list of WalkForwardResult (one per seed).
        """
        all_results = {}
        for symbol, (X_asset, y_asset) in assets.items():
            log.info(f"Multi-asset walk-forward: {symbol}")
            bt = WalkForwardBacktest(
                strategy_factory=self.strategy_factory,
                X=X_asset,
                y=y_asset,
                n_folds=self.n_folds,
                window_type=self.window_type,
                train_size=self.train_size,
                gap=self.gap,
                metric_fn=self.metric_fn,
            )
            all_results[symbol] = bt.run_multi_seed(seeds=seeds)
        return all_results


def save_results(
    results: list[WalkForwardResult] | dict[str, list[WalkForwardResult]],
    path: str | Path,
) -> None:
    """Serialize walk-forward results to JSON."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)

    if isinstance(results, dict):
        data = {
            "type": "multi_asset",
            "assets": {
                sym: [r.to_dict() for r in res_list]
                for sym, res_list in results.items()
            },
        }
    else:
        data = {
            "type": "multi_seed",
            "seeds": [r.to_dict() for r in results],
        }

    path.write_text(json.dumps(data, indent=2, default=str), encoding="utf-8")
    log.info(f"Results saved to {path}")
