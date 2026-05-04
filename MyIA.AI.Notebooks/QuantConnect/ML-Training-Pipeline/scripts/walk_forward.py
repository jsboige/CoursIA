"""
Walk-forward validation and purged k-fold cross-validation for financial ML.

Implements time-series aware splitting strategies that prevent data leakage
from forward-looking features and overlapping training/test windows.

References:
    - Lopez de Prado, "Advances in Financial Machine Learning" (AFML), Chapter 7
    - Hands-On AI Trading with Python, Pik et al., Wiley 2025
"""

from __future__ import annotations

from typing import Iterator

import numpy as np
import pandas as pd
from sklearn.model_selection import BaseCrossValidator


class WalkForwardSplitter(BaseCrossValidator):
    """Rolling walk-forward split for time-series cross-validation.

    Generates non-overlapping train/test pairs that roll forward in time,
    respecting a configurable gap between train and test to prevent
    information leakage from forward-looking features.

    Parameters
    ----------
    n_splits : int
        Number of walk-forward splits to generate.
    train_size : int or None
        Fixed training window size. If None, uses expanding window
        (all data up to test start).
    gap : int
        Number of observations between train end and test start.
        Prevents leakage from autocorrelated features.
    test_size : int or None
        Fixed test window size per split. If None, uses remaining
        data after train + gap.
    """

    def __init__(
        self,
        n_splits: int = 5,
        train_size: int | None = None,
        gap: int = 0,
        test_size: int | None = None,
    ) -> None:
        if n_splits < 1:
            raise ValueError(f"n_splits must be >= 1, got {n_splits}")
        if gap < 0:
            raise ValueError(f"gap must be >= 0, got {gap}")
        if train_size is not None and train_size < 1:
            raise ValueError(f"train_size must be >= 1, got {train_size}")
        if test_size is not None and test_size < 1:
            raise ValueError(f"test_size must be >= 1, got {test_size}")

        self.n_splits = n_splits
        self.train_size = train_size
        self.gap = gap
        self.test_size = test_size

    def split(self, X: pd.DataFrame | np.ndarray, y=None, groups=None) -> Iterator[tuple[np.ndarray, np.ndarray]]:
        """Generate train/test index pairs.

        Parameters
        ----------
        X : array-like of shape (n_samples, ...)
            Training data. Only the length is used for splitting.
        y : ignored
        groups : ignored

        Yields
        ------
        train_indices : np.ndarray
            Training set indices for this split.
        test_indices : np.ndarray
            Test set indices for this split.
        """
        n_samples = len(X)

        # Determine test size per fold
        test_size = self.test_size
        if test_size is None:
            # Divide remaining data evenly
            if self.train_size is not None:
                available = n_samples - self.train_size - self.gap
            else:
                available = n_samples // 2
            test_size = max(1, available // self.n_splits)

        # Calculate the step between each split start
        total_needed = (self.train_size or 0) + self.gap + test_size
        if self.train_size is not None:
            step = max(1, (n_samples - total_needed) // max(1, self.n_splits - 1)) if self.n_splits > 1 else 1
        else:
            step = max(1, (n_samples - test_size) // max(1, self.n_splits))

        splits_yielded = 0
        for i in range(self.n_splits):
            if self.train_size is not None:
                # Fixed-size rolling window
                train_end = self.train_size + i * step
                train_start = i * step
            else:
                # Expanding window
                train_end = min((i + 1) * step, n_samples - test_size)
                train_start = 0

            test_start = train_end + self.gap
            test_end = test_start + test_size

            if test_end > n_samples:
                break
            if train_end <= train_start:
                continue

            train_indices = np.arange(train_start, train_end)
            test_indices = np.arange(test_start, test_end)

            # Verify non-overlap and gap
            assert train_indices[-1] + self.gap < test_indices[0] or self.gap == 0

            splits_yielded += 1
            yield train_indices, test_indices

    def get_n_splits(self, X=None, y=None, groups=None) -> int:
        return self.n_splits


class PurgedKFold(BaseCrossValidator):
    """Purged and embargoed k-fold cross-validation for financial data.

    Implements the purged k-fold from Lopez de Prado (AFML, Chapter 7).
    Prevents information leakage by:
    1. Purging observations from the training set that overlap with
       the test set's label window (t1).
    2. Applying an embargo after each test fold to prevent leakage
       from serially correlated features.

    Parameters
    ----------
    n_splits : int
        Number of folds.
    t1 : pd.Series
        Index = observation index, value = end time of the label window
        for that observation. Observations whose label windows overlap
        with the test fold are purged from training.
    pct_embargo : float
        Fraction of total observations to embargo after each test fold.
        Default 0.01 (1% of data).
    """

    def __init__(
        self,
        n_splits: int = 5,
        t1: pd.Series | None = None,
        pct_embargo: float = 0.01,
    ) -> None:
        if n_splits < 2:
            raise ValueError(f"n_splits must be >= 2 for k-fold, got {n_splits}")
        if pct_embargo < 0 or pct_embargo > 1:
            raise ValueError(f"pct_embargo must be in [0, 1], got {pct_embargo}")

        self.n_splits = n_splits
        self.t1 = t1 if t1 is not None else pd.Series(dtype=float)
        self.pct_embargo = pct_embargo

    def _get_embargo_indices(self, test_indices: np.ndarray, n_samples: int) -> set[int]:
        """Compute embargo zone after test fold."""
        if self.pct_embargo <= 0:
            return set()

        embargo_size = int(n_samples * self.pct_embargo)
        if embargo_size == 0:
            return set()

        last_test = test_indices[-1]
        embargo_end = min(last_test + embargo_size + 1, n_samples)
        return set(range(last_test + 1, embargo_end))

    def _get_purge_indices(self, test_indices: np.ndarray) -> set[int]:
        """Purge training observations whose label windows overlap with test set."""
        if self.t1.empty:
            return set()

        purge = set()
        test_set = set(test_indices)

        # For each test observation, find training observations whose t1
        # overlaps with the test period
        test_start = test_indices[0]
        test_end = test_indices[-1]

        for idx, end_time in self.t1.items():
            if idx in test_set:
                continue
            # If this observation's label window extends into the test period
            if idx < test_start and end_time >= test_start:
                purge.add(idx)
            # If this observation starts within the test period but its index
            # is not in the test set (shouldn't happen but defensive)
            if test_start <= idx <= test_end and idx not in test_set:
                purge.add(idx)

        return purge

    def split(self, X: pd.DataFrame | np.ndarray, y=None, groups=None) -> Iterator[tuple[np.ndarray, np.ndarray]]:
        """Generate purged train/test index pairs.

        Parameters
        ----------
        X : array-like of shape (n_samples, ...)
            Training data.
        y : ignored
        groups : ignored

        Yields
        ------
        train_indices : np.ndarray
            Training set indices (purged + embargoed).
        test_indices : np.ndarray
            Test set indices for this fold.
        """
        n_samples = len(X)
        indices = np.arange(n_samples)
        fold_size = n_samples // self.n_splits

        for i in range(self.n_splits):
            test_start = i * fold_size
            test_end = test_start + fold_size if i < self.n_splits - 1 else n_samples
            test_indices = indices[test_start:test_end]

            # Get exclusion zones
            purge_set = self._get_purge_indices(test_indices)
            embargo_set = self._get_embargo_indices(test_indices, n_samples)
            test_set = set(test_indices)

            excluded = test_set | purge_set | embargo_set
            train_indices = np.array([idx for idx in indices if idx not in excluded])

            if len(train_indices) > 0 and len(test_indices) > 0:
                yield train_indices, test_indices

    def get_n_splits(self, X=None, y=None, groups=None) -> int:
        return self.n_splits


def combinatorial_purged_split(
    X: pd.DataFrame | np.ndarray,
    n_splits: int = 5,
    n_test_groups: int = 1,
    t1: pd.Series | None = None,
    pct_embargo: float = 0.01,
) -> Iterator[tuple[np.ndarray, np.ndarray]]:
    """Combinatorial purged cross-validation (CPCV).

    Generates all combinations of n_test_groups out of n_splits groups
    as test sets, with purging and embargo. Provides more exhaustive
    backtesting than single k-fold.

    Reference: AFML Chapter 12.

    Parameters
    ----------
    X : array-like
        Data to split.
    n_splits : int
        Number of groups to divide data into.
    n_test_groups : int
        Number of groups to use as test set in each combination.
    t1 : pd.Series or None
        Label end times for purging.
    pct_embargo : float
        Embargo fraction.

    Yields
    ------
    train_indices, test_indices : tuple of np.ndarray
    """
    from itertools import combinations

    n_samples = len(X)
    indices = np.arange(n_samples)
    group_size = n_samples // n_splits

    groups = []
    for i in range(n_splits):
        start = i * group_size
        end = start + group_size if i < n_splits - 1 else n_samples
        groups.append(indices[start:end])

    purger = PurgedKFold(n_splits=2, t1=t1, pct_embargo=pct_embargo)

    for test_combo in combinations(range(n_splits), n_test_groups):
        test_indices = np.concatenate([groups[g] for g in test_combo])
        train_groups = [g for g in range(n_splits) if g not in test_combo]
        train_candidates = np.concatenate([groups[g] for g in train_groups])

        # Apply purging and embargo
        purge_set = purger._get_purge_indices(test_indices)
        embargo_set = purger._get_embargo_indices(test_indices, n_samples)
        excluded = set(test_indices) | purge_set | embargo_set

        train_indices = np.array([idx for idx in train_candidates if idx not in excluded])

        if len(train_indices) > 0:
            yield train_indices, test_indices
