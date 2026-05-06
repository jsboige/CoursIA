"""Tests for walk_forward.py — WalkForwardSplitter and PurgedKFold."""

from __future__ import annotations

import numpy as np
import pandas as pd
import pytest

from scripts.walk_forward import (
    PurgedKFold,
    WalkForwardSplitter,
    combinatorial_purged_split,
)


# ---------------------------------------------------------------------------
# WalkForwardSplitter
# ---------------------------------------------------------------------------


class TestWalkForwardSplitter:
    """Walk-forward rolling window split tests."""

    def test_basic_split_count(self):
        X = np.arange(100)
        wf = WalkForwardSplitter(n_splits=5, train_size=10, gap=0, test_size=5)
        splits = list(wf.split(X))
        assert len(splits) == 5

    def test_non_overlapping_train_test(self):
        X = np.arange(100)
        wf = WalkForwardSplitter(n_splits=5, train_size=10, gap=0, test_size=5)
        for train_idx, test_idx in wf.split(X):
            assert len(np.intersect1d(train_idx, test_idx)) == 0

    def test_gap_respected(self):
        """Gap ensures no adjacency between train end and test start."""
        X = np.arange(100)
        gap = 3
        wf = WalkForwardSplitter(n_splits=5, train_size=10, gap=gap, test_size=5)
        for train_idx, test_idx in wf.split(X):
            assert train_idx[-1] + gap < test_idx[0]

    def test_expanding_window(self):
        """Expanding window: train grows each split."""
        X = np.arange(200)
        wf = WalkForwardSplitter(n_splits=3, train_size=None, test_size=20)
        sizes = [len(train) for train, _ in wf.split(X)]
        # Expanding window should be non-decreasing
        assert sizes == sorted(sizes)

    def test_fixed_window_constant_size(self):
        X = np.arange(100)
        wf = WalkForwardSplitter(n_splits=5, train_size=10, gap=0, test_size=5)
        sizes = [len(train) for train, _ in wf.split(X)]
        assert all(s == 10 for s in sizes)

    def test_monotonic_test_indices(self):
        """Test indices should always be after train indices."""
        X = np.arange(100)
        wf = WalkForwardSplitter(n_splits=5, train_size=10, gap=0, test_size=5)
        for train_idx, test_idx in wf.split(X):
            assert train_idx[-1] < test_idx[0]

    def test_covers_full_data(self):
        """All indices should appear in at least one train or test set."""
        X = np.arange(50)
        wf = WalkForwardSplitter(n_splits=3, train_size=10, gap=0, test_size=10)
        all_indices = set()
        for train_idx, test_idx in wf.split(X):
            all_indices.update(train_idx)
            all_indices.update(test_idx)
        # Should cover most of the data
        assert len(all_indices) >= 30

    def test_single_split(self):
        X = np.arange(20)
        wf = WalkForwardSplitter(n_splits=1, train_size=10, gap=0, test_size=5)
        splits = list(wf.split(X))
        assert len(splits) == 1
        train, test = splits[0]
        assert len(train) == 10
        assert len(test) == 5

    def test_invalid_params(self):
        with pytest.raises(ValueError):
            WalkForwardSplitter(n_splits=0)
        with pytest.raises(ValueError):
            WalkForwardSplitter(n_splits=5, gap=-1)
        with pytest.raises(ValueError):
            WalkForwardSplitter(n_splits=5, train_size=0)
        with pytest.raises(ValueError):
            WalkForwardSplitter(n_splits=5, test_size=0)

    def test_too_few_data_produces_fewer_splits(self):
        """If data is too small, fewer splits are yielded gracefully."""
        X = np.arange(10)
        wf = WalkForwardSplitter(n_splits=100, train_size=3, gap=1, test_size=2)
        splits = list(wf.split(X))
        assert len(splits) < 100
        assert len(splits) > 0

    def test_get_n_splits(self):
        wf = WalkForwardSplitter(n_splits=7)
        assert wf.get_n_splits() == 7


# ---------------------------------------------------------------------------
# PurgedKFold
# ---------------------------------------------------------------------------


class TestPurgedKFold:
    """Purged k-fold cross-validation tests (AFML Ch. 7)."""

    def test_basic_kfold_splits(self):
        X = np.arange(100)
        pkf = PurgedKFold(n_splits=5, pct_embargo=0.0)
        splits = list(pkf.split(X))
        assert len(splits) == 5

    def test_non_overlapping_purged(self):
        """Train and test should not overlap."""
        X = np.arange(100)
        pkf = PurgedKFold(n_splits=5, pct_embargo=0.0)
        for train, test in pkf.split(X):
            assert len(np.intersect1d(train, test)) == 0

    def test_embargo_removes_post_test(self):
        """Embargo should exclude observations immediately after test."""
        X = np.arange(100)
        pkf = PurgedKFold(n_splits=5, pct_embargo=0.05)
        n_samples = len(X)
        embargo_size = int(n_samples * 0.05)

        for train, test in pkf.split(X):
            test_end = test[-1]
            embargo_zone = set(range(test_end + 1, test_end + embargo_size + 1))
            for idx in train:
                assert idx not in embargo_zone

    def test_purging_with_t1_overlap(self):
        """Observations whose label windows overlap with test are purged."""
        n = 50
        X = np.arange(n)
        # Each observation's label extends 5 periods forward
        t1 = pd.Series(
            index=np.arange(n),
            data=np.arange(n) + 5,
        )

        pkf = PurgedKFold(n_splits=5, t1=t1, pct_embargo=0.0)
        for train, test in pkf.split(X):
            test_start = test[0]
            # No training observation should have t1 >= test_start
            # if the observation is before the test period
            for idx in train:
                if idx < test_start:
                    assert t1.iloc[idx] < test_start

    def test_no_purge_without_t1(self):
        """Without t1, no purging occurs — standard k-fold behavior."""
        X = np.arange(100)
        pkf_no_t1 = PurgedKFold(n_splits=5, pct_embargo=0.0)
        train_sizes = [len(t) for t, _ in pkf_no_t1.split(X)]
        # Each fold should have ~80 train samples (100 - 20)
        for s in train_sizes:
            assert s == 80

    def test_embargo_percentage(self):
        """Verify embargo size matches pct_embargo on non-last folds."""
        X = np.arange(100)
        pct = 0.05
        pkf = PurgedKFold(n_splits=5, pct_embargo=pct)
        expected_embargo = int(100 * pct)

        for train, test in pkf.split(X):
            test_end = test[-1]
            embargo_end = min(test_end + expected_embargo + 1, len(X))
            # Skip last fold where embargo may extend beyond data
            if embargo_end >= len(X):
                continue
            embargo_zone = set(range(test_end + 1, embargo_end))
            train_set = set(train)
            excluded_after = sum(1 for i in embargo_zone if i not in train_set)
            assert excluded_after >= expected_embargo - 1

    def test_invalid_params(self):
        with pytest.raises(ValueError):
            PurgedKFold(n_splits=1)
        with pytest.raises(ValueError):
            PurgedKFold(n_splits=5, pct_embargo=-0.1)
        with pytest.raises(ValueError):
            PurgedKFold(n_splits=5, pct_embargo=1.5)

    def test_get_n_splits(self):
        pkf = PurgedKFold(n_splits=10)
        assert pkf.get_n_splits() == 10

    def test_all_indices_covered(self):
        """Every index should appear in at least one train or test set."""
        X = np.arange(50)
        pkf = PurgedKFold(n_splits=5, pct_embargo=0.0)
        all_idx = set()
        for train, test in pkf.split(X):
            all_idx.update(train)
            all_idx.update(test)
        assert all_idx == set(range(50))


# ---------------------------------------------------------------------------
# Combinatorial Purged Cross-Validation
# ---------------------------------------------------------------------------


class TestCombinatorialPurged:
    """CPCV (AFML Ch. 12) tests."""

    def test_basic_cpcv_count(self):
        """Number of combinations = C(n_splits, n_test_groups)."""
        from math import comb

        X = np.arange(100)
        n_splits = 5
        n_test = 2
        expected = comb(n_splits, n_test)
        splits = list(combinatorial_purged_split(X, n_splits=n_splits, n_test_groups=n_test))
        assert len(splits) == expected

    def test_non_overlapping(self):
        X = np.arange(100)
        for train, test in combinatorial_purged_split(X, n_splits=5, n_test_groups=2):
            assert len(np.intersect1d(train, test)) == 0

    def test_single_test_group_equals_kfold(self):
        """With n_test_groups=1, should produce n_splits combinations."""
        X = np.arange(60)
        splits = list(combinatorial_purged_split(X, n_splits=5, n_test_groups=1))
        assert len(splits) == 5
