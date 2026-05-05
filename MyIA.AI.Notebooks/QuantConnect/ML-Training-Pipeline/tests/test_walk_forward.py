"""Tests for walk_forward.py -- walk-forward and purged k-fold validation."""

import sys
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from walk_forward import (
    PurgedKFold,
    WalkForwardSplitter,
    combinatorial_purged_split,
)


class TestWalkForwardSplitter:
    def test_basic_split(self):
        X = np.arange(100)
        splitter = WalkForwardSplitter(n_splits=3, train_size=20, test_size=10, gap=5)
        splits = list(splitter.split(X))
        assert len(splits) >= 1
        for train_idx, test_idx in splits:
            assert len(train_idx) > 0
            assert len(test_idx) == 10

    def test_gap_respected(self):
        X = np.arange(100)
        splitter = WalkForwardSplitter(n_splits=3, train_size=20, test_size=10, gap=5)
        for train_idx, test_idx in splitter.split(X):
            assert train_idx[-1] + 5 < test_idx[0]

    def test_no_overlap(self):
        X = np.arange(100)
        splitter = WalkForwardSplitter(n_splits=5, train_size=20, test_size=10, gap=2)
        for train_idx, test_idx in splitter.split(X):
            assert len(set(train_idx) & set(test_idx)) == 0

    def test_expanding_window(self):
        X = np.arange(100)
        splitter = WalkForwardSplitter(n_splits=3, test_size=10, gap=2)
        splits = list(splitter.split(X))
        assert len(splits) >= 1
        # Each split should have train_start = 0 (expanding)
        for train_idx, test_idx in splits:
            assert train_idx[0] == 0

    def test_get_n_splits(self):
        splitter = WalkForwardSplitter(n_splits=5)
        assert splitter.get_n_splits() == 5

    def test_invalid_params(self):
        with pytest.raises(ValueError):
            WalkForwardSplitter(n_splits=0)
        with pytest.raises(ValueError):
            WalkForwardSplitter(gap=-1)
        with pytest.raises(ValueError):
            WalkForwardSplitter(train_size=0)

    def test_with_dataframe(self):
        df = pd.DataFrame({"a": np.arange(50), "b": np.random.randn(50)})
        splitter = WalkForwardSplitter(n_splits=2, train_size=15, test_size=5, gap=3)
        splits = list(splitter.split(df))
        assert len(splits) >= 1


class TestPurgedKFold:
    def test_basic_split(self):
        X = np.arange(100)
        splitter = PurgedKFold(n_splits=5)
        splits = list(splitter.split(X))
        assert len(splits) == 5
        for train_idx, test_idx in splits:
            assert len(train_idx) > 0
            assert len(test_idx) > 0

    def test_no_overlap(self):
        X = np.arange(100)
        splitter = PurgedKFold(n_splits=5)
        for train_idx, test_idx in splitter.split(X):
            assert len(set(train_idx) & set(test_idx)) == 0

    def test_all_indices_covered(self):
        X = np.arange(100)
        splitter = PurgedKFold(n_splits=5)
        all_test = set()
        all_train = set()
        for train_idx, test_idx in splitter.split(X):
            all_test.update(test_idx)
            all_train.update(train_idx)
        assert all_test == set(range(100))

    def test_embargo(self):
        X = np.arange(100)
        splitter = PurgedKFold(n_splits=5, pct_embargo=0.05)
        for train_idx, test_idx in splitter.split(X):
            assert len(set(train_idx) & set(test_idx)) == 0

    def test_invalid_n_splits(self):
        with pytest.raises(ValueError):
            PurgedKFold(n_splits=1)

    def test_get_n_splits(self):
        splitter = PurgedKFold(n_splits=5)
        assert splitter.get_n_splits() == 5


class TestCombinatorialPurgedSplit:
    def test_basic(self):
        X = np.arange(100)
        splits = list(combinatorial_purged_split(X, n_splits=5, n_test_groups=1))
        assert len(splits) == 5

    def test_no_overlap(self):
        X = np.arange(100)
        for train_idx, test_idx in combinatorial_purged_split(X, n_splits=5, n_test_groups=1):
            assert len(set(train_idx) & set(test_idx)) == 0

    def test_with_embargo(self):
        X = np.arange(100)
        splits = list(combinatorial_purged_split(X, n_splits=5, n_test_groups=2, pct_embargo=0.02))
        assert len(splits) > 0
