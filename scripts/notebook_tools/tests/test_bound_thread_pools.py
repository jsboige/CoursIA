"""Tests for bound_native_thread_pools (#11111) — OpenMP/BLAS bounding.

The function mutates os.environ; every test cleans up the three variables
so a pre-set machine value or a previous test never leaks across cases.
"""

import os
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from notebook_helpers import (
    NATIVE_THREAD_POOL_VARS,
    bound_native_thread_pools,
)


@pytest.fixture(autouse=True)
def _clean_thread_env(monkeypatch):
    """Remove the three vars before each test, restore after."""
    for var in NATIVE_THREAD_POOL_VARS:
        monkeypatch.delenv(var, raising=False)
    yield


class TestBoundNativeThreadPools:
    def test_sets_all_three_vars_when_absent(self):
        set_vars = bound_native_thread_pools()
        for var in NATIVE_THREAD_POOL_VARS:
            assert os.environ[var] == "4"
            assert set_vars[var] == "4"

    def test_custom_default(self):
        bound_native_thread_pools(default=8)
        assert os.environ["OMP_NUM_THREADS"] == "8"

    def test_preset_value_wins(self):
        os.environ["OMP_NUM_THREADS"] = "32"
        set_vars = bound_native_thread_pools()
        assert os.environ["OMP_NUM_THREADS"] == "32"
        assert "OMP_NUM_THREADS" not in set_vars

    def test_returns_only_what_it_set(self):
        os.environ["OPENBLAS_NUM_THREADS"] = "2"
        set_vars = bound_native_thread_pools()
        assert set_vars == {"OMP_NUM_THREADS": "4", "MKL_NUM_THREADS": "4"}

    def test_idempotent(self):
        first = bound_native_thread_pools()
        second = bound_native_thread_pools()
        assert first == {"OMP_NUM_THREADS": "4", "OPENBLAS_NUM_THREADS": "4",
                         "MKL_NUM_THREADS": "4"}
        assert second == {}
