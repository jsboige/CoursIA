"""Tests for the data-source resolution in overnight_sweep (#16795 voie 1).

Covers the diverse_200k -> HF 200k fallback: a fresh machine without the
gitignored data_cache/diverse_200k.npz must not abort the Phase 1 sweep.
All loaders are monkeypatched -- no disk, no network, no torch execution.
"""

import importlib.util
import sys
import types
from pathlib import Path

import numpy as np
import pytest

SWEEP_PATH = Path(__file__).resolve().parents[1] / "sudoku" / "overnight_sweep.py"


@pytest.fixture()
def sweep():
    """Exec overnight_sweep.py in an isolated import context.

    The script imports its sibling package bare (`from core import ...`),
    which collides with scripts/genai-stack/core when another test has
    already imported `core` in the same worker (seen in CI: ImportError
    'cannot import name SudokuRRN from core (genai-stack)'). Purge any
    cached `core`, put scripts/sudoku first on sys.path, and restore both
    sys.path and sys.modules afterwards so the suite stays order-agnostic.
    """
    saved_core = sys.modules.pop("core", None)
    saved_path = sys.path[:]
    sys.path.insert(0, str(SWEEP_PATH.parent))
    try:
        spec = importlib.util.spec_from_file_location("overnight_sweep_under_test", SWEEP_PATH)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod
    finally:
        sys.path[:] = saved_path
        sys.modules.pop("core", None)
        if saved_core is not None:
            sys.modules["core"] = saved_core


def _arr(n=4):
    return np.zeros((n, 81), dtype=np.int64), np.ones((n, 81), dtype=np.int64)


def _no_download(n_total):
    raise AssertionError(f"must not download (n_total={n_total})")


def test_diverse_cache_hit_no_note(sweep, monkeypatch):
    p, s = _arr()
    monkeypatch.setattr(
        sweep, "load_npz",
        lambda name: (p, s) if name == "diverse_200k.npz" else (None, None),
    )
    monkeypatch.setattr(sweep, "load_sudoku_dataset", _no_download)
    out_p, out_s, note = sweep.load_experiment_data("diverse_200k")
    assert out_p is p and out_s is s
    assert note is None


def test_diverse_missing_falls_back_to_hf_200k(sweep, monkeypatch):
    seen = {}

    def fake_hf(n_total):
        seen["n_total"] = n_total
        return _arr()

    monkeypatch.setattr(sweep, "load_npz", lambda name: (None, None))
    monkeypatch.setattr(sweep, "load_sudoku_dataset", fake_hf)
    puzzles, solutions, note = sweep.load_experiment_data("diverse_200k")
    assert seen["n_total"] == 200_000
    assert puzzles.shape == (4, 81)
    assert note is not None and "HF 200k fallback" in note


def test_hf_1m_cache_hit_no_download(sweep, monkeypatch):
    p, s = _arr()
    monkeypatch.setattr(
        sweep, "load_npz",
        lambda name: (p, s) if name == "puzzles_hf_1000000.npz" else (None, None),
    )
    monkeypatch.setattr(sweep, "load_sudoku_dataset", _no_download)
    _, _, note = sweep.load_experiment_data("hf_1m")
    assert note is None


def test_hf_1m_cache_miss_downloads_1m(sweep, monkeypatch):
    seen = {}

    def fake_hf(n_total):
        seen["n_total"] = n_total
        return _arr()

    monkeypatch.setattr(sweep, "load_npz", lambda name: (None, None))
    monkeypatch.setattr(sweep, "load_sudoku_dataset", fake_hf)
    _, _, note = sweep.load_experiment_data("hf_1m")
    assert seen["n_total"] == 1_000_000
    assert note is None


def test_unknown_source_raises(sweep):
    with pytest.raises(ValueError, match="Unknown data source"):
        sweep.load_experiment_data("nope")


def test_import_survives_foreign_core_cached():
    """Regression: a foreign `core` already in sys.modules (e.g. genai-stack's,
    imported by an earlier test in the same worker) must not leak into the
    sweep module's own `from core import ...` (CI run 35502987573). Validates
    the same purge-then-exec recipe the `sweep` fixture applies.
    """
    foreign = types.ModuleType("core")
    foreign.__file__ = "scripts/genai-stack/core/__init__.py"  # deliberately NOT sudoku's
    sys.modules["core"] = foreign
    saved_path = sys.path[:]
    sys.path.insert(0, str(SWEEP_PATH.parent))
    sys.modules.pop("core", None)  # the purge that neutralizes the poison
    try:
        spec = importlib.util.spec_from_file_location("overnight_sweep_poisoned", SWEEP_PATH)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        assert hasattr(mod, "load_experiment_data")
    finally:
        sys.path[:] = saved_path
        sys.modules.pop("core", None)
