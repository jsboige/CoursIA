"""Tests for the data-source resolution in overnight_sweep (#16795 voie 1).

Covers the diverse_200k -> HF 200k fallback: a fresh machine without the
gitignored data_cache/diverse_200k.npz must not abort the Phase 1 sweep.
All loaders are monkeypatched -- no disk, no network, no torch execution.
"""

import importlib.util
from pathlib import Path

import numpy as np
import pytest

SWEEP_PATH = Path(__file__).resolve().parents[1] / "sudoku" / "overnight_sweep.py"


@pytest.fixture()
def sweep():
    spec = importlib.util.spec_from_file_location("overnight_sweep_under_test", SWEEP_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


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
