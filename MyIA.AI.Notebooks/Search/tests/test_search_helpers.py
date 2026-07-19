"""Tests pour le module ``search_helpers`` (visualisation + benchmarking).

Run with: pytest Search/tests/test_search_helpers.py -v

Pinned bug: ``plot_benchmark`` crashed (TypeError on the matplotlib bar,
ValueError on the ``f'{val:.1f}'`` annotation) when a result dict carried a
non-numeric metric value -- e.g. ``{'algorithm': 'CMA-ES', 'time_ms': None}``
for a timed-out run, or ``'?'`` / ``'N/A'`` for an unknown. The sibling
``benchmark_table`` renders the same values as text without crashing, so the
inconsistency was a real defect on realistic benchmark data. ``plot_benchmark``
now coerces non-numeric values to NaN (matplotlib renders a gap, annotation
reads 'nan') via ``_as_metric_value``.
"""

import io
import math
import sys
import contextlib
from pathlib import Path

import matplotlib

matplotlib.use("Agg")  # headless before pyplot import

import pytest  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import search_helpers as sh  # noqa: E402


# --- _as_metric_value (the coercion helper) ---------------------------------

def test_as_metric_value_numeric():
    assert sh._as_metric_value(10.0) == 10.0
    assert sh._as_metric_value(5) == 5.0
    assert sh._as_metric_value(0) == 0.0


@pytest.mark.parametrize("v", [None, "N/A", "?", "missing", True, False, []])
def test_as_metric_value_non_numeric_is_nan(v):
    out = sh._as_metric_value(v)
    assert math.isnan(out), f"expected NaN for {v!r}, got {out!r}"


# --- Regression pin: the bug this file exists for ---------------------------

def test_plot_benchmark_none_metric_does_not_crash():
    """A timed-out run (time_ms=None) must not crash plot_benchmark.

    Before the fix this raised TypeError (matplotlib bar with None) then
    ValueError (f-string annotation).
    """
    results = [
        {"algorithm": "A", "time_ms": 10.0},
        {"algorithm": "B (timeout)", "time_ms": None},
        {"algorithm": "C", "time_ms": 5.0},
    ]
    fig = sh.plot_benchmark(results, metric="time_ms")
    assert fig is not None


def test_plot_benchmark_string_metric_does_not_crash():
    """A '?' / 'N/A' metric value must not crash the annotation."""
    results = [
        {"algorithm": "A", "time_ms": 10.0},
        {"algorithm": "B", "time_ms": "N/A"},
    ]
    fig = sh.plot_benchmark(results, metric="time_ms")
    assert fig is not None


def test_plot_benchmark_non_numeric_coerced_to_nan_not_zero():
    """Non-numeric metrics must be NaN (gap), not a misleading 0.0 bar."""
    results = [{"algorithm": "A", "time_ms": 10.0}, {"algorithm": "B", "time_ms": None}]
    # Re-derive values the same way plot_benchmark does, to assert the contract.
    values = [sh._as_metric_value(r.get("time_ms", 0)) for r in results]
    assert values[0] == 10.0
    assert math.isnan(values[1])


# --- Normal-path preservation -----------------------------------------------

def test_plot_benchmark_all_numeric_path_preserved():
    results = [
        {"algorithm": "DFS", "time_ms": 12.3},
        {"algorithm": "BFS", "time_ms": 8.1},
        {"algorithm": "A*", "time_ms": 5.5},
    ]
    fig = sh.plot_benchmark(results, metric="time_ms")
    assert fig is not None


def test_plot_benchmark_missing_key_defaults_to_zero():
    """Missing metric key keeps the pre-fix default-0 behavior (not changed)."""
    results = [{"algorithm": "A"}, {"algorithm": "B", "time_ms": 5}]
    values = [sh._as_metric_value(r.get("time_ms", 0)) for r in results]
    assert values == [0.0, 5.0]
    fig = sh.plot_benchmark(results, metric="time_ms")
    assert fig is not None


def test_plot_benchmark_alternate_metric_nodes_expanded():
    results = [
        {"algorithm": "A", "time_ms": 10.0, "nodes_expanded": 42},
        {"algorithm": "B", "time_ms": 5.0, "nodes_expanded": 100},
    ]
    fig = sh.plot_benchmark(results, metric="nodes_expanded")
    assert fig is not None


# --- benchmark_table (sibling, defensive) ------------------------------------

def test_benchmark_table_handles_none_and_missing_fields():
    """benchmark_table must render None/missing fields without crashing."""
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        sh.benchmark_table([
            {"algorithm": "A", "time_ms": None},
            {"algorithm": "B"},  # missing time_ms / nodes / etc.
        ])
    out = buf.getvalue()
    assert "A" in out and "B" in out
    assert "Comparaison" in out


# --- SearchTreeNode + _find_solution_path -----------------------------------

def test_search_tree_node_add_child_accumulates_cost():
    root = sh.SearchTreeNode("root", cost=0)
    child = root.add_child("c1", cost=5)
    grandchild = child.add_child("c2", cost=3)
    assert child.cost == 5
    assert grandchild.cost == 8
    assert child.depth == 1
    assert grandchild.depth == 2


def test_find_solution_path_returns_none_when_no_solution():
    root = sh.SearchTreeNode("r")
    root.add_child("c1")
    assert sh._find_solution_path(root) is None


def test_find_solution_path_returns_chain_to_solution():
    root = sh.SearchTreeNode("r")
    child = root.add_child("c1")
    grand = child.add_child("c2")
    grand.is_solution = True
    path = sh._find_solution_path(root)
    assert path == [root, child, grand]


def test_draw_search_tree_single_node():
    fig = sh.draw_search_tree(sh.SearchTreeNode("only"))
    assert fig is not None
