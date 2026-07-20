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


# --- draw_search_tree degenerate-input guard (c.703) -----------------------

class TestDrawSearchTreeDegenerateInputGuard:
    """Garde-fou d'entree pour ``draw_search_tree``.

    Reproduit le pattern robusteur c.702 sur ``wfc_cpsat.run_all`` /
    ``wfc_cpsat.adjacency_violations`` : refuser explicitement les
    arguments degeneres plutot que de laisser une ``AttributeError``
    opaque (``root=None`` -> ``'NoneType' object has no attribute
    'children'``) ou un rendu matplotlib pathologique (``max_depth<=0``
    -> y=1.0 partout, aretes confondues avec la legende).
    """

    def test_root_none_raises_typeerror(self):
        # L'AttributeError d'origine etait silencieuse et confondait
        # l'appelant avec un bug dans son arbre -- on la remplace par
        # un TypeError explicite qui pointe la cause reelle.
        with pytest.raises(TypeError, match="root must be a SearchTreeNode"):
            sh.draw_search_tree(None)

    def test_root_non_node_raises_typeerror(self):
        # Tout objet qui n'est pas un SearchTreeNode est rejete avec
        # le meme message -- la verification se fait sur le type, pas
        # sur la verite/falsete (un SearchTreeNode est toujours truthy
        # en pratique, mais on ne veut pas dependre de __bool__).
        with pytest.raises(TypeError, match="got str"):
            sh.draw_search_tree("not_a_node")

    def test_root_dict_raises_typeerror(self):
        with pytest.raises(TypeError, match="got dict"):
            sh.draw_search_tree({"state": "A"})

    def test_max_depth_zero_raises_valueerror(self):
        # max_depth=0 -> toutes les positions y=1.0, aretes illisibles.
        with pytest.raises(ValueError, match="max_depth must be a strictly positive"):
            sh.draw_search_tree(sh.SearchTreeNode("root"), max_depth=0)

    def test_max_depth_negative_raises_valueerror(self):
        with pytest.raises(ValueError, match="max_depth must be a strictly positive"):
            sh.draw_search_tree(sh.SearchTreeNode("root"), max_depth=-5)

    def test_max_depth_non_int_raises_valueerror(self):
        # 1.5 est un float valide ; on exige un int strict.
        with pytest.raises(ValueError, match="max_depth must be a strictly positive"):
            sh.draw_search_tree(sh.SearchTreeNode("root"), max_depth=1.5)

    def test_max_depth_one_still_renders(self):
        # Sanity check : l'invariant "max_depth>=1 OK" doit etre preserve.
        fig = sh.draw_search_tree(sh.SearchTreeNode("root"), max_depth=1)
        assert fig is not None

    def test_valid_root_unaffected(self):
        # Pas de regression sur l'appel normal (defaut max_depth=5).
        root = sh.SearchTreeNode("root")
        root.add_child("a")
        root.add_child("b")
        fig = sh.draw_search_tree(root)
        assert fig is not None
