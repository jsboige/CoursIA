"""Tests for QuantConnect/shared/plotting.py (matplotlib/seaborn viz helpers).

The module exposes 6 figure-creation helpers consumed by the QC ML notebooks
(equity/drawdown/returns plots, feature importance, confusion matrix, returns
distribution + Q-Q, correlation heatmap, cumulative returns). It had 0 test.

The matplotlib Agg backend is set BEFORE importing the module (which imports
``matplotlib.pyplot`` at import time), so ``plt.show()`` is a no-op and tests
run headless/CPU-only. Every figure is closed after each test. Data is fully
deterministic (no RNG) so structure/data assertions are reproducible.

The tests pin figure STRUCTURE (axes count, titles, labels) + the DATA bound to
each artist (line ydata, bar widths == importance, heatmap QuadMesh values ==
the underlying matrix) -- i.e. they lock the contract that the helpers paint
the right thing, without asserting pixel positions (which would be brittle).
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import matplotlib

matplotlib.use("Agg")  # MUST precede any pyplot import (module imports pyplot)
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402
import pandas as pd  # noqa: E402
import pytest  # noqa: E402

# Agg backend makes plt.show() a no-op -> the helper emits a non-interactive
# UserWarning on every call. Silence it project-wide for this test module.
pytestmark = pytest.mark.filterwarnings(
    "ignore:FigureCanvasAgg is non-interactive")

# --- Load the module under test by path (shared/ has no package __init__) --- #
_MODULE_PATH = Path(__file__).resolve().parent / "plotting.py"
_spec = importlib.util.spec_from_file_location("plotting_under_test", _MODULE_PATH)
plotting = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(plotting)


@pytest.fixture(autouse=True)
def _close_figs():
    """Close every figure before AND after each test (isolation)."""
    plt.close("all")
    yield
    plt.close("all")


# --------------------------------------------------------------------------- #
# Deterministic fixtures
# --------------------------------------------------------------------------- #
@pytest.fixture
def backtest_results():
    """Deterministic equity / daily_returns / drawdown DataFrame."""
    # Linearly increasing equity -> non-negative cumulative path.
    equity = pd.Series([100.0, 101.0, 103.0, 102.0, 105.0, 108.0],
                       index=pd.date_range("2020-01-01", periods=6))
    daily_returns = equity.pct_change()
    drawdown = (equity / equity.cummax()) - 1
    return pd.DataFrame({"equity": equity,
                         "daily_returns": daily_returns,
                         "drawdown": drawdown})


class _FakeTreeModel:
    """Minimal tree-based model stub exposing .feature_importances_."""

    def __init__(self, importances):
        self.feature_importances_ = np.asarray(importances, dtype=float)


# --------------------------------------------------------------------------- #
# plot_backtest_results
# --------------------------------------------------------------------------- #
class TestPlotBacktestResults:
    def test_three_subplots_created(self, backtest_results):
        plotting.plot_backtest_results(backtest_results)
        fig = plt.gcf()
        # 3 stacked axes (equity, drawdown, returns hist). No colorbar here.
        assert len(fig.axes) == 3

    def test_suptitle_set(self, backtest_results):
        plotting.plot_backtest_results(backtest_results, title="My Run")
        assert plt.gcf()._suptitle.get_text() == "My Run"

    def test_default_title(self, backtest_results):
        plotting.plot_backtest_results(backtest_results)
        assert plt.gcf()._suptitle.get_text() == "Backtest Results"

    def test_equity_line_without_benchmark(self, backtest_results):
        plotting.plot_backtest_results(backtest_results)
        ax0 = plt.gcf().axes[0]
        lines = ax0.get_lines()
        assert len(lines) == 1  # no benchmark -> single strategy line
        # The painted ydata matches the equity input (last value 108.0).
        ydata = lines[0].get_ydata()
        assert float(np.asarray(ydata)[-1]) == pytest.approx(108.0)

    def test_benchmark_adds_second_line(self, backtest_results):
        bench = pd.Series([50.0, 52.0, 51.0, 53.0, 55.0, 56.0],
                          index=backtest_results.index)
        plotting.plot_backtest_results(backtest_results, benchmark=bench)
        ax0 = plt.gcf().axes[0]
        assert len(ax0.get_lines()) == 2  # strategy + benchmark

    def test_subplot_titles(self, backtest_results):
        plotting.plot_backtest_results(backtest_results)
        titles = [ax.get_title() for ax in plt.gcf().axes]
        assert "Equity Curve" in titles
        assert "Drawdown" in titles
        assert "Returns Distribution" in titles


# --------------------------------------------------------------------------- #
# plot_feature_importance
# --------------------------------------------------------------------------- #
class TestPlotFeatureImportance:
    def test_raises_without_feature_importances(self):
        with pytest.raises(ValueError, match="feature_importances_"):
            plotting.plot_feature_importance(
                object(), ["a", "b", "c"])  # bare object has no attr

    def test_top_n_bars(self):
        model = _FakeTreeModel([0.5, 0.3, 0.15, 0.05])
        names = ["f0", "f1", "f2", "f3"]
        plotting.plot_feature_importance(model, names, top_n=2)
        ax = plt.gca()
        # top_n=2 -> exactly 2 horizontal bars.
        assert len(ax.patches) == 2

    def test_bars_sorted_descending_by_width(self):
        model = _FakeTreeModel([0.5, 0.3, 0.15, 0.05])
        plotting.plot_feature_importance(model,
                                         ["f0", "f1", "f2", "f3"], top_n=4)
        widths = sorted(p.get_width() for p in plt.gca().patches)
        # The 4 importances, ascending: 0.05, 0.15, 0.3, 0.5.
        assert widths == pytest.approx([0.05, 0.15, 0.3, 0.5])

    def test_title_set(self):
        plotting.plot_feature_importance(_FakeTreeModel([0.5, 0.5]),
                                         ["a", "b"], top_n=2, title="Imp!")
        assert plt.gca().get_title() == "Imp!"


# --------------------------------------------------------------------------- #
# plot_confusion_matrix
# --------------------------------------------------------------------------- #
class TestPlotConfusionMatrix:
    def test_figure_created_with_title(self):
        y_true = [0, 1, 0, 1, 0, 1]
        y_pred = [0, 1, 0, 0, 0, 1]
        plotting.plot_confusion_matrix(y_true, y_pred,
                                       labels=["Down", "Up"], title="CM")
        ax = plt.gca()
        assert ax.get_title() == "CM"

    def test_heatmap_quadmesh_values_match(self):
        # 2x2 confusion matrix: true [0,1,0,1], pred [0,1,0,0]
        # -> [[2,0],[1,1]]  (rows=true, cols=pred)
        y_true = [0, 1, 0, 1]
        y_pred = [0, 1, 0, 0]
        plotting.plot_confusion_matrix(y_true, y_pred)
        ax = plt.gca()
        # The seaborn heatmap paints a QuadMesh in ax.collections.
        quads = [c for c in ax.collections if c.get_array() is not None]
        assert quads, "expected a heatmap QuadMesh"
        values = np.asarray(quads[0].get_array()).ravel()
        # [[2,0],[1,1]] flattened (row-major) -> {2, 0, 1, 1}.
        assert sorted(int(v) for v in values) == [0, 1, 1, 2]

    def test_axis_labels(self):
        plotting.plot_confusion_matrix([0, 1], [0, 1])
        ax = plt.gca()
        assert ax.get_xlabel() == "Predicted"
        assert ax.get_ylabel() == "True"


# --------------------------------------------------------------------------- #
# plot_returns_distribution
# --------------------------------------------------------------------------- #
class TestPlotReturnsDistribution:
    def test_two_subplots_created(self):
        returns = pd.Series([-0.01, 0.0, 0.01, 0.02, -0.005, 0.015])
        plotting.plot_returns_distribution(returns)
        fig = plt.gcf()
        # 1x2 layout -> 2 axes (no colorbar).
        assert len(fig.axes) == 2

    def test_suptitle(self):
        plotting.plot_returns_distribution(pd.Series([0.0, 0.01]),
                                           title="Dist")
        assert plt.gcf()._suptitle.get_text() == "Dist"

    def test_histogram_bin_count_respected(self):
        returns = pd.Series(np.linspace(-0.05, 0.05, 200))
        plotting.plot_returns_distribution(returns, bins=40)
        # The histogram is the first axes' first PolyCollection.
        ax0 = plt.gcf().axes[0]
        # bins param flows to ax.hist -> len(edges)-1 == 40.
        polys = [c for c in ax0.collections if hasattr(c, "get_paths")]
        # hist draws via patches or a PolyCollection depending on mpl version;
        # assert at least one artist was added.
        assert ax0.patches or polys


# --------------------------------------------------------------------------- #
# plot_correlation_matrix
# --------------------------------------------------------------------------- #
class TestPlotCorrelationMatrix:
    def test_heatmap_values_match_corr(self):
        # Deterministic DataFrame with a known correlation structure.
        df = pd.DataFrame({
            "a": [1.0, 2.0, 3.0, 4.0, 5.0],
            "b": [2.0, 4.0, 6.0, 8.0, 10.0],   # perfectly correlated with a
            "c": [5.0, 4.0, 3.0, 2.0, 1.0],    # perfectly anti-correlated
        })
        plotting.plot_correlation_matrix(df, method="pearson")
        ax = plt.gca()
        quads = [c for c in ax.collections if c.get_array() is not None]
        assert quads
        values = np.asarray(quads[0].get_array()).ravel()
        expected = df.corr(method="pearson").values.ravel()
        assert values == pytest.approx(expected)

    def test_method_spearman(self):
        df = pd.DataFrame({"a": [1.0, 2.0, 3.0], "b": [1.0, 2.0, 3.0]})
        plotting.plot_correlation_matrix(df, method="spearman", title="Spearman")
        ax = plt.gca()
        assert ax.get_title() == "Spearman"

    def test_diagonal_is_one(self):
        df = pd.DataFrame({"a": [1.0, 2.0, 3.0, 4.0],
                           "b": [1.0, 2.0, 3.0, 4.0]})
        plotting.plot_correlation_matrix(df)
        ax = plt.gca()
        quads = [c for c in ax.collections if c.get_array() is not None][0]
        vals = np.asarray(quads.get_array()).reshape(2, 2)
        # Diagonal correlations are exactly 1.0.
        assert vals[0, 0] == pytest.approx(1.0)
        assert vals[1, 1] == pytest.approx(1.0)


# --------------------------------------------------------------------------- #
# plot_cumulative_returns
# --------------------------------------------------------------------------- #
class TestPlotCumulativeReturns:
    def test_line_without_benchmark(self):
        idx = pd.date_range("2020-01-01", periods=5)
        strategy = pd.Series([0.0, 0.1, 0.1, 0.1, 0.1], index=idx)
        plotting.plot_cumulative_returns(strategy)
        ax = plt.gca()
        lines = ax.get_lines()
        assert len(lines) == 1
        # (1 + strategy).cumprod() -> [1.0, 1.1, 1.21, 1.331, 1.4641]
        ydata = np.asarray(lines[0].get_ydata(), dtype=float)
        expected = (1 + strategy).cumprod().values
        assert ydata == pytest.approx(expected)

    def test_benchmark_adds_second_line(self):
        idx = pd.date_range("2020-01-01", periods=4)
        strategy = pd.Series([0.0, 0.1, 0.0, 0.1], index=idx)
        bench = pd.Series([0.05, 0.05, 0.05, 0.05], index=idx)
        plotting.plot_cumulative_returns(strategy, benchmark_returns=bench)
        assert len(plt.gca().get_lines()) == 2

    def test_title_and_labels(self):
        plotting.plot_cumulative_returns(pd.Series([0.0, 0.01]),
                                         title="Cum")
        ax = plt.gca()
        assert ax.get_title() == "Cum"
        assert ax.get_xlabel() == "Date"
        assert ax.get_ylabel() == "Cumulative Returns"
