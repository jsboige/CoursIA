"""Tests for portfolio simulation and production metrics."""

import sys
from pathlib import Path

import numpy as np
import pytest

# Add scripts dir to path for imports
SCRIPT_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from wf_framework.portfolio import (
    simulate_fold,
    simulate_walk_forward,
    SPY_COST_MODEL,
    CRYPTO_COST_MODEL,
    COST_PRESETS,
)
from wf_framework.metrics import (
    compute_sharpe,
    compute_max_drawdown,
    compute_cagr,
    compute_hit_rate,
    compute_volatility,
    compute_portfolio_metrics,
    aggregate_fold_metrics,
    PortfolioMetrics,
)


# --- Portfolio tests ---

class TestSimulateFold:
    def test_perfect_predictions_positive_returns(self):
        y_true = np.array([1, 1, 1, 1, 1])
        y_pred = np.array([1, 1, 1, 1, 1])
        returns = np.array([0.01, 0.01, 0.01, 0.01, 0.01])

        result = simulate_fold(y_true, y_pred, returns=returns, cost_model="spy")
        assert result.n_trades == 1  # entry only
        assert result.final_equity > 100_000  # made money
        assert len(result.equity_curve) == 6  # initial + 5 periods

    def test_wrong_predictions_lose_money(self):
        y_true = np.array([1, 1, 1])
        y_pred = np.array([0, 0, 0])
        returns = np.array([0.01, 0.01, 0.01])

        result = simulate_fold(y_true, y_pred, returns=returns, cost_model="default")
        assert result.final_equity < 100_000

    def test_no_trades_when_flat(self):
        y_pred = np.array([1, 1, 1, 1, 1])
        y_true = np.array([1, 1, 1, 1, 1])
        returns = np.array([0.01, 0.01, 0.01, 0.01, 0.01])

        result = simulate_fold(y_true, y_pred, returns=returns, cost_model="spy")
        assert result.n_trades == 1  # only entry trade

    def test_transaction_costs_reduce_returns(self):
        y_true = np.array([1, 0, 1, 0, 1])
        y_pred = np.array([1, 0, 1, 0, 1])
        returns = np.array([0.01, 0.01, 0.01, 0.01, 0.01])

        result = simulate_fold(y_true, y_pred, returns=returns, cost_model="crypto")
        assert result.total_cost_bps > 0
        assert result.n_trades == 5  # entry + 4 position changes

    def test_crypto_costs_higher_than_spy(self):
        y_true = np.array([1, 0, 1])
        y_pred = np.array([1, 0, 1])
        returns = np.array([0.01, 0.01, 0.01])

        result_spy = simulate_fold(y_true, y_pred, returns=returns, cost_model="spy")
        result_crypto = simulate_fold(y_true, y_pred, returns=returns, cost_model="crypto")
        assert result_crypto.total_cost_bps > result_spy.total_cost_bps

    def test_negative_one_one_encoding(self):
        y_true = np.array([1, 1, -1, -1])
        y_pred = np.array([1, 1, -1, -1])
        returns = np.array([0.01, 0.01, -0.01, -0.01])

        result = simulate_fold(y_true, y_pred, returns=returns, cost_model="spy")
        assert result.final_equity > 100_000  # all correct

    def test_to_dict(self):
        y_true = np.array([1])
        y_pred = np.array([1])
        returns = np.array([0.01])
        result = simulate_fold(y_true, y_pred, returns=returns, cost_model="spy")
        d = result.to_dict()
        assert "n_trades" in d
        assert "total_return" in d


class TestSimulateWalkForward:
    def test_multi_fold(self):
        folds = [
            (np.array([1, 1]), np.array([1, 1])),
            (np.array([0, 0]), np.array([0, 0])),
        ]
        returns_per_fold = [
            np.array([0.01, 0.01]),
            np.array([-0.01, -0.01]),
        ]
        results = simulate_walk_forward(
            folds, returns_per_fold=returns_per_fold, cost_model="spy",
        )
        assert len(results) == 2
        assert results[0].final_equity > 100_000
        assert results[1].final_equity > 100_000  # short in downtrend


# --- Metrics tests ---

class TestSharpe:
    def test_zero_returns(self):
        assert compute_sharpe(np.zeros(100)) == 0.0

    def test_positive_sharpe(self):
        returns = np.random.default_rng(42).normal(0.001, 0.01, 252)
        sharpe = compute_sharpe(returns)
        assert isinstance(sharpe, float)

    def test_constant_returns(self):
        returns = np.full(252, 0.001)
        sharpe = compute_sharpe(returns)
        assert sharpe == 0.0  # std = 0


class TestMaxDrawdown:
    def test_no_drawdown(self):
        equity = np.arange(100, 200, dtype=float)
        dd = compute_max_drawdown(equity)
        assert dd == 0.0

    def test_known_drawdown(self):
        equity = np.array([100, 110, 105, 115, 100, 120])
        dd = compute_max_drawdown(equity)
        # Max DD: from 115 to 100 = -13.04%
        assert -0.15 < dd < -0.10

    def test_single_value(self):
        assert compute_max_drawdown(np.array([100.0])) == 0.0


class TestCAGR:
    def test_doubling_in_one_year(self):
        equity = np.linspace(100, 200, 253)
        cagr = compute_cagr(equity, periods_per_year=252)
        assert abs(cagr - 1.0) < 0.01  # ~100% CAGR

    def test_flat_equity(self):
        equity = np.full(253, 100.0)
        cagr = compute_cagr(equity, periods_per_year=252)
        assert abs(cagr) < 0.001


class TestHitRate:
    def test_all_positive(self):
        assert compute_hit_rate(np.array([0.01, 0.02, 0.03])) == 1.0

    def test_mixed(self):
        hr = compute_hit_rate(np.array([0.01, -0.01, 0.01, -0.01]))
        assert hr == 0.5


class TestVolatility:
    def test_zero_vol(self):
        assert compute_volatility(np.zeros(100)) == 0.0

    def test_annualized(self):
        daily_std = 0.01
        returns = np.full(252, daily_std)  # constant = 0 std
        assert compute_volatility(returns) == 0.0


class TestPortfolioMetrics:
    def test_full_metrics(self):
        net_returns = np.random.default_rng(42).normal(0.001, 0.01, 252)
        metrics = compute_portfolio_metrics(net_returns)

        assert isinstance(metrics, PortfolioMetrics)
        assert isinstance(metrics.sharpe, float)
        assert isinstance(metrics.max_drawdown, float)
        assert isinstance(metrics.cagr, float)
        assert isinstance(metrics.hit_rate, float)
        assert isinstance(metrics.calmar, float)
        assert metrics.n_periods == 252

    def test_with_gross_returns(self):
        rng = np.random.default_rng(42)
        gross = rng.normal(0.002, 0.01, 100)
        costs = np.full(100, 0.0002)
        net = gross - costs
        metrics = compute_portfolio_metrics(net, gross_returns=gross)
        assert metrics.cost_drag_bps > 0

    def test_to_dict(self):
        net = np.array([0.01, 0.01])
        metrics = compute_portfolio_metrics(net)
        d = metrics.to_dict()
        assert "sharpe" in d
        assert "max_drawdown" in d
        assert "cagr" in d


class TestAggregateFoldMetrics:
    def test_empty(self):
        assert aggregate_fold_metrics([]) == {}

    def test_aggregation(self):
        m1 = compute_portfolio_metrics(np.array([0.01, 0.02]))
        m2 = compute_portfolio_metrics(np.array([-0.01, 0.03]))
        agg = aggregate_fold_metrics([m1, m2])
        assert agg["n_folds"] == 2
        assert "mean_sharpe" in agg
        assert "std_sharpe" in agg


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
