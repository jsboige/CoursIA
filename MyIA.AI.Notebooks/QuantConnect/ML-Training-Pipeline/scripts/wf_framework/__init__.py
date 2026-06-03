"""Walk-forward backtesting framework for financial ML validation.

Stage 4 of ML SOTA curriculum — prevents data-snooping bias by standardizing
walk-forward evaluation with multi-seed and multi-asset statistical tests.

Key components:
- WalkForwardBacktest: orchestrates walk-forward evaluation with any strategy
- multi_seed_eval: statistical validation across random seeds (t-test)
- multi_asset_eval: multi-asset validation with Bonferroni correction
- PortfolioResult: position tracking + P&L with transaction costs
- PortfolioMetrics: production metrics (Sharpe, MaxDD, CAGR, HitRate, Calmar)
"""

from wf_framework.backtest import WalkForwardBacktest
from wf_framework.stats import multi_seed_eval, multi_asset_eval
from wf_framework.portfolio import simulate_fold, PortfolioResult, COST_PRESETS
from wf_framework.metrics import compute_portfolio_metrics, PortfolioMetrics

__all__ = [
    "WalkForwardBacktest", "multi_seed_eval", "multi_asset_eval",
    "simulate_fold", "PortfolioResult", "COST_PRESETS",
    "compute_portfolio_metrics", "PortfolioMetrics",
]
