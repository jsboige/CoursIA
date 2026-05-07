"""Walk-forward backtesting framework for financial ML validation.

Stage 4 of ML SOTA curriculum — prevents data-snooping bias by standardizing
walk-forward evaluation with multi-seed and multi-asset statistical tests.

Key components:
- WalkForwardBacktest: orchestrates walk-forward evaluation with any strategy
- multi_seed_eval: statistical validation across random seeds (t-test)
- multi_asset_eval: multi-asset validation with Bonferroni correction
"""

from wf_framework.backtest import WalkForwardBacktest
from wf_framework.stats import multi_seed_eval, multi_asset_eval

__all__ = ["WalkForwardBacktest", "multi_seed_eval", "multi_asset_eval"]
