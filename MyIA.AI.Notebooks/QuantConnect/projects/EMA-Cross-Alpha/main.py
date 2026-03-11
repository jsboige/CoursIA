# region imports
from AlgorithmImports import *
# endregion

from alpha_models import EMACrossAlpha
from portfolio_construction import MultiStrategyPCM


class EMACrossAlphaAlgorithm(QCAlgorithm):
    """EMA Cross Alpha - Multi-stock EMA crossover with Alpha Model framework.

    Strategy:
    - Universe: 5 tech stocks (AAPL, MSFT, GOOGL, AMZN, NVDA)
    - Signal: EMA fast (20) > EMA slow (50)
    - Equal-weight portfolio of bullish stocks
    - Daily rebalancing

    Alpha Model: EMACrossAlpha generates DirectionInsights
    Portfolio: MultiStrategyPCM with equal weight allocation
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)

        # Universe selection - 5 tech stocks
        tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]
        for ticker in tickers:
            self.add_equity(ticker, Resolution.DAILY)

        self.set_benchmark("SPY")
        self.add_equity("SPY", Resolution.DAILY)

        # Set Alpha Model
        self.set_alpha(EMACrossAlpha(
            fast_period=20,
            slow_period=50,
            resolution=Resolution.DAILY
        ))

        # Set Portfolio Construction - Equal weight among insights
        self.set_portfolio_construction(MultiStrategyPCM())

        # Set Execution - Immediate execution
        self.set_execution(ImmediateExecutionModel())

        # Set Risk - Null for now (no stop-loss in original)
        self.set_risk_management(NullRiskManagementModel())

        # Warmup for slowest EMA
        self.set_warm_up(50, Resolution.DAILY)

    def on_data(self, data):
        """No action needed - Alpha framework handles everything."""
        pass
