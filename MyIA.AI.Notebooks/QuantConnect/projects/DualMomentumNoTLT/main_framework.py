# region imports
from AlgorithmImports import *
# endregion

from alpha_model import DualMomentumAlpha


class FrameworkDualMomentumNoTLT(QCAlgorithm):
    """Framework version of DualMomentumNoTLT using AlphaModel pattern.

    Uses DualMomentumAlpha for signal generation and
    InsightWeightingPortfolioConstructionModel for position sizing.
    Target: Sharpe within +/-15% of standalone.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)

        tickers = ["SPY", "QQQ", "IEF", "GLD", "XLP"]
        for ticker in tickers:
            self.add_equity(ticker, Resolution.DAILY)

        self.set_alpha(DualMomentumAlpha(
            tickers, lookback=252, num_holdings=2
        ))
        self.set_portfolio_construction(
            InsightWeightingPortfolioConstructionModel()
        )
        self.set_execution(ImmediateExecutionModel())
        self.set_risk_management(NullRiskManagementModel())

        self.set_benchmark("SPY")
        self.set_warm_up(262, Resolution.DAILY)
