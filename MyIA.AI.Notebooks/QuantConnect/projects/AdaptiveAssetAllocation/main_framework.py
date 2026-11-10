# region imports
from AlgorithmImports import *
# endregion

from alpha_model import AdaptiveAssetAllocationAlpha


class FrameworkAdaptiveAssetAllocation(QCAlgorithm):
    """Framework version of AdaptiveAssetAllocation (QC project of config_framework.json).

    AdaptiveAssetAllocationAlpha emits the monthly momentum + minimum-variance
    weights; InsightWeightingPortfolioConstructionModel turns them into targets.
    Same universe, lookbacks, top 4 and brokerage model as the standalone main.py.
    Upload this file as main.py next to alpha_model.py.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        # Explicit account type, as in the standalone version: the weights sum
        # to 1, so the margin account does not lever the portfolio.
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        tickers = [
            "SPY", "EFA", "EEM", "VNQ", "GLD",
            "DBC", "TLT", "IEF", "TIP", "HYG"
        ]
        for ticker in tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            equity.set_data_normalization_mode(DataNormalizationMode.ADJUSTED)

        self.set_alpha(AdaptiveAssetAllocationAlpha(
            tickers, lookback_momentum=126, lookback_vol=60,
            lookback_corr=126, top_n=4, insight_bars=30
        ))
        self.set_portfolio_construction(
            InsightWeightingPortfolioConstructionModel()
        )
        self.set_execution(ImmediateExecutionModel())
        self.set_risk_management(NullRiskManagementModel())

        self.set_benchmark("SPY")
        self.set_warm_up(252, Resolution.DAILY)
