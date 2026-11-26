# region imports
from AlgorithmImports import *
# endregion

from alpha_model import SectorMomentumAlpha


class FrameworkMomentumStrategy(QCAlgorithm):
    """Framework version of MomentumStrategy (QC project of config_framework.json).

    SectorMomentumAlpha emits the monthly sector selection and the daily
    stop-loss; InsightWeightingPortfolioConstructionModel turns them into
    targets. Same universe, parameters, warm-up and brokerage model as the
    standalone main.py. Upload this file as main.py next to alpha_model.py.
    Target: Sharpe within +/-15% of the standalone main.py measured on the
    same 2015-2024 window (0.516, README "Variante Framework"). The 0.472 of
    the README history table is the archived v4.0 figure, not this reference.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        # Explicit account type, as in the standalone version: the weights sum
        # to 1, so the margin account does not lever the portfolio.
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        sector_tickers = [
            "XLK", "XLF", "XLE", "XLV", "XLI",
            "XLY", "XLP", "XLU", "XLB", "XLRE", "XLC",
        ]
        for ticker in sector_tickers:
            self.add_equity(ticker, Resolution.DAILY)

        self.add_equity("SPY", Resolution.DAILY)

        self.set_alpha(SectorMomentumAlpha(
            sector_tickers, top_n=4, lookback=252,
            skip_days=21, vol_window=63, stop_loss_pct=-0.10
        ))
        self.set_portfolio_construction(
            InsightWeightingPortfolioConstructionModel()
        )
        self.set_execution(ImmediateExecutionModel())
        self.set_risk_management(NullRiskManagementModel())

        self.set_benchmark("SPY")
        self.set_warm_up(282, Resolution.DAILY)
