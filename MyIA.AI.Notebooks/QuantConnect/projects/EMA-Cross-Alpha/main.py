# region imports
from AlgorithmImports import *
from alpha_models import EMACrossAlpha
from portfolio_construction import MultiStrategyPCM
# endregion


class EMACrossAlphaAlgorithm(QCAlgorithm):

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]
        for ticker in tickers:
            self.add_equity(ticker, Resolution.DAILY)

        self.set_alpha(EMACrossAlpha(tickers, fast_period=20, slow_period=50))

        self.set_portfolio_construction(MultiStrategyPCM(
            alpha_allocations={"EMACross": 1.0},
            rebalance=timedelta(days=1)
        ))

        self.set_risk_management(NullRiskManagementModel())
        self.set_execution(ImmediateExecutionModel())
        self.set_benchmark("SPY")
        self.set_warm_up(60, Resolution.DAILY)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"EMA-Cross-Alpha: Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
