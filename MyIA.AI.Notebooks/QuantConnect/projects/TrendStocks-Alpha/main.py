# region imports
from AlgorithmImports import *
from alpha_models import TrendStocksAlpha
from portfolio_construction import MultiStrategyPCM
# endregion


class TrendStocksAlphaAlgorithm(QCAlgorithm):

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        tickers = [
            "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA",
            "JPM", "V", "MA",
            "UNH", "JNJ",
            "XOM", "CVX",
            "HD", "PG", "KO"
        ]

        for ticker in tickers:
            self.add_equity(ticker, Resolution.DAILY)

        self.set_alpha(TrendStocksAlpha(tickers, ema_fast=20, ema_slow=50, sma_trend=200))

        self.set_portfolio_construction(MultiStrategyPCM(
            alpha_allocations={"TrendStocks": 1.0},
            rebalance=timedelta(days=7)
        ))

        self.set_risk_management(NullRiskManagementModel())
        self.set_execution(ImmediateExecutionModel())
        self.set_benchmark("SPY")
        self.set_warm_up(210, Resolution.DAILY)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"TrendStocks-Alpha: Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
