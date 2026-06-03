# region imports
from AlgorithmImports import *
from alpha_models import TrendStocksAlpha, AllWeatherAlpha
from portfolio_construction import MultiStrategyPCM
# endregion


class FrameworkCompositeStrategy(QCAlgorithm):
    """
    Framework Composite v1.5 - Production (T75/AW25, Mom3m)

    Combines TrendStocksLite (momentum-weighted large-caps) with
    AllWeather (SPY/IEF/GLD/XLP) via Algorithm Framework.

    Allocation sweep results (2015-2026):
    v1.3 (T60/AW40): Sharpe 1.130, CAGR 23.8%, MaxDD 24.5%
    v1.4b (T65/AW35): Sharpe 1.141, CAGR 25.0%, MaxDD 25.6%
    v1.4c (T70/AW30): Sharpe 1.149, CAGR 26.2%, MaxDD 26.6%
    v1.4d (T75/AW25): Sharpe 1.155, CAGR 27.4%, MaxDD 27.7% <-- selected
    v1.4e (T80/AW20): Sharpe 1.163, CAGR 28.7%, MaxDD 28.7%

    T75/AW25 chosen as production: best risk/return balance before
    beta exceeds 0.80 and MaxDD approaches 29%.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2025, 12, 31)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        trend_tickers = [
            "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA",
            "JPM", "V", "MA",
            "UNH", "JNJ",
            "XOM", "CVX",
            "HD", "PG", "KO"
        ]
        aw_tickers = ["SPY", "IEF", "GLD", "XLP"]

        all_tickers = list(set(trend_tickers + aw_tickers))
        for ticker in all_tickers:
            self.add_equity(ticker, Resolution.DAILY)

        self.set_alpha(CompositeAlphaModel(
            TrendStocksAlpha(trend_tickers),
            AllWeatherAlpha(aw_tickers)
        ))

        self.set_portfolio_construction(MultiStrategyPCM(
            alpha_allocations={
                "TrendStocks": 0.75,
                "AllWeather": 0.25,
            },
            rebalance=timedelta(days=31)
        ))

        self.set_risk_management(NullRiskManagementModel())
        self.set_execution(ImmediateExecutionModel())
        self.set_benchmark("SPY")
        self.set_warm_up(270, Resolution.DAILY)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FRAMEWORK COMPOSITE v1.5: Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
