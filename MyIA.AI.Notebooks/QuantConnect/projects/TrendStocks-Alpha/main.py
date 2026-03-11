# region imports
from AlgorithmImports import *
# endregion

from alpha_models import TrendStocksAlpha
from portfolio_construction import MultiStrategyPCM


class TrendStocksAlphaAlgorithm(QCAlgorithm):
    """Trend Stocks Lite Alpha - 15 diversified stocks with trend-following.

    Strategy:
    - Universe: 15 stocks across 5 sectors (Tech, Financials, Healthcare, Energy, Consumer)
    - Signal: Price > SMA200 AND EMA20 > EMA50 (double confirmation)
    - Equal-weight portfolio of trending stocks
    - Weekly rebalancing (Mondays)

    Alpha Model: TrendStocksAlpha generates DirectionInsights
    Portfolio: MultiStrategyPCM with equal weight allocation
    """

    def initialize(self):
        self.set_start_date(2020, 1, 1)
        self.set_cash(100000)

        # Universe selection - 15 diversified stocks
        tickers = [
            "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA",  # Tech
            "JPM", "V", "MA",                            # Financials
            "UNH", "JNJ",                                # Healthcare
            "XOM", "CVX",                                # Energy
            "HD", "PG", "KO"                             # Consumer
        ]

        for ticker in tickers:
            self.add_equity(ticker, Resolution.DAILY)

        self.set_benchmark("SPY")
        self.add_equity("SPY", Resolution.DAILY)

        # Set Alpha Model - requires SMA200 confirmation
        self.set_alpha(TrendStocksAlpha(
            ema_fast=20,
            ema_slow=50,
            sma_trend=200,
            resolution=Resolution.DAILY
        ))

        # Set Portfolio Construction
        self.set_portfolio_construction(MultiStrategyPCM())

        # Set Execution
        self.set_execution(ImmediateExecutionModel())

        # Set Risk
        self.set_risk_management(NullRiskManagementModel())

        # Warmup for SMA200
        self.set_warm_up(200, Resolution.DAILY)

    def on_data(self, data):
        """No action needed - Alpha framework handles everything."""
        pass
