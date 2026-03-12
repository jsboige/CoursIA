# region imports
from AlgorithmImports import *
from alpha_models import EMACrossAlpha, TrendStocksAlpha
from portfolio_construction import MultiStrategyPCM
# endregion


class FrameworkCompositeEMATrend(QCAlgorithm):
    """
    Framework Composite - EMA-Cross + TrendStocks

    Combines EMA-Cross (5 tech stocks, daily rebalance) with TrendStocks
    (15 diversified stocks, weekly rebalance) via QC Algorithm Framework.

    Universe overlap: The 5 tech stocks (AAPL, MSFT, GOOGL, AMZN, NVDA)
    are included in both strategies. This is intentional - the MultiStrategyPCM
    will additively combine weights, giving tech stocks higher allocation
    when both strategies agree on the direction.

    Target allocation (starting point): EMA40/Trend60
    Sweep range: EMA30/Trend70 to EMA70/Trend30

    Reference strategies:
    - EMA-Cross-Alpha: Sharpe 0.980, daily emission
    - TrendStocks-Alpha: Sharpe 0.718, weekly emission

    Design principles:
    - EMA-Cross: Fast mean-reversion on tech stocks (20/50 EMA)
    - TrendStocks: Double-confirmation trend following (Price>SMA200 + EMA20>EMA50)
    - Complementarity: Different timeframes and confirmation logic
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # EMA-Cross universe: 5 tech stocks
        ema_tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]

        # TrendStocks universe: 15 stocks (includes the 5 tech)
        trend_tickers = [
            "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA",  # Tech (overlap)
            "JPM", "V", "MA",                            # Financials
            "UNH", "JNJ",                                 # Healthcare
            "XOM", "CVX",                                 # Energy
            "HD", "PG", "KO"                             # Consumer staples
        ]

        # Add all equities
        all_tickers = list(set(ema_tickers + trend_tickers))
        for ticker in all_tickers:
            self.add_equity(ticker, Resolution.DAILY)

        # Create Alpha models
        self.set_alpha(CompositeAlphaModel(
            EMACrossAlpha(ema_tickers, fast_period=20, slow_period=50),
            TrendStocksAlpha(trend_tickers, ema_fast=20, ema_slow=50, sma_trend=200)
        ))

        # Target allocation: EMA40/Trend60 (starting point for sweep)
        self.set_portfolio_construction(MultiStrategyPCM(
            alpha_allocations={
                "EMACross": 0.40,
                "TrendStocks": 0.60,
            },
            rebalance=timedelta(days=7)  # Weekly rebalance to align with TrendStocks
        ))

        self.set_risk_management(NullRiskManagementModel())
        self.set_execution(ImmediateExecutionModel())
        self.set_benchmark("SPY")
        self.set_warm_up(210, Resolution.DAILY)  # Max(SMA200, EMA50)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FRAMEWORK COMPOSITE (EMA40/Trend60): Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
