# region imports
from AlgorithmImports import *
from alpha_models import EMACrossAlpha, TrendStocksAlpha
from portfolio_construction import MultiStrategyPCM
# endregion


class FrameworkCompositeEMATrend(QCAlgorithm):
    """
    Framework Composite - EMA-Cross + TrendStocks

    Combines EMA-Cross (5 tech/Mag7 stocks, daily rebalance) with TrendStocks
    (15 diversified mega-caps, weekly rebalance) via QC Algorithm Framework.

    Target allocation: EMA70/Trend30 (sweep WINNER; matches QC Cloud project
    28911253 + catalog baseline Sharpe 0.741 @ 2015-2025, docstring claim 0.867).

    Universe overlap: the 5 tech/Mag7 stocks (AAPL, MSFT, GOOGL, AMZN, NVDA)
    are included in both strategies. This is intentional - the MultiStrategyPCM
    additively combines weights, giving Mag7 higher allocation when both
    strategies agree on the direction. Mag7 survivorship caveat: the EMA sleeve
    is 100% Mag7, so a decade dominated by Mag7 outperformance inflates the
    trend signal (see docs/qc/qc-comparative-backtests.md Key-finding #36).

    Reference strategies:
    - EMA-Cross-Alpha: Sharpe 0.980, daily emission
    - TrendStocks-Alpha: Sharpe 0.718, weekly emission

    Design principles:
    - EMA-Cross: Fast mean-reversion on tech/Mag7 stocks (20/50 EMA)
    - TrendStocks: Double-confirmation trend following (Price>SMA200 + EMA20>EMA50)
    - Complementarity: Different timeframes and confirmation logic
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_end_date(2025, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # EMA-Cross universe: 5 tech/Mag7 stocks
        ema_tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]

        # TrendStocks universe: 15 stocks (includes the 5 tech/Mag7)
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

        # Target allocation: EMA70/Trend30 (sweep winner)
        self.set_portfolio_construction(MultiStrategyPCM(
            alpha_allocations={
                "EMACross": 0.70,
                "TrendStocks": 0.30,
            },
            rebalance=timedelta(days=7)  # Weekly rebalance to align with TrendStocks
        ))

        self.set_risk_management(NullRiskManagementModel())
        self.set_execution(ImmediateExecutionModel())
        self.set_benchmark("SPY")
        self.set_warm_up(210, Resolution.DAILY)  # Max(SMA200, EMA50)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FRAMEWORK COMPOSITE (EMA70/Trend30): Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
