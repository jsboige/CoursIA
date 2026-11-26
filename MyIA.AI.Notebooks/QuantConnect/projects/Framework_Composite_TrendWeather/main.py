# region imports
from AlgorithmImports import *
from alpha_models import TrendStocksAlpha, AllWeatherAlpha
from SharedPCM.pouches_pcm import MultiStrategyPouchesPCM
# endregion


class FrameworkCompositeStrategy(QCAlgorithm):
    """
    Framework Composite v1.5 - Production (T75/AW25, Mom3m)

    Combines TrendStocksLite (momentum-weighted large-caps) with
    AllWeather (SPY/IEF/GLD/XLP) via Algorithm Framework.

    Allocation sweep, measured on QC Cloud on 2026-11-09 (#25533),
    window 2015-01-01 -> 2025-12-31, QC parameter `trend_alloc`:
    T60/AW40: Sharpe 1.120, CAGR 23.4%, MaxDD 24.5%, beta 0.683
    T65/AW35: Sharpe 1.131, CAGR 24.7%, MaxDD 25.6%, beta 0.711
    T70/AW30: Sharpe 1.140, CAGR 25.9%, MaxDD 26.6%, beta 0.740
    T75/AW25: Sharpe 1.148, CAGR 27.1%, MaxDD 27.6%, beta 0.769 <-- default
    T80/AW20: Sharpe 1.156, CAGR 28.4%, MaxDD 28.7%, beta 0.798
    Control, SPY held (same window, broker and starting cash):
              Sharpe 0.537, CAGR 13.4%, MaxDD 33.5%, beta 0.994

    The sweep is monotonic: each 5-point step toward the trend pocket adds
    about 0.009 Sharpe, 1.1 point of MaxDD and 0.029 beta. There is no
    optimum inside the range, so T75 is a risk choice: it is the share at
    which the annual volatility (0.148) matches SPY held (0.147).

    Caveat (#19393): the 15 trend stocks were picked in 2026, so the list
    reads the future. The sweep does not remove that bias, and the verdict
    against SPY held and 60/40 stays NO BEATS.
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

        # Part de la poche tendance (parametre QC, defaut T75/AW25).
        # Le balayage de la docstring fait varier ce seul parametre.
        trend_alloc = float(self.get_parameter("trend_alloc", 0.75))
        aw_alloc = round(1.0 - trend_alloc, 4)
        self.log(f"Allocation : TrendStocks {trend_alloc}, AllWeather {aw_alloc}")

        self.set_portfolio_construction(MultiStrategyPouchesPCM(
            alpha_allocations={
                "TrendStocks": trend_alloc,
                "AllWeather": aw_alloc,
            },
            rebalance=timedelta(days=31),
            additive=True,  # Univers disjoints : identique au mode base
            algorithm=self,
        ))

        self.set_risk_management(NullRiskManagementModel())
        self.set_execution(ImmediateExecutionModel())
        self.set_benchmark("SPY")
        self.set_warm_up(270, Resolution.DAILY)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FRAMEWORK COMPOSITE v1.5: Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
