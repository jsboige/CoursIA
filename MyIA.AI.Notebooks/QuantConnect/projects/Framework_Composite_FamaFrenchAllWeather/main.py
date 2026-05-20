# region imports
from AlgorithmImports import *
from alpha_models import FamaFrenchAlpha, AllWeatherAlpha
from portfolio_construction import MultiStrategyPCM
# endregion


class FrameworkCompositeFamaFrenchAllWeather(QCAlgorithm):
    """
    Framework Composite - FamaFrench Factor Rotation + AllWeather

    Combines Fama-French factor ETF rotation (VLUE, MTUM, SIZE, QUAL, USMV)
    with AllWeather static allocation (SPY, IEF, GLD, XLP) via QC Algorithm Framework.

    Target allocation: FF20/AW80 (FamaFrench 20%, AllWeather 80%)
    Sweep result: Sharpe 0.588, CAGR 9.9%, MaxDD 17.1%

    Key design principle from lesson learned in MomentumRegime:
    - NO overlap between universes (factor ETFs vs traditional assets)
    - True diversification: equity factors + macro allocation
    - FamaFrench uses risk-adjusted momentum only (NO SMA200 filter - AllWeather handles defense)

    Reference strategies:
    - FamaFrench v3.0: Sharpe 0.540, CAGR 12.1%, MaxDD 24.2%
    - AllWeather: Ray Dalio-inspired static allocation

    Quarterly rebalancing for FamaFrench (factor rotation), monthly for AllWeather.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2025, 12, 31)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # FamaFrench universe: factor ETFs (iShares)
        ff_tickers = ["VLUE", "MTUM", "SIZE", "QUAL", "USMV"]

        # AllWeather universe: traditional assets
        aw_tickers = ["SPY", "IEF", "GLD", "XLP"]

        # Add all equities
        all_tickers = ff_tickers + aw_tickers
        for ticker in all_tickers:
            self.add_equity(ticker, Resolution.DAILY)

        # Create Alpha models
        self.set_alpha(CompositeAlphaModel(
            FamaFrenchAlpha(ff_tickers),
            AllWeatherAlpha(aw_tickers)
        ))

        # Target allocation: configurable via backtest parameters (default FF20/AW80)
        ff_allocation = float(self.GetParameter("ff_allocation", 0.20))
        aw_allocation = float(self.GetParameter("aw_allocation", 0.80))

        self.set_portfolio_construction(MultiStrategyPCM(
            alpha_allocations={
                "FamaFrench": ff_allocation,
                "AllWeather": aw_allocation,
            },
            rebalance=timedelta(days=31)  # Monthly rebalance
        ))

        self.set_risk_management(NullRiskManagementModel())
        self.set_execution(ImmediateExecutionModel())
        self.set_benchmark("SPY")
        self.set_warm_up(252, Resolution.DAILY)  # 1 year for momentum calculations

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FRAMEWORK COMPOSITE (FF20/AW80): Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
