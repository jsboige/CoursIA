# region imports
from AlgorithmImports import *
from alpha_models import FamaFrenchAlpha, AllWeatherAlpha
from portfolio_construction import MultiStrategyPCM
# endregion


class FrameworkCompositeStrategy(QCAlgorithm):
    """
    Framework Composite v1.0 - FamaFrench + AllWeather

    Combines FamaFrench factor rotation (momentum-weighted large-caps) with
    AllWeather (SPY/IEF/GLD/XLP) via Algorithm Framework.

    Allocation sweep (2015-2025):
    - FF40/AW60: To be tested
    - FF50/AW50: To be tested (baseline)
    - FF60/AW40: To be tested

    Target: Sharpe > 0.7 (both standalone: FF=0.540, AW=0.667)

    Expected improvement: FF provides growth momentum, AW provides
    defensive diversification with low correlation.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # FamaFrench factor ETFs
        ff_tickers = ["VLUE", "MTUM", "SIZE", "QUAL", "USMV"]
        
        # AllWeather tickers
        aw_tickers = ["SPY", "IEF", "GLD", "XLP"]

        # Add SPY for FF regime filter (duplicate will be handled)
        all_tickers = list(set(ff_tickers + aw_tickers + ["SPY"]))
        for ticker in all_tickers:
            self.add_equity(ticker, Resolution.DAILY)

        # Baseline allocation: FF50/AW50
        self.set_alpha(CompositeAlphaModel(
            FamaFrenchAlpha(ff_tickers + ["SPY"]),
            AllWeatherAlpha(aw_tickers)
        ))

        self.set_portfolio_construction(MultiStrategyPCM(
            alpha_allocations={
                "FamaFrench": 0.50,
                "AllWeather": 0.50,
            },
            rebalance=timedelta(days=31)
        ))

        self.set_risk_management(NullRiskManagementModel())
        self.set_execution(ImmediateExecutionModel())
        self.set_benchmark("SPY")
        self.set_warm_up(270, Resolution.DAILY)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FRAMEWORK COMPOSITE FF/AW v1.0: Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
