# region imports
from AlgorithmImports import *
from alpha_models import SectorMomentumAlpha, RegimeSwitchingAlpha
from portfolio_construction import MultiStrategyPCM
# endregion


class MomentumRegimeAdaptiveWeights(QCAlgorithm):
    """
    Adaptive-weight composite: SectorMomentum (85%) + RegimeSwitching (15%).

    Variant of Framework_Composite_MomentumRegime (project 31243821).
    The baseline 60/40 split diluted SectorMomentum returns OOS (Sharpe 0.145).
    This variant shifts weight toward the stronger momentum signal.

    Changes from baseline:
    - T85/RS15 allocation (was T60/RS40)
    - SectorMomentum universe includes QQQ (was SPY/IEF/GLD only)
    - SectorMomentum lookback weights favor shorter-term (0.5/0.2/0.2/0.1)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2025, 12, 31)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        all_tickers = ["SPY", "QQQ", "IEF", "GLD"]

        for ticker in all_tickers:
            self.add_equity(ticker, Resolution.DAILY)

        # SectorMomentum now includes QQQ for growth exposure
        sector_mom_tickers = ["SPY", "QQQ", "IEF", "GLD"]
        regime_switch_tickers = ["SPY", "QQQ", "IEF", "GLD"]

        self.set_alpha(CompositeAlphaModel(
            SectorMomentumAlpha(sector_mom_tickers),
            RegimeSwitchingAlpha(regime_switch_tickers)
        ))

        # Adaptive weight: T85/RS15
        self.set_portfolio_construction(MultiStrategyPCM(
            alpha_allocations={
                "SectorMomentum": 0.85,
                "RegimeSwitching": 0.15,
            },
            rebalance=timedelta(days=31)
        ))

        self.set_risk_management(NullRiskManagementModel())
        self.set_execution(ImmediateExecutionModel())
        self.set_benchmark("SPY")
        self.set_warm_up(252, Resolution.DAILY)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"ADAPTIVE T85/RS15: Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
