# region imports
from AlgorithmImports import *
from alpha_models import SectorMomentumAlpha, RegimeSwitchingAlpha
from portfolio_construction import MultiStrategyPCM
# endregion


class FrameworkCompositeMomentumRegime(QCAlgorithm):
    """
    Framework Composite - MomentumSector + RegimeSwitching

    Combines Sector Dual Momentum (SPY/TLT/GLD) with Regime-Switching
    (Momentum in bull, Mean-Reversion in bear/sideways) via QC Algorithm Framework.

    Target allocation: T60/RS40 (Trend60/RegimeSwitching40)
    - Initial sweep will test T55/RS45 to T65/RS35

    Monthly rebalancing (low turnover).

    Reference strategies:
    - SectorMomentum: Sharpe 0.621, CAGR 13.2%, MaxDD 22.8% (2010-2026)
    - RegimeSwitching: Sharpe 0.553, CAGR 11.7%, MaxDD 33.0% (2008-2026)

    Hypothesis: Combining momentum in strong regimes with defensive mean-reversion
    in weak regimes should improve risk-adjusted returns.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # Combined universe from both strategies
        # SectorMomentum: SPY, IEF, GLD (IEF instead of TLT - TLT destroys value 2015-2026)
        # RegimeSwitching: SPY, QQQ, IEF, GLD
        all_tickers = ["SPY", "QQQ", "IEF", "GLD"]

        for ticker in all_tickers:
            self.add_equity(ticker, Resolution.DAILY)

        # Create Alpha models
        sector_mom_tickers = ["SPY", "IEF", "GLD"]  # IEF instead of TLT
        regime_switch_tickers = ["SPY", "QQQ", "IEF", "GLD"]

        self.set_alpha(CompositeAlphaModel(
            SectorMomentumAlpha(sector_mom_tickers),
            RegimeSwitchingAlpha(regime_switch_tickers)
        ))

        # Target allocation: T60/RS40
        # Will sweep from T55/RS45 to T65/RS35 during optimization
        self.set_portfolio_construction(MultiStrategyPCM(
            alpha_allocations={
                "SectorMomentum": 0.60,
                "RegimeSwitching": 0.40,
            },
            rebalance=timedelta(days=31)  # Monthly
        ))

        self.set_risk_management(NullRiskManagementModel())
        self.set_execution(ImmediateExecutionModel())
        self.set_benchmark("SPY")
        self.set_warm_up(252, Resolution.DAILY)  # 1 year for all indicators

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FRAMEWORK COMPOSITE (T60/RS40): Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
