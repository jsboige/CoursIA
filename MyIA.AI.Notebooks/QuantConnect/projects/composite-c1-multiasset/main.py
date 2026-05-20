# region imports
from AlgorithmImports import *
from alpha_models import MomentumAlpha, MACDAlpha, RelativeStrengthAlpha
from portfolio_construction import RiskParityPCM
from risk_management import DrawdownCapRiskModel
from execution import VWAPExecutionModel
# endregion


class CompositeC1MultiAssetRotation(QCAlgorithm):
    """
    C4.1 - Multi-Asset Rotation Composite (v10)

    Equal-weight PCM, weekly rebalance, 100% max exposure.
    No regime filter — let alpha models drive allocation.
    Drawdown cap 12% + trailing stop 4%.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2025, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # Universe: 5 ETFs across asset classes
        self.tickers = ["SPY", "TLT", "GLD", "USO", "EFA"]
        for ticker in self.tickers:
            self.add_equity(ticker, Resolution.DAILY).set_leverage(2.0)

        # Alpha Models: 3-model ensemble
        self.set_alpha(CompositeAlphaModel(
            MomentumAlpha(self.tickers),
            MACDAlpha(self.tickers),
            RelativeStrengthAlpha(self.tickers)
        ))

        # PCM: Equal-weight, weekly rebalance, 100% exposure
        self.set_portfolio_construction(RiskParityPCM(
            rebalance=timedelta(days=7),
            max_exposure=1.0,
            sector_cap=0.40
        ))

        # Risk: Drawdown cap + trailing stop
        dd_cap = float(self.get_parameter("max_drawdown", 0.12))
        trail = float(self.get_parameter("trail_stop", 0.04))
        self.set_risk_management(DrawdownCapRiskModel(
            max_drawdown=dd_cap,
            trail_pct=trail
        ))

        # Execution: VWAP slicing
        self.set_execution(VWAPExecutionModel(
            num_slices=4,
            slice_interval_minutes=15
        ))

        self.set_benchmark("SPY")
        self.set_warm_up(252, Resolution.DAILY)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"C4.1 MULTI-ASSET ROTATION: Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
