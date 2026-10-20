# region imports
from AlgorithmImports import *
from alpha_models import MomentumAlpha, MACDAlpha, RelativeStrengthAlpha
from portfolio_construction import RiskParityPCM, CappedPouchesPCM
from risk_management import DrawdownCapRiskModel
from execution import VWAPExecutionModel
# endregion


class CompositeC1MultiAssetRotation(QCAlgorithm):
    """
    C4.1 - Multi-Asset Rotation Composite (v10)

    One capital sleeve per alpha (canonical sleeve PCM), weekly rebalance,
    100% max exposure, 40% cap per line.
    No regime filter — let alpha models drive allocation.
    Drawdown cap 12% + trailing stop 4%.
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_end_date(2025, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # Universe: 5 ETFs across asset classes
        self.tickers = ["SPY", "TLT", "GLD", "USO", "EFA"]
        for ticker in self.tickers:
            self.add_equity(ticker, Resolution.DAILY).set_leverage(2.0)

        # Alpha Models: 3-model ensemble. alphas=momentum|macd|relstrength
        # keeps a single model (witnesses of #21147).
        alpha_classes = {
            "momentum": MomentumAlpha,
            "macd": MACDAlpha,
            "relstrength": RelativeStrengthAlpha,
        }
        alphas = self.get_parameter("alphas") or "all"
        selected = list(alpha_classes) if alphas == "all" else [alphas]
        self.set_alpha(CompositeAlphaModel(
            *[alpha_classes[name](self.tickers) for name in selected]
        ))

        # PCM: one third of capital per alpha (canonical sleeve PCM, #21134),
        # weekly rebalance, 40% cap per line. pcm_mode=symbol reproduces the
        # PCM before #21147: Lean keeps the last insight per symbol, so only
        # one alpha per ETF reaches RiskParityPCM.
        if (self.get_parameter("pcm_mode") or "sleeve") == "symbol":
            self.pcm = RiskParityPCM(
                rebalance=timedelta(days=7),
                max_exposure=1.0,
                sector_cap=0.40
            )
        else:
            self.pcm = CappedPouchesPCM(
                {"Momentum": 1 / 3, "MACD": 1 / 3, "RelStrength": 1 / 3},
                line_cap=0.40,
                rebalance=timedelta(days=7),
                algorithm=self
            )
        self.set_portfolio_construction(self.pcm)

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
        # Insights per alpha that Lean passes to the PCM (active / received).
        self.set_runtime_statistic("PCM calls", str(self.pcm.calls))
        for source in sorted(set(self.pcm.reached) | set(self.pcm.reached_active)):
            self.set_runtime_statistic(
                f"PCM {source}",
                f"{self.pcm.reached_active.get(source, 0)}/{self.pcm.reached.get(source, 0)}")
        # Sleeve mode: insights per alpha seen by the (symbol, alpha) rebuild.
        pouch_seen = getattr(self.pcm, "pouch_seen", {})
        for source in sorted(pouch_seen):
            self.set_runtime_statistic(
                f"PCM poche {source}",
                f"{self.pcm.pouch_seen_active.get(source, 0)}/{pouch_seen[source]}")
