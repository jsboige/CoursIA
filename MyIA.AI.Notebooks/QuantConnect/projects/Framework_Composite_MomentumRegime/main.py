# region imports
from AlgorithmImports import *
from datetime import datetime
from alpha_models import SectorMomentumAlpha, RegimeSwitchingAlpha
from portfolio_construction import MultiStrategyPCM
# endregion

ALL_TICKERS = ["SPY", "QQQ", "IEF", "GLD"]

# Modes (#19740). "intent" (default since #19740) makes MultiStrategyPCM add
# the two sleeves on shared tickers, as its docstring announces. "base" is the
# code before #19740 (RegimeSwitching at 40 %, the rest in cash). "sm" and "rs"
# run each alpha alone at 100 %. "spy" and "sixty40" are held references,
# traded outside the Framework.
FRAMEWORK_MODES = ("base", "intent", "sm", "rs")
REFERENCE_WEIGHTS = {
    "spy": {"SPY": 1.0},
    "sixty40": {"SPY": 0.6, "IEF": 0.4},
}


class _ScaledFeeModel(FeeModel):
    """Broker fees multiplied by a constant (doubled-fee robustness run)."""

    def __init__(self, multiplier):
        super().__init__()
        self._multiplier = multiplier
        self._base = InteractiveBrokersFeeModel()

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None or self._multiplier == 1.0:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))


class _ScaledFeeInitializer(BrokerageModelSecurityInitializer):
    """Keeps the brokerage model settings, then swaps in the scaled fee model."""

    def __init__(self, brokerage_model, security_seeder, multiplier):
        super().__init__(brokerage_model, security_seeder)
        self._multiplier = multiplier

    def initialize(self, security):
        super().initialize(security)
        security.set_fee_model(_ScaledFeeModel(self._multiplier))


class FrameworkCompositeMomentumRegime(QCAlgorithm):
    """
    Framework Composite - MomentumSector + RegimeSwitching

    Combines Sector Dual Momentum (SPY/IEF/GLD) with Regime-Switching
    (Momentum in bull, Mean-Reversion in bear/sideways) via QC Algorithm Framework.

    Target allocation: T60/RS40 (Trend60/RegimeSwitching40)

    Both alphas emit on the first trading day of each month on three shared
    tickers. In mode "base", Lean's PortfolioConstructionModel keeps one
    active insight per symbol before determine_target_percent runs, so the
    sleeves are not added (#19740); mode "intent" adds them. Measured results
    and verdict: README.md.

    Reference strategies:
    - SectorMomentum: Sharpe 0.621, CAGR 13.2%, MaxDD 22.8% (2010-2026)
    - RegimeSwitching: Sharpe 0.553, CAGR 11.7%, MaxDD 33.0% (2008-2026)

    Hypothesis: Combining momentum in strong regimes with defensive mean-reversion
    in weak regimes should improve risk-adjusted returns.
    """

    def initialize(self):
        self.mode = self.get_parameter("mode") or "intent"
        if self.mode not in FRAMEWORK_MODES and self.mode not in REFERENCE_WEIGHTS:
            raise ValueError(f"unknown mode: {self.mode}")

        start = datetime.strptime(self.get_parameter("start") or "2015-01-01", "%Y-%m-%d")
        end = datetime.strptime(self.get_parameter("end") or "2025-12-31", "%Y-%m-%d")
        self.set_start_date(start)
        self.set_end_date(end)
        self.set_cash(100000)
        self.start_value = 100000
        # Configurable brokerage for fee sweep (default: IBKR margin with real fees)
        self._brokerage_mode = self.get_parameter("brokerage", "ibkr")
        if self._brokerage_mode != "none":
            self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self.fee_mult = float(self.get_parameter("fee_mult") or 1)
        if self.fee_mult != 1.0 and self._brokerage_mode != "none":
            self.set_security_initializer(_ScaledFeeInitializer(
                self.brokerage_model, FuncSecuritySeeder(self.get_last_known_prices), self.fee_mult))

        # Combined universe from both strategies
        # SectorMomentum: SPY, IEF, GLD (IEF instead of TLT - TLT destroys value 2015-2026)
        # RegimeSwitching: SPY, QQQ, IEF, GLD
        self.symbols = {}
        for ticker in ALL_TICKERS:
            self.symbols[ticker] = self.add_equity(ticker, Resolution.DAILY).symbol

        self.pcm = None
        if self.mode in FRAMEWORK_MODES:
            sector_mom_tickers = ["SPY", "IEF", "GLD"]  # IEF instead of TLT
            regime_switch_tickers = ["SPY", "QQQ", "IEF", "GLD"]

            sm_weights = [float(w) for w in (self.get_parameter("sm_weights") or "0.4,0.2,0.2,0.2").split(",")]
            rs_lookback = int(self.get_parameter("rs_lookback") or 63)
            sm_allocation = float(self.get_parameter("sm_allocation") or 0.60)
            rs_allocation = float(self.get_parameter("rs_allocation") or 0.40)

            sector_momentum = SectorMomentumAlpha(sector_mom_tickers, lookback_weights=sm_weights)
            regime_switching = RegimeSwitchingAlpha(regime_switch_tickers, momentum_lookback=rs_lookback)
            if self.mode == "sm":
                self.set_alpha(CompositeAlphaModel(sector_momentum))
                allocations = {"SectorMomentum": 1.0}
            elif self.mode == "rs":
                self.set_alpha(CompositeAlphaModel(regime_switching))
                allocations = {"RegimeSwitching": 1.0}
            else:
                self.set_alpha(CompositeAlphaModel(sector_momentum, regime_switching))
                allocations = {"SectorMomentum": sm_allocation, "RegimeSwitching": rs_allocation}

            self.pcm = MultiStrategyPCM(
                alpha_allocations=allocations,
                rebalance=timedelta(days=31),  # Monthly
                additive=(self.mode == "intent"),
                algorithm=self,
            )
            self.set_portfolio_construction(self.pcm)

            self.set_risk_management(NullRiskManagementModel())
            self.set_execution(ImmediateExecutionModel())
        self.set_benchmark("SPY")
        self.set_warm_up(252, Resolution.DAILY)  # 1 year for all indicators

        # Shadow-replay contract (#18923): portfolio value at each daily close.
        self.closes = 0
        self.traded = 0.0
        self.order_counts = {}
        self.gross_sum = 0.0
        self._ref_month = -1

    def on_data(self, data):
        if self.is_warming_up:
            return
        if self.mode in REFERENCE_WEIGHTS and self.time.month != self._ref_month:
            # Held reference, rebalanced on the first daily bar of each month,
            # the same bar on which the Framework alphas emit.
            self._ref_month = self.time.month
            for ticker, weight in REFERENCE_WEIGHTS[self.mode].items():
                self.set_holdings(self.symbols[ticker], weight)
        if data.bars.contains_key(self.symbols["SPY"]):
            value = self.portfolio.total_portfolio_value
            self.plot("shadow", f"e{self.closes % 5}", value)
            self.plot("shadow", "fees", self.portfolio.total_fees / self.start_value)
            self.plot("shadow", "turnover", self.traded)
            gross = sum(abs(holding.holdings_value) for holding in self.portfolio.values())
            self.gross_sum += gross / value if value > 0 else 0.0
            self.closes += 1

    def on_order_event(self, order_event):
        if order_event.status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            self.traded += (abs(order_event.fill_quantity * order_event.fill_price)
                            / self.portfolio.total_portfolio_value)
        if order_event.status == OrderStatus.FILLED:
            ticker = order_event.symbol.value
            self.order_counts[ticker] = self.order_counts.get(ticker, 0) + 1

    def on_end_of_algorithm(self):
        for ticker in ALL_TICKERS:
            self.set_runtime_statistic(f"Orders {ticker}", str(self.order_counts.get(ticker, 0)))
        gross = self.gross_sum / self.closes if self.closes else 0.0
        self.set_runtime_statistic("Gross exposure", f"{gross:.3f}")
        if self.pcm is not None:
            self.set_runtime_statistic("PCM calls", str(self.pcm.calls))
            self.set_runtime_statistic("PCM calls with SM", str(self.pcm.calls_with_sm))
            self.set_runtime_statistic("SM UP reaching PCM", str(self.pcm.sm_up_seen))
        final = self.portfolio.total_portfolio_value
        self.log(f"FRAMEWORK COMPOSITE ({self.mode}): Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}, gross exposure={gross:.3f}")
