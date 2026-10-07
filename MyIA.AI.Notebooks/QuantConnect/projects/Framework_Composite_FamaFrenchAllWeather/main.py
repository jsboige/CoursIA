# region imports
from AlgorithmImports import *
from datetime import datetime
from alpha_models import FamaFrenchAlpha, AllWeatherAlpha
from portfolio_construction import MultiStrategyPCM
# endregion

FF_TICKERS = ["VLUE", "MTUM", "SIZE", "QUAL", "USMV"]
AW_TICKERS = ["SPY", "IEF", "GLD", "XLP"]

# Modes (#19621). "intent" (default) is the design the docstring below
# announces: the FamaFrench sleeve uses risk-adjusted momentum only. "base" is
# the code before #19621, where the SPY SMA200 regime filter is never created,
# so the FamaFrench sleeve emits nothing and stays in cash. "sma" makes that
# filter effective. "spy" and "sixty40" are held references, traded outside
# the Framework.
FRAMEWORK_MODES = ("base", "intent", "sma")
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


class FrameworkCompositeFamaFrenchAllWeather(QCAlgorithm):
    """
    Framework Composite - FamaFrench Factor Rotation + AllWeather

    Combines Fama-French factor ETF rotation (VLUE, MTUM, SIZE, QUAL, USMV)
    with AllWeather static allocation (SPY, IEF, GLD, XLP) via QC Algorithm Framework.

    Target allocation: FF20/AW80 (FamaFrench 20%, AllWeather 80%)
    Measured results and verdict (#19621): see README.md.

    Key design principle from lesson learned in MomentumRegime:
    - NO overlap between universes (factor ETFs vs traditional assets)
    - True diversification: equity factors + macro allocation
    - FamaFrench uses risk-adjusted momentum only (NO SMA200 filter - AllWeather handles defense)

    Reference strategies:
    - FamaFrench v3.0: Sharpe 0.540, CAGR 12.1%, MaxDD 24.2%
    - AllWeather: Ray Dalio-inspired static allocation

    Both alphas emit on the first trading day of each month; the portfolio
    construction model rebalances every 31 days.
    """

    def initialize(self):
        self.mode = self.get_parameter("mode") or "intent"
        if self.mode not in FRAMEWORK_MODES and self.mode not in REFERENCE_WEIGHTS:
            raise ValueError(f"unknown mode: {self.mode}")

        start = datetime.strptime(self.get_parameter("start") or "2018-01-01", "%Y-%m-%d")
        end = datetime.strptime(self.get_parameter("end") or "2025-01-01", "%Y-%m-%d")
        self.set_start_date(start)
        self.set_end_date(end)
        self.set_cash(100000)
        self.start_value = 100000
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self.fee_mult = float(self.get_parameter("fee_mult") or 1)
        if self.fee_mult != 1.0:
            self.set_security_initializer(_ScaledFeeInitializer(
                self.brokerage_model, FuncSecuritySeeder(self.get_last_known_prices), self.fee_mult))

        # FamaFrench universe: factor ETFs (iShares)
        ff_tickers = FF_TICKERS

        # AllWeather universe: traditional assets
        aw_tickers = AW_TICKERS

        # Add all equities
        all_tickers = ff_tickers + aw_tickers
        self.symbols = {}
        for ticker in all_tickers:
            self.symbols[ticker] = self.add_equity(ticker, Resolution.DAILY).symbol

        if self.mode in FRAMEWORK_MODES:
            lookback = int(self.get_parameter("lookback") or 252)
            vol_window = int(self.get_parameter("vol_window") or 63)

            # Create Alpha models
            self.set_alpha(CompositeAlphaModel(
                FamaFrenchAlpha(ff_tickers, mode=self.mode, lookback=lookback, vol_window=vol_window),
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

        # Shadow-replay contract (#18923): portfolio value at each daily close.
        self.closes = 0
        self.traded = 0.0
        self.order_counts = {}
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
            self.plot("shadow", f"e{self.closes % 5}", self.portfolio.total_portfolio_value)
            self.plot("shadow", "fees", self.portfolio.total_fees / self.start_value)
            self.plot("shadow", "turnover", self.traded)
            self.closes += 1

    def on_order_event(self, order_event):
        if order_event.status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            self.traded += (abs(order_event.fill_quantity * order_event.fill_price)
                            / self.portfolio.total_portfolio_value)
        if order_event.status == OrderStatus.FILLED:
            ticker = order_event.symbol.value
            self.order_counts[ticker] = self.order_counts.get(ticker, 0) + 1

    def on_end_of_algorithm(self):
        for ticker in FF_TICKERS + AW_TICKERS:
            self.set_runtime_statistic(f"Orders {ticker}", str(self.order_counts.get(ticker, 0)))
        ff_orders = sum(self.order_counts.get(t, 0) for t in FF_TICKERS)
        self.set_runtime_statistic("Orders FamaFrench", str(ff_orders))
        final = self.portfolio.total_portfolio_value
        self.log(f"FRAMEWORK COMPOSITE ({self.mode}): Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}, FamaFrench orders={ff_orders}")
