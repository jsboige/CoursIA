# region imports
from AlgorithmImports import *
from datetime import datetime
from alpha_models import EMACrossAlpha, TrendStocksAlpha
from portfolio_construction import MultiStrategyPCM
# endregion

# EMA-Cross universe: 5 tech/Mag7 stocks
EMA_TICKERS = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]

# TrendStocks universe: 15 stocks (includes the 5 tech/Mag7)
TREND_TICKERS = [
    "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA",  # Tech (overlap)
    "JPM", "V", "MA",                            # Financials
    "UNH", "JNJ",                                 # Healthcare
    "XOM", "CVX",                                 # Energy
    "HD", "PG", "KO"                             # Consumer staples
]

# Modes (#19759). "intent" (default since #19759) makes MultiStrategyPCM add
# the two slices on the shared tickers, as the docstring announces. "base" is
# the code before #19759: on the five shared tickers the last alpha to emit
# wins. "ema" and "trend" run each alpha alone at 100 %. "spy" and "sixty40"
# are held references, traded outside the Framework.
FRAMEWORK_MODES = ("base", "intent", "ema", "trend")
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

        # SPY is the daily clock of the shadow chart in every mode (never traded
        # by the Framework modes); IEF only serves the 60/40 reference.
        self.symbols = {"SPY": self.add_equity("SPY", Resolution.DAILY).symbol}
        self.pcm = None
        if self.mode in REFERENCE_WEIGHTS:
            if "IEF" in REFERENCE_WEIGHTS[self.mode]:
                self.symbols["IEF"] = self.add_equity("IEF", Resolution.DAILY).symbol
        else:
            # Add all equities
            for ticker in sorted(set(EMA_TICKERS + TREND_TICKERS)):
                self.symbols[ticker] = self.add_equity(ticker, Resolution.DAILY).symbol

            ema_fast = int(self.get_parameter("ema_fast") or 20)
            ema_slow = int(self.get_parameter("ema_slow") or 50)
            sma_trend = int(self.get_parameter("sma_trend") or 200)
            ema_allocation = float(self.get_parameter("ema_allocation") or 0.70)
            trend_allocation = float(self.get_parameter("trend_allocation") or 0.30)

            ema_cross = EMACrossAlpha(EMA_TICKERS, fast_period=ema_fast, slow_period=ema_slow)
            trend_stocks = TrendStocksAlpha(TREND_TICKERS, ema_fast=20, ema_slow=50, sma_trend=sma_trend)
            if self.mode == "ema":
                self.set_alpha(CompositeAlphaModel(ema_cross))
                allocations = {"EMACross": 1.0}
            elif self.mode == "trend":
                self.set_alpha(CompositeAlphaModel(trend_stocks))
                allocations = {"TrendStocks": 1.0}
            else:
                self.set_alpha(CompositeAlphaModel(ema_cross, trend_stocks))
                # Target allocation: EMA70/Trend30 (sweep winner)
                allocations = {"EMACross": ema_allocation, "TrendStocks": trend_allocation}

            self.pcm = MultiStrategyPCM(
                alpha_allocations=allocations,
                rebalance=timedelta(days=7),  # Weekly rebalance to align with TrendStocks
                additive=(self.mode == "intent"),
                algorithm=self,
                watch_source="TrendStocks",
                watch_tickers=EMA_TICKERS,
            )
            self.set_portfolio_construction(self.pcm)

            self.set_risk_management(NullRiskManagementModel())
            self.set_execution(ImmediateExecutionModel())
        self.set_benchmark("SPY")
        self.set_warm_up(210, Resolution.DAILY)  # Max(SMA200, EMA50)

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
            # Held reference, rebalanced on the first daily bar of each month.
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
        for ticker in sorted(self.symbols):
            self.set_runtime_statistic(f"Orders {ticker}", str(self.order_counts.get(ticker, 0)))
        gross = self.gross_sum / self.closes if self.closes else 0.0
        self.set_runtime_statistic("Gross exposure", f"{gross:.3f}")
        if self.pcm is not None:
            self.set_runtime_statistic("PCM calls", str(self.pcm.calls))
            self.set_runtime_statistic("PCM calls with Trend on EMA tickers", str(self.pcm.calls_with_watch))
        final = self.portfolio.total_portfolio_value
        self.log(f"FRAMEWORK COMPOSITE ({self.mode}): Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}, gross exposure={gross:.3f}")
