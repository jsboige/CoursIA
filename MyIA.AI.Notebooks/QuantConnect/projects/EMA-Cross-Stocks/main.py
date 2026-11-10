# region imports
from AlgorithmImports import *
# endregion


class _ScaledFeeModel(FeeModel):
    """Broker fees (Lean default model), scaled (identity at 1.0).

    Declared copy from TrendWeatherPointInTime: a QC project cannot import another project.
    """

    def __init__(self, multiplier):
        self._multiplier = multiplier
        self._base = InteractiveBrokersFeeModel()

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None or self._multiplier == 1.0:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))


class _Initializer(BrokerageModelSecurityInitializer):
    """Brokerage initialisation, plus the last known price on add and the scaled fees."""

    def __init__(self, brokerage_model, seeder, fee_mult):
        super().__init__(brokerage_model, seeder)
        self._fee_mult = fee_mult

    def initialize(self, security):
        super().initialize(security)
        if self._fee_mult != 1.0:
            security.set_fee_model(_ScaledFeeModel(self._fee_mult))


class EMACrossStocksAlgorithm(QCAlgorithm):
    """Multi-stock EMA crossover: AAPL, MSFT, GOOGL, AMZN, NVDA.

    Equal-weight portfolio of stocks with bullish EMA cross.
    Long each stock when its EMA fast > EMA slow, flat otherwise.
    Rebalances daily, max 5 positions.

    Brokerage parameter: pass "brokerage=none" to test cost-free baseline.
    Default: IBKR Margin (realistic fees).

    Measurement parameters (#20258), no effect with their defaults:
    - start, end: backtest window (default 2015-01-01 / 2024-12-31);
    - universe: "fixed" (the five tickers above) or "pit" (each month, the top_n largest
      US market caps known at that date);
    - top_n: size of the "pit" universe (default 5);
    - mode: "ema" (the rule above) or "hold" (same names, same weights, same 5% band,
      no EMA condition);
    - fee_mult: broker fee multiplier (default 1);
    - trace: "1" plots the portfolio value and the SPY close once per session in a
      "shadow" chart (interleaved series e0..e4 and b0..b4, strategy league format #19821).
    """

    def initialize(self):
        start = datetime.strptime(self.get_parameter("start", "2015-01-01"), "%Y-%m-%d")
        end = datetime.strptime(self.get_parameter("end", "2024-12-31"), "%Y-%m-%d")
        self.set_start_date(start.year, start.month, start.day)
        self.set_end_date(end.year, end.month, end.day)
        self.set_cash(100000)

        # Brokerage: US equities traded via IBKR margin account
        # Use parameter "brokerage=none" to test without brokerage fees (cost-free baseline)
        brokerage_mode = self.get_parameter("brokerage", "ibkr")
        self._brokerage_mode = brokerage_mode
        if brokerage_mode != "none":
            self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self._universe_mode = self.get_parameter("universe", "fixed")
        self._pit = self._universe_mode == "pit"
        self.top_n = int(self.get_parameter("top_n", "5"))
        self._hold = self.get_parameter("mode", "ema") == "hold"
        fee_mult = float(self.get_parameter("fee_mult", "1"))
        self._trace = self.get_parameter("trace", "0") == "1"

        if self._pit or fee_mult != 1.0:
            seeder = FuncSecuritySeeder(self.get_last_known_prices) if self._pit else SecuritySeeder.NULL
            self.set_security_initializer(_Initializer(self.brokerage_model, seeder, fee_mult))

        self.tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]
        # key -> symbol; the key is the ticker in "fixed" mode, the symbol in "pit" mode
        self.symbols = {}
        self.ema_fast = {}
        self.ema_slow = {}

        # EMA parameters
        self.fast_period = 20
        self.slow_period = 50

        if self._pit:
            self._members = set()
            self._seen = set()
            self._sel_month = -1
            self._reviews = 0
            self.universe_settings.resolution = Resolution.DAILY
            self.add_universe(self._select)
        else:
            for ticker in self.tickers:
                security = self.add_equity(ticker, Resolution.DAILY)
                self.symbols[ticker] = security.symbol
                self.ema_fast[ticker] = self.ema(security.symbol, self.fast_period, Resolution.DAILY)
                self.ema_slow[ticker] = self.ema(security.symbol, self.slow_period, Resolution.DAILY)

        self._spy = self.add_equity("SPY", Resolution.DAILY).symbol if self._trace else None
        self._trace_points = 0
        self._lines_sum = 0
        self._cash_sessions = 0

        self.set_benchmark("SPY")
        self.set_warm_up(self.slow_period + 10, Resolution.DAILY)

        # Rebalance daily at market open
        self._last_rebal = None
        self._trade_count = 0

    def _select(self, fundamental):
        """Monthly: the top_n largest US market caps (filter of TrendWeatherPointInTime)."""
        if self.time.month == self._sel_month:
            return Universe.UNCHANGED
        self._sel_month = self.time.month
        rows = [f for f in fundamental if f.has_fundamental_data and f.price > 5 and f.market_cap > 0
                and f.security_reference.is_primary_share and not f.security_reference.is_depositary_receipt]
        rows.sort(key=lambda f: f.market_cap, reverse=True)
        chosen = [f.symbol for f in rows[:self.top_n]]
        self._members = set(chosen)
        self._seen.update(chosen)
        self._reviews += 1
        self.log(f"select {self.time:%Y-%m-%d} " + " ".join(s.value for s in chosen))
        return chosen

    def on_securities_changed(self, changes):
        if not self._pit:
            return
        for security in changes.removed_securities:
            sym = security.symbol
            if sym not in self.symbols:
                continue
            if self.portfolio[sym].invested:
                self.liquidate(sym, tag=f"Universe exit {sym.value}")
                self._trade_count += 1
            for ind in (self.ema_fast.pop(sym), self.ema_slow.pop(sym)):
                self.deregister_indicator(ind)
            del self.symbols[sym]
        for security in changes.added_securities:
            sym = security.symbol
            if sym not in self._members or sym in self.symbols:
                continue
            self.symbols[sym] = sym
            self.ema_fast[sym] = self.ema(sym, self.fast_period, Resolution.DAILY)
            self.ema_slow[sym] = self.ema(sym, self.slow_period, Resolution.DAILY)
            self.warm_up_indicator(sym, self.ema_fast[sym], Resolution.DAILY)
            self.warm_up_indicator(sym, self.ema_slow[sym], Resolution.DAILY)

    def on_data(self, data):
        if self.is_warming_up:
            return

        if self._trace and data.bars.contains_key(self._spy):
            k = self._trace_points % 5
            self.plot("shadow", f"e{k}", self.portfolio.total_portfolio_value)
            self.plot("shadow", f"b{k}", data.bars[self._spy].close)
            self._trace_points += 1
            lines = sum(1 for sym in self.symbols.values() if self.portfolio[sym].invested)
            self._lines_sum += lines
            self._cash_sessions += lines == 0

        # A slice with no trade bar for the universe (a dividend or split notice, delivered at
        # midnight) must not run the day's rebalance: every name would read as "no data" and be
        # liquidated, and the day's real bars would then be skipped (#20258).
        if not any(data.bars.contains_key(sym) for sym in self.symbols.values()):
            return

        # Rebalance once per day
        today = self.time.date()
        if self._last_rebal == today:
            return
        self._last_rebal = today

        # Find stocks with bullish EMA cross ("hold" mode: every name with ready data)
        bullish = []
        for key, sym in self.symbols.items():
            if not self.ema_fast[key].is_ready or not self.ema_slow[key].is_ready:
                continue
            if not data.contains_key(sym) or data[sym] is None:
                continue
            if self._hold or self.ema_fast[key].current.value > self.ema_slow[key].current.value:
                bullish.append(key)

        # Equal weight allocation
        target_weight = 0.95 / max(len(bullish), 1) if bullish else 0

        for key, sym in self.symbols.items():
            name = sym.value if self._pit else key
            if key in bullish:
                current = self.portfolio[sym].holdings_value / self.portfolio.total_portfolio_value
                if abs(current - target_weight) > 0.05:
                    self.set_holdings(sym, target_weight, tag=f"EMA Long {name}")
                    self._trade_count += 1
            else:
                if self.portfolio[sym].invested:
                    self.liquidate(sym, tag=f"EMA Exit {name}")
                    self._trade_count += 1

    def on_end_of_algorithm(self):
        years = (self.end_date - self.start_date).days / 365.25
        self.log(f"EMA-Cross-Stocks: Brokerage={self._brokerage_mode} | "
                 f"Trades={self._trade_count} | "
                 f"Avg trades/yr={self._trade_count / max(years, 1):.0f}")
        if self._trace:
            self.set_runtime_statistic("Trace points", str(self._trace_points))
            self.set_runtime_statistic("Avg lines held", f"{self._lines_sum / max(self._trace_points, 1):.3f}")
            self.set_runtime_statistic("Cash sessions", str(self._cash_sessions))
        if self._pit:
            self.set_runtime_statistic("Reviews", str(self._reviews))
            self.set_runtime_statistic("Distinct members", str(len(self._seen)))
