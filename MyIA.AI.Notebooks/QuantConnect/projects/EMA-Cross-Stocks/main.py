# region imports
from AlgorithmImports import *
# endregion


class EMACrossStocksAlgorithm(QCAlgorithm):
    """Multi-stock EMA crossover: AAPL, MSFT, GOOGL, AMZN, NVDA.

    Equal-weight portfolio of stocks with bullish EMA cross.
    Long each stock when its EMA fast > EMA slow, flat otherwise.
    Rebalances daily, max 5 positions.

    Brokerage parameter: pass "brokerage=none" to test cost-free baseline.
    Default: IBKR Margin (realistic fees).
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)

        # Brokerage: US equities traded via IBKR margin account
        # Use parameter "brokerage=none" to test without brokerage fees (cost-free baseline)
        brokerage_mode = self.get_parameter("brokerage", "ibkr")
        self._brokerage_mode = brokerage_mode
        if brokerage_mode != "none":
            self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self.tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]
        self.symbols = {}
        self.ema_fast = {}
        self.ema_slow = {}

        # EMA parameters
        self.fast_period = 20
        self.slow_period = 50

        for ticker in self.tickers:
            security = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = security.symbol
            self.ema_fast[ticker] = self.ema(security.symbol, self.fast_period, Resolution.DAILY)
            self.ema_slow[ticker] = self.ema(security.symbol, self.slow_period, Resolution.DAILY)

        self.set_benchmark("SPY")
        self.set_warm_up(self.slow_period + 10, Resolution.DAILY)

        # Rebalance daily at market open
        self._last_rebal = None
        self._trade_count = 0

    def on_data(self, data):
        if self.is_warming_up:
            return

        # Rebalance once per day
        today = self.time.date()
        if self._last_rebal == today:
            return
        self._last_rebal = today

        # Find stocks with bullish EMA cross
        bullish = []
        for ticker in self.tickers:
            sym = self.symbols[ticker]
            if not self.ema_fast[ticker].is_ready or not self.ema_slow[ticker].is_ready:
                continue
            if not data.contains_key(sym) or data[sym] is None:
                continue
            if self.ema_fast[ticker].current.value > self.ema_slow[ticker].current.value:
                bullish.append(ticker)

        # Equal weight allocation
        target_weight = 0.95 / max(len(bullish), 1) if bullish else 0

        for ticker in self.tickers:
            sym = self.symbols[ticker]
            if ticker in bullish:
                current = self.portfolio[sym].holdings_value / self.portfolio.total_portfolio_value
                if abs(current - target_weight) > 0.05:
                    self.set_holdings(sym, target_weight, tag=f"EMA Long {ticker}")
                    self._trade_count += 1
            else:
                if self.portfolio[sym].invested:
                    self.liquidate(sym, tag=f"EMA Exit {ticker}")
                    self._trade_count += 1

    def on_end_of_algorithm(self):
        years = (self.end_date - self.start_date).days / 365.25
        self.log(f"EMA-Cross-Stocks: Brokerage={self._brokerage_mode} | "
                 f"Trades={self._trade_count} | "
                 f"Avg trades/yr={self._trade_count / max(years, 1):.0f}")
