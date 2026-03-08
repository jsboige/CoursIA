# region imports
from AlgorithmImports import *
# endregion


class EMACrossStocksAlgorithm(QCAlgorithm):
    """Multi-stock EMA crossover: AAPL, MSFT, GOOGL, AMZN, NVDA.

    Equal-weight portfolio of stocks with bullish EMA cross.
    Long each stock when its EMA fast > EMA slow, flat otherwise.
    Rebalances daily, max 5 positions.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)

        self.tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]
        self.symbols = {}
        self.ema_fast = {}
        self.ema_slow = {}

        # EMA parameters
        self.fast_period = 20
        self.slow_period = 50

        for ticker in self.tickers:
            sym = self.add_equity(ticker, Resolution.DAILY).symbol
            self.symbols[ticker] = sym
            self.ema_fast[ticker] = self.ema(sym, self.fast_period, Resolution.DAILY)
            self.ema_slow[ticker] = self.ema(sym, self.slow_period, Resolution.DAILY)

        self.set_benchmark("SPY")
        self.set_warm_up(self.slow_period + 10, Resolution.DAILY)

        # Rebalance daily at market open
        self._last_rebal = None

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
            else:
                if self.portfolio[sym].invested:
                    self.liquidate(sym, tag=f"EMA Exit {ticker}")
