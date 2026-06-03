# region imports
from AlgorithmImports import *
# endregion

class EmaCrossingDemo(QCAlgorithm):

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash("EUR", 100000)
        self.tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]

        self.fast_period = 20
        self.slow_period = 50

        self.symbols = {}
        self.ema_fast = {}
        self.ema_slow = {}

        for ticker in self.tickers:
            sym = self.add_equity(ticker, Resolution.DAILY).symbol
            self.symbols[ticker] = sym
            self.ema_fast[ticker] = self.ema(sym, self.fast_period, Resolution.DAILY)
            self.ema_slow[ticker] = self.ema(sym, self.slow_period, Resolution.DAILY)

        self.set_benchmark("SPY")
        self.set_warm_up(self.slow_period + 10, Resolution.DAILY)
        self._last_rebal = None
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.CASH)

    def on_data(self, data: Slice):
        if self.is_warming_up:
            return

        for ticker in self.tickers:
            sym = self.symbols[ticker]
            if self.portfolio[sym].invested:
                if  (self.ema_fast[ticker].current.value < self.ema_slow[ticker].current.value):
                    self.liquidate(sym, tag=f"EMA Exit {ticker}")
            else:
                if  (self.ema_fast[ticker].current.value > self.ema_slow[ticker].current.value):
                    self.set_holdings(sym, 0.2, tag=f"EMA Long {ticker}")

