# region imports
from AlgorithmImports import *
# endregion


class EMACrossIndexAlgorithm(QCAlgorithm):
    """Simple dual EMA crossover on SPY (S&P 500 index ETF).

    Long when EMA fast > EMA slow, flat otherwise.
    Daily resolution, no leverage, simple risk management.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.set_benchmark(self.spy)

        # EMA parameters
        self.fast_period = 20
        self.slow_period = 50

        # Indicators
        self.ema_fast = self.ema(self.spy, self.fast_period, Resolution.DAILY)
        self.ema_slow = self.ema(self.spy, self.slow_period, Resolution.DAILY)

        self.set_warm_up(self.slow_period + 10, Resolution.DAILY)

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not self.ema_fast.is_ready or not self.ema_slow.is_ready:
            return
        if not data.contains_key(self.spy) or data[self.spy] is None:
            return

        fast_val = self.ema_fast.current.value
        slow_val = self.ema_slow.current.value
        invested = self.portfolio[self.spy].invested

        # Long signal: fast EMA crosses above slow EMA
        if fast_val > slow_val and not invested:
            self.set_holdings(self.spy, 0.95, tag="EMA Cross Long")

        # Exit: fast EMA crosses below slow EMA
        elif fast_val < slow_val and invested:
            self.liquidate(self.spy, tag="EMA Cross Exit")
