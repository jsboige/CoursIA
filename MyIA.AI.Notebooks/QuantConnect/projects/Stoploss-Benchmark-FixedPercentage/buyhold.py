# region imports
from AlgorithmImports import *
# endregion


class BuyAndHoldKOAlgorithm(QCAlgorithm):
    """
    Buy-and-hold KO baseline for the HandsOn Ex08 stop-loss benchmark
    (book reference: Sharpe 0.263, 2018-12-31 to 2024-04-01, 100k).
    Buys KO once at the start and holds until the end. Entry timed like
    the benchmark algorithm (first trading day, 9:32 AM). This file is
    the main.py of cloud project HandsOn-Ex08-Stoploss-Benchmark-BuyHold.
    """

    def initialize(self):
        self.set_start_date(2018, 12, 31)
        self.set_end_date(2024, 4, 1)
        self.set_cash(100_000)
        self._symbol = self.add_equity(
            "KO", data_normalization_mode=DataNormalizationMode.RAW
        ).symbol
        self.schedule.on(
            self.date_rules.on(2018, 12, 31),
            self.time_rules.after_market_open(self._symbol, 2),
            self._enter
        )

    def _enter(self):
        self.market_order(self._symbol, self.calculate_order_quantity(self._symbol, 1))
