# region imports
from AlgorithmImports import *
# endregion


class EMACrossCryptoAlgorithm(QCAlgorithm):
    """Simple dual EMA crossover on BTCUSDT (Binance Cash).

    Long when EMA fast > EMA slow, flat otherwise.
    Daily resolution, no leverage, simple risk management.
    """

    def initialize(self):
        self.set_start_date(2020, 1, 1)
        self.set_account_currency("USDT")
        self.set_cash(10000)
        self.btc = self.add_crypto("BTCUSDT", Resolution.DAILY, Market.BINANCE).symbol
        self.set_benchmark(self.btc)
        self.set_brokerage_model(BrokerageName.BINANCE, AccountType.CASH)

        # EMA parameters
        self.fast_period = 20
        self.slow_period = 50

        # Indicators
        self.ema_fast = self.ema(self.btc, self.fast_period, Resolution.DAILY)
        self.ema_slow = self.ema(self.btc, self.slow_period, Resolution.DAILY)

        self.set_warm_up(self.slow_period + 10, Resolution.DAILY)

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not self.ema_fast.is_ready or not self.ema_slow.is_ready:
            return
        if not data.contains_key(self.btc) or data[self.btc] is None:
            return

        fast_val = self.ema_fast.current.value
        slow_val = self.ema_slow.current.value
        invested = self.portfolio[self.btc].invested

        # Long signal: fast EMA crosses above slow EMA
        if fast_val > slow_val and not invested:
            usdt_available = self.portfolio.cash_book["USDT"].amount
            price = float(data[self.btc].close)
            qty = round((usdt_available * 0.95) / price, 5)
            if qty > 0 and usdt_available > 10:
                self.market_order(self.btc, qty, tag="EMA Cross Long")

        # Exit: fast EMA crosses below slow EMA
        elif fast_val < slow_val and invested:
            qty = self.portfolio[self.btc].quantity
            if qty > 0:
                self.market_order(self.btc, -qty, tag="EMA Cross Exit")
