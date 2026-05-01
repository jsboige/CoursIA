# region imports
from AlgorithmImports import *
# endregion


class EMACrossCryptoAlgorithm(QCAlgorithm):
    """Dual EMA crossover on BTCUSDT (Binance Cash) with risk management.

    Entry: EMA fast > EMA slow AND BTC > SMA200 (bull market filter).
    Exit: EMA cross (fast < slow) OR trailing stop triggered.
    Position size: 80% of available USDT (reduced from 95%).
    Trailing stop: 10% from peak price.

    Research findings (research.ipynb):
    - SMA200 filter is the most powerful MaxDD reducer (~10-15 pts reduction)
    - Trailing stop 10% adds further protection against rapid crashes
    - Position cap 80% reduces exposure proportionally
    - EMA 20/50 remains optimal (no improvement from alternatives)
    - Scale-out and dynamic vol sizing add complexity without clear benefit
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)  # Extended from 2020: +3 years for robustness validation (includes 2017 bull & 2018 crash)
        self.set_account_currency("USDT")
        self.set_cash(10000)
        self.btc = self.add_crypto("BTCUSDT", Resolution.DAILY, Market.BINANCE).symbol
        self.set_benchmark(self.btc)
        self.set_brokerage_model(BrokerageName.BINANCE, AccountType.CASH)

        # EMA parameters (unchanged from v1 - 20/50 is optimal)
        self.fast_period = 20
        self.slow_period = 50

        # Risk management parameters
        self.position_size = 0.80       # Reduced from 0.95 - limits exposure
        self.trailing_stop_pct = 0.10   # 10% trailing stop from peak
        self.sma200_period = 200        # Bull market filter

        # Indicators
        self.ema_fast = self.ema(self.btc, self.fast_period, Resolution.DAILY)
        self.ema_slow = self.ema(self.btc, self.slow_period, Resolution.DAILY)
        self.sma200 = self.SMA(self.btc, self.sma200_period, Resolution.DAILY)

        # Trailing stop tracking
        self.peak_price = 0.0

        warmup_days = self.sma200_period + 10
        self.set_warm_up(warmup_days, Resolution.DAILY)

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not self.ema_fast.is_ready or not self.ema_slow.is_ready or not self.sma200.is_ready:
            return
        if not data.contains_key(self.btc) or data[self.btc] is None:
            return

        fast_val = self.ema_fast.current.value
        slow_val = self.ema_slow.current.value
        sma200_val = self.sma200.current.value
        price = float(data[self.btc].close)
        invested = self.portfolio[self.btc].invested

        # Update trailing stop peak
        if invested and price > self.peak_price:
            self.peak_price = price

        # --- EXIT LOGIC ---

        # 1. Trailing stop (checked first - protects against rapid crashes)
        if invested and self.peak_price > 0:
            drawdown_from_peak = (price - self.peak_price) / self.peak_price
            if drawdown_from_peak <= -self.trailing_stop_pct:
                qty = self.portfolio[self.btc].quantity
                if qty > 0:
                    self.market_order(self.btc, -qty,
                                      tag=f"Trailing Stop {drawdown_from_peak*100:.1f}%")
                    self.peak_price = 0.0
                return

        # 2. EMA cross exit: fast crosses below slow
        if fast_val < slow_val and invested:
            qty = self.portfolio[self.btc].quantity
            if qty > 0:
                self.market_order(self.btc, -qty, tag="EMA Cross Exit")
                self.peak_price = 0.0

        # --- ENTRY LOGIC ---

        # Long signal: fast EMA > slow EMA AND BTC above SMA200 (bull market)
        elif fast_val > slow_val and not invested:
            # SMA200 filter: only enter in structural bull market
            if price < sma200_val:
                return  # Skip entry if BTC is below its 200-day SMA

            usdt_available = self.portfolio.cash_book["USDT"].amount
            qty = round((usdt_available * self.position_size) / price, 5)
            if qty > 0 and usdt_available > 10:
                self.market_order(self.btc, qty, tag="EMA Cross Long")
                self.peak_price = price
