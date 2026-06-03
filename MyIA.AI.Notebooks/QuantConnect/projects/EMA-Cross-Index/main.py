# region imports
from AlgorithmImports import *
# endregion


class EMACrossIndexAlgorithm(QCAlgorithm):
    """Dual EMA crossover on SPY (S&P 500 index ETF) - v2.0.

    Research findings (research.ipynb):
    - EMA 20/60 selected over 20/50: robustness IS/OOS = 1.55 (best of grid search)
    - Slow=60 captures quarterly trends, reduces whipsaws vs slow=50
    - Cooldown 3d after exit: eliminates immediate re-entry on false signals (+4.6% Sharpe)
    - Trailing stop rejected: degrades Sharpe OR changes strategy nature (too many trades)
    - QQQ rejected: correlation 0.92-0.95 with SPY, no real diversification benefit
    - Volume filter rejected: SPY is hyper-liquid, volume not directional signal for ETFs

    Signal: long when EMA(20) > EMA(60), flat otherwise. Exit on cross-down.
    Beta ~ 0.42 (signal-driven, not beta loading).
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.set_benchmark(self.spy)

        # EMA parameters (v2.0: slow changed from 50 to 60)
        # Justification: EMA 20/60 has IS/OOS robustness = 1.55, OOS Sharpe = 1.325 (2010-2015)
        # confirming the signal is structural, not overfitted to the 2015-2026 bull market
        self.fast_period = 20
        self.slow_period = 60

        # Cooldown after exit: 3 days to avoid immediate re-entry on false signals
        # Justification: eliminates 1 whipsaw trade over 11 years, +4.6% Sharpe improvement
        self.cooldown_days = 3
        self.cooldown_counter = 0

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

        # Decrement cooldown counter
        if self.cooldown_counter > 0:
            self.cooldown_counter -= 1

        # Long signal: fast EMA crosses above slow EMA (and not in cooldown)
        if fast_val > slow_val and not invested and self.cooldown_counter == 0:
            self.set_holdings(self.spy, 0.95, tag="EMA Cross Long")

        # Exit: fast EMA crosses below slow EMA
        elif fast_val < slow_val and invested:
            self.liquidate(self.spy, tag="EMA Cross Exit")
            self.cooldown_counter = self.cooldown_days
