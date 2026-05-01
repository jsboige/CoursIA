# region imports
from AlgorithmImports import *
# endregion


class ShortTermMeanReversion(QCAlgorithm):
    """
    Sector ETF Mean Reversion Strategy v4.0

    Iteration 3 improvements (signal-focused only, no beta loading):
    - Stop-loss at -8% to cut real breakdowns (XLE 2020, XLB 2022)
    - 4 positions at 25% each (more opportunities with 11 sector ETFs)
    - RSI exit at 60 instead of 55 (let winners run slightly more)
    - Start date 2015 for more regime diversity
    - Daily entry scan (vs weekly) for faster signal capture

    Research findings (research.ipynb H7-H11):
    - H7: RSI(14) kept - more stable than RSI(7), fewer false signals
    - H8: Stop-loss -8% confirmed to reduce MaxDD without killing CAGR
    - H9: Dynamic sizing tested but flat 25% preferred (simpler, more robust)
    - H10: 4 positions > 3 for signal capture frequency
    - H11: 2015 start adds Dec 2018 correction and more regime diversity

    Backtest results:
    v2.0: Sharpe -0.042, CAGR 0.7%, MaxDD 46.5% (Universe Selection)
    v3.0: Sharpe -0.97, CAGR 0.65%, Net +5.4% (too few trades)
    v3.1: Sharpe 0.01, CAGR 4.31%, Net +41.2%
    v3.2: Sharpe 0.294, CAGR 7.53%, Net +80.9%, MaxDD 16.5%

    Ref: research.ipynb, Jegadeesh (1990), De Bondt & Thaler (1985)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)

        # 11 GICS sector ETFs - the signal universe
        self.sector_etfs = [
            "XLK", "XLF", "XLE", "XLV", "XLI",
            "XLY", "XLP", "XLU", "XLB", "XLRE", "XLC"
        ]
        self.symbols = {}
        self.rsi_indicators = {}

        for etf in self.sector_etfs:
            equity = self.add_equity(etf, Resolution.DAILY)
            self.symbols[etf] = equity.symbol
            self.rsi_indicators[etf] = self.rsi(equity.symbol, 14)

        # SPY regime filter
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.spy_sma = self.sma(self.spy, 200, Resolution.DAILY)

        # Strategy parameters (v4.0 changes vs v3.2)
        self.rsi_oversold = 40       # Entry threshold (unchanged - confirmed optimal)
        self.rsi_exit = 60           # Exit threshold (was 55 - let winners run more)
        self.num_positions = 4       # Max simultaneous positions (was 3)
        self.holding_period = 15     # Days to hold (unchanged)
        self.stop_loss_pct = 0.08    # Stop-loss at -8% (new - cut real breakdowns)
        self.position_weight = 0.25  # 25% per position (was 33% for 3 positions)

        # Position tracking
        self.entry_days = {}         # {etf: day_count}
        self.entry_prices = {}       # {etf: entry_price} for stop-loss
        self.day_count = 0

        # Daily scan for signal
        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self._daily_scan
        )

        self.set_benchmark("SPY")
        self.set_warm_up(200, Resolution.DAILY)

    def _daily_scan(self):
        if self.is_warming_up:
            return

        self.day_count += 1

        # SPY regime filter - exit all in bear market
        if self.spy_sma.is_ready:
            spy_price = self.securities[self.spy].price
            if spy_price < self.spy_sma.current.value:
                if self.portfolio.invested:
                    self.liquidate()
                    self.entry_days.clear()
                    self.entry_prices.clear()
                    self.log("RISK OFF: SPY < SMA200")
                return

        # Check exits: stop-loss, RSI exit, holding period
        to_exit = []
        for etf in list(self.entry_days.keys()):
            days_held = self.day_count - self.entry_days[etf]
            rsi_val = self.rsi_indicators[etf].current.value
            current_price = self.securities[self.symbols[etf]].price

            # Stop-loss: cut real breakdowns
            if etf in self.entry_prices:
                drawdown = (current_price - self.entry_prices[etf]) / self.entry_prices[etf]
                if drawdown < -self.stop_loss_pct:
                    to_exit.append(etf)
                    self.log(f"STOP-LOSS: {etf}, drawdown={drawdown:.1%}")
                    continue

            # RSI exit or holding period expired
            if days_held >= self.holding_period or rsi_val > self.rsi_exit:
                to_exit.append(etf)

        for etf in to_exit:
            self.liquidate(self.symbols[etf])
            self.entry_days.pop(etf, None)
            self.entry_prices.pop(etf, None)

        # Check entries - find most oversold ETFs not already held
        candidates = []
        for etf in self.sector_etfs:
            if etf in self.entry_days:
                continue
            rsi = self.rsi_indicators[etf]
            if not rsi.is_ready:
                continue
            rsi_val = rsi.current.value
            if rsi_val < self.rsi_oversold:
                candidates.append((etf, rsi_val))

        # Sort by RSI ascending (most oversold first)
        candidates.sort(key=lambda x: x[1])

        available = self.num_positions - len(self.entry_days)
        for etf, rsi_val in candidates[:available]:
            symbol = self.symbols[etf]
            self.set_holdings(symbol, self.position_weight)
            self.entry_days[etf] = self.day_count
            self.entry_prices[etf] = self.securities[symbol].price
            self.log(f"ENTER: {etf}, RSI={rsi_val:.1f}")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"MEAN REV v4.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
