# region imports
from AlgorithmImports import *
# endregion


class ShortTermMeanReversion(QCAlgorithm):
    """
    Sector ETF Mean Reversion Strategy v3.2

    Research-driven RSI mean reversion on 11 GICS sector ETFs.
    Replaces slow Universe Selection with fixed ETF basket.
    Long-only, top 3 most oversold ETFs. Daily scan.
    SPY SMA200 regime filter. Exit on RSI > 55 or 15-day hold.

    Backtest results:
    v2.0: Sharpe -0.042, CAGR 0.7%, MaxDD 46.5% (Universe Selection)
    v3.0: Sharpe -0.97, CAGR 0.65%, Net +5.4% (too few trades)
    v3.1: Sharpe 0.01, CAGR 4.31%, Net +41.2%
    v3.2: Sharpe 0.294, CAGR 7.53%, Net +80.9%, MaxDD 16.5%

    Ref: research.ipynb, Jegadeesh (1990), De Bondt & Thaler (1985)
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_cash(100000)

        # 11 GICS sector ETFs
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

        # Strategy parameters
        self.rsi_oversold = 40      # Entry threshold
        self.rsi_exit = 55          # Exit threshold
        self.num_positions = 3      # Max simultaneous positions
        self.holding_period = 15    # Days to hold

        # Position tracking
        self.entry_days = {}
        self.day_count = 0

        # Daily scan
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

        # SPY regime filter
        if self.spy_sma.is_ready:
            spy_price = self.securities[self.spy].price
            if spy_price < self.spy_sma.current.value:
                if self.portfolio.invested:
                    self.liquidate()
                    self.entry_days.clear()
                    self.log("RISK OFF: SPY < SMA200")
                return

        # Check exits
        to_exit = []
        for etf, entry_day in self.entry_days.items():
            days_held = self.day_count - entry_day
            rsi_val = self.rsi_indicators[etf].current.value
            if days_held >= self.holding_period or rsi_val > self.rsi_exit:
                to_exit.append(etf)

        for etf in to_exit:
            self.liquidate(self.symbols[etf])
            del self.entry_days[etf]

        # Check entries
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

        candidates.sort(key=lambda x: x[1])

        available = self.num_positions - len(self.entry_days)
        weight = 0.33  # 33% per position
        for etf, rsi_val in candidates[:available]:
            symbol = self.symbols[etf]
            self.set_holdings(symbol, weight)
            self.entry_days[etf] = self.day_count
            self.log(f"ENTER: {etf}, RSI={rsi_val:.1f}")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"MEAN REV v3.2: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
