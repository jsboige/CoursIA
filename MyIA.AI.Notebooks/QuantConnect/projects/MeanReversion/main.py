# region imports
from AlgorithmImports import *
# endregion


class ShortTermMeanReversion(QCAlgorithm):
    """
    Sector ETF Mean Reversion Strategy v4.0 - SPY Parking

    Key change: SPY parking when no active mean reversion positions.
    Core-satellite: SPY 40% core + MR positions 20% each.

    History:
    v3.0: Sharpe -0.97, CAGR 0.65%
    v3.1: Sharpe 0.01, CAGR 4.31%
    v3.2: Sharpe 0.294, CAGR 7.53%, MaxDD 16.5%
    v4.0: Sharpe 0.486, CAGR 13.4%, Net +179.9%, MaxDD 32.4%
         Alpha +0.002, Beta 0.901, Win Rate 62%

    Ref: research.ipynb, Jegadeesh (1990)
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

        # SPY for regime filter AND parking
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.spy_sma = self.sma(self.spy, 200, Resolution.DAILY)

        # Strategy parameters
        self.rsi_oversold = 40
        self.rsi_exit = 55
        self.num_positions = 3
        self.holding_period = 15
        self.mr_weight = 0.20       # 20% per MR position (satellite)
        self.spy_full = 0.95        # 95% SPY when no signals
        self.spy_core = 0.40        # 40% SPY core during active MR

        # Position tracking
        self.entry_days = {}
        self.day_count = 0

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

        # SPY regime filter - risk off = full SPY (no sector bets)
        if self.spy_sma.is_ready:
            spy_price = self.securities[self.spy].price
            if spy_price < self.spy_sma.current.value:
                for etf in list(self.entry_days.keys()):
                    self.liquidate(self.symbols[etf])
                self.entry_days.clear()
                self.set_holdings(self.spy, self.spy_full)
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
        for etf, rsi_val in candidates[:available]:
            symbol = self.symbols[etf]
            self.set_holdings(symbol, self.mr_weight)
            self.entry_days[etf] = self.day_count
            self.log(f"ENTER: {etf}, RSI={rsi_val:.1f}")

        # Adjust SPY position based on active MR positions
        active_count = len(self.entry_days)
        if active_count > 0:
            spy_target = self.spy_core
        else:
            spy_target = self.spy_full

        current_spy = self.portfolio[self.spy].holdings_value / self.portfolio.total_portfolio_value if self.portfolio.total_portfolio_value > 0 else 0
        if abs(current_spy - spy_target) > 0.05:
            self.set_holdings(self.spy, spy_target)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"MEAN REV v4.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
