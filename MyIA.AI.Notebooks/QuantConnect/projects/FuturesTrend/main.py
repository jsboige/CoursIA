# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class FuturesTrendFollowing(QCAlgorithm):
    """
    Multi-Asset Trend Following v3.0 - SPY Parking

    Donchian breakout on diversified ETFs (ex-SPY for signal purity).
    SPY parking when no trend signals active. Core-satellite approach.

    History:
    v2.0: Sharpe 0.144, CAGR 5.5%, MaxDD 16.9%
    v2.1: Sharpe 0.216, CAGR 6.3%, MaxDD 8.5%
    v2.3: Sharpe 0.280, CAGR 7.3%, MaxDD 10.2%
    v3.0: Sharpe 0.588, CAGR 12.6%, Net +164.2%, MaxDD 20.1%
         Alpha +0.018, Beta 0.545

    Ref: Curtis Faith (2007), Moskowitz et al. (2012), research.ipynb
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_cash(100000)

        # SPY for parking (not in signal universe)
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # 5 diversified ETFs for trend signals (SPY removed)
        self.etf_list = ["GLD", "TLT", "EFA", "VNQ", "DBC"]
        self.symbols = {}

        for etf in self.etf_list:
            equity = self.add_equity(etf, Resolution.DAILY)
            self.symbols[etf] = equity.symbol

        # Donchian parameters
        self.entry_period = 20
        self.exit_period = 10
        self.trend_weight = 0.20   # 20% per trend position (satellite)
        self.spy_core = 0.40       # 40% SPY core during active trends
        self.spy_full = 0.95       # 95% SPY when no trends
        self.max_positions = 3

        # Position tracking
        self.positions = {etf: 0 for etf in self.etf_list}

        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self._daily_scan
        )

        self.set_benchmark("SPY")
        self.set_warm_up(self.entry_period + 5, Resolution.DAILY)

    def _daily_scan(self):
        if self.is_warming_up:
            return

        # Phase 1: Check exits
        for etf in self.etf_list:
            if self.positions[etf] == 0:
                continue

            symbol = self.symbols[etf]
            hist = self.history(symbol, self.exit_period + 1, Resolution.DAILY)
            if hist.empty or len(hist) < self.exit_period + 1:
                continue

            lows = hist['low'].values
            current_price = self.securities[symbol].price
            exit_low = np.min(lows[:-1])

            if current_price < exit_low:
                self.liquidate(symbol)
                self.positions[etf] = 0
                self.log(f"EXIT {etf} at {current_price:.2f}")

        # Phase 2: Check entries
        candidates = []
        for etf in self.etf_list:
            if self.positions[etf] == 1:
                continue

            symbol = self.symbols[etf]
            hist = self.history(symbol, self.entry_period + 1, Resolution.DAILY)
            if hist.empty or len(hist) < self.entry_period + 1:
                continue

            highs = hist['high'].values
            current_price = self.securities[symbol].price
            entry_high = np.max(highs[:-1])

            if current_price > entry_high:
                momentum = current_price / entry_high - 1
                candidates.append((etf, momentum))

        candidates.sort(key=lambda x: x[1], reverse=True)
        current_count = sum(self.positions.values())
        available = self.max_positions - current_count

        for etf, mom in candidates[:available]:
            symbol = self.symbols[etf]
            self.set_holdings(symbol, self.trend_weight)
            self.positions[etf] = 1
            self.log(f"LONG {etf} at {self.securities[symbol].price:.2f}, mom={mom:.3f}")

        # Phase 3: Adjust SPY parking
        active_count = sum(self.positions.values())
        if active_count > 0:
            spy_target = self.spy_core
        else:
            spy_target = self.spy_full

        current_spy = self.portfolio[self.spy].holdings_value / self.portfolio.total_portfolio_value if self.portfolio.total_portfolio_value > 0 else 0
        if abs(current_spy - spy_target) > 0.05:
            self.set_holdings(self.spy, spy_target)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"TREND v3.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
