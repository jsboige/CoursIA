# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class ShortTermMeanReversion(QCAlgorithm):
    """
    Long-Only Mean Reversion Strategy v2 (RSI)

    Achete les actions survendues (RSI < 30) du S&P 500.
    Long-only pour eviter le short-squeeze en bull market.
    Rebalancement hebdomadaire. SPY SMA200 filter.

    Ref: Jegadeesh (1990), De Bondt & Thaler (1985)
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_cash(100000)

        # Parametres
        self.num_coarse = 100
        self.num_long = 10
        self.rsi_period = 14
        self.rsi_oversold = 35
        self.lookback_days = 5

        # SPY regime filter
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.spy_sma = self.sma(self.spy, 200, Resolution.DAILY)

        self.universe_settings.resolution = Resolution.DAILY
        self.add_universe(self.coarse_selection)

        # Rebalancement hebdomadaire (lundi)
        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.after_market_open("SPY", 30),
            self._rebalance
        )

        self.rsi_indicators = {}
        self.set_benchmark("SPY")
        self.set_warm_up(200, Resolution.DAILY)

    def coarse_selection(self, coarse):
        filtered = [x for x in coarse
                    if x.price > 10
                    and x.dollar_volume > 5000000
                    and x.has_fundamental_data]

        sorted_by_volume = sorted(filtered,
                                  key=lambda x: x.dollar_volume,
                                  reverse=True)[:self.num_coarse]
        return [x.symbol for x in sorted_by_volume]

    def on_securities_changed(self, changes):
        for security in changes.added_securities:
            symbol = security.symbol
            if symbol not in self.rsi_indicators:
                self.rsi_indicators[symbol] = self.rsi(symbol, self.rsi_period)

        for security in changes.removed_securities:
            symbol = security.symbol
            if symbol in self.rsi_indicators:
                self.rsi_indicators.pop(symbol, None)
            if self.portfolio[symbol].invested:
                self.liquidate(symbol)

    def _rebalance(self):
        if self.is_warming_up:
            return

        # SPY regime filter: cash if below SMA200
        if self.spy_sma.is_ready:
            spy_below_sma = self.securities[self.spy].price < self.spy_sma.current.value
            if spy_below_sma:
                if self.portfolio.invested:
                    self.liquidate()
                    self.log("RISK OFF: SPY < SMA200")
                return

        # Find oversold stocks
        oversold = []
        for symbol, rsi in self.rsi_indicators.items():
            if not rsi.is_ready:
                continue
            if not self.securities.contains_key(symbol):
                continue
            if self.securities[symbol].price <= 0:
                continue

            rsi_value = rsi.current.value
            if rsi_value < self.rsi_oversold:
                history = self.history(symbol, self.lookback_days + 1, Resolution.DAILY)
                if len(history) < 2:
                    continue
                try:
                    ret_5d = (history['close'].iloc[-1] / history['close'].iloc[0]) - 1
                    # Lower RSI + bigger drop = stronger signal
                    score = rsi_value + ret_5d * 100
                    oversold.append((symbol, score))
                except:
                    continue

        # Sort by score (lowest = most oversold)
        oversold.sort(key=lambda x: x[1])
        selected = [s for s, _ in oversold[:self.num_long]]

        # Liquidate non-selected
        for kvp in self.portfolio:
            if kvp.value.invested and kvp.key not in selected and kvp.key != self.spy:
                self.liquidate(kvp.key)

        if len(selected) == 0:
            return

        # Equal weight long positions
        weight = 0.9 / len(selected)  # 90% invested, 10% cash buffer
        for symbol in selected:
            self.set_holdings(symbol, weight)

        self.log(f"MEAN REV v2: {len(selected)} long positions")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"MEAN REVERSION v2: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
