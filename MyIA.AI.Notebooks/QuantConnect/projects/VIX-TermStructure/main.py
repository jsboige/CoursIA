# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class VIXTermStructureStrategy(QCAlgorithm):
    """
    VIX Term Structure Strategy v2

    Exploite le contango de la courbe VIX via un ratio VIXY.
    - Contango persistant + VIX bas -> modeste short vol (SVXY)
    - Backwardation / VIX spike -> cash ou long vol (VIXY)
    - Risk management: trailing stop, max exposure, VIX ceiling

    Ref: Simon & Campasano (2014)
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_cash(100000)

        # VIX index
        self.vix = self.add_data(CBOE, "VIX", Resolution.DAILY).symbol

        # ETNs de volatilite
        self.vixy = self.add_equity("VIXY", Resolution.DAILY).symbol
        self.svxy = self.add_equity("SVXY", Resolution.DAILY).symbol
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # Indicateurs
        self.vix_sma_short = self.sma(self.vix, 5, Resolution.DAILY)
        self.vix_sma_long = self.sma(self.vix, 20, Resolution.DAILY)
        self.spy_sma = self.sma(self.spy, 200, Resolution.DAILY)

        # Rolling window pour le ratio VIXY (proxy contango)
        self.vixy_returns = RollingWindow[float](20)

        # Parametres de risque
        self.max_svxy_weight = 0.30   # Max 30% SVXY
        self.max_vixy_weight = 0.20   # Max 20% VIXY
        self.vix_ceiling = 25         # Pas de SVXY si VIX > 25
        self.vix_floor = 15           # VIX < 15 = contango fort

        # Tracking
        self.entry_price = 0
        self.trailing_stop = 0
        self.stop_pct = 0.08  # 8% trailing stop

        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 60),
            self._trade
        )

        self.set_benchmark("SPY")
        self.set_warm_up(30, Resolution.DAILY)

    def on_data(self, data):
        """Track VIXY daily returns for contango proxy."""
        if self.is_warming_up:
            return
        if data.contains_key(self.vixy) and self.securities[self.vixy].price > 0:
            history = self.history(self.vixy, 2, Resolution.DAILY)
            if len(history) >= 2:
                ret = (history['close'].iloc[-1] / history['close'].iloc[0]) - 1
                self.vixy_returns.add(ret)

    def _trade(self):
        if self.is_warming_up:
            return
        if not self.vix_sma_short.is_ready or not self.vix_sma_long.is_ready:
            return
        if not self.spy_sma.is_ready:
            return

        vix_price = self.securities[self.vix].price
        if vix_price <= 0:
            return

        vix_sma5 = self.vix_sma_short.current.value
        vix_sma20 = self.vix_sma_long.current.value
        spy_price = self.securities[self.spy].price
        spy_above_sma = spy_price > self.spy_sma.current.value

        # Contango proxy: VIXY losing value = roll yield negative = contango
        contango_signal = False
        if self.vixy_returns.is_ready:
            avg_vixy_ret = np.mean([self.vixy_returns[i] for i in range(self.vixy_returns.count)])
            contango_signal = avg_vixy_ret < -0.002  # VIXY declining ~0.2%/day

        # VIX regime
        vix_declining = vix_sma5 < vix_sma20
        vix_low = vix_price < self.vix_ceiling
        vix_very_low = vix_price < self.vix_floor

        # Check trailing stop on SVXY
        if self.portfolio[self.svxy].invested:
            svxy_price = self.securities[self.svxy].price
            if svxy_price > self.trailing_stop:
                self.trailing_stop = svxy_price * (1 - self.stop_pct)
            elif svxy_price < self.trailing_stop:
                self.liquidate(self.svxy)
                self.log(f"STOP HIT: SVXY at {svxy_price:.2f}, stop was {self.trailing_stop:.2f}")
                return

        # Decision
        if vix_low and contango_signal and vix_declining and spy_above_sma:
            # Contango favorable: modeste long SVXY
            weight = 0.15 if not vix_very_low else self.max_svxy_weight
            if not self.portfolio[self.svxy].invested:
                self.set_holdings(self.svxy, weight)
                self.entry_price = self.securities[self.svxy].price
                self.trailing_stop = self.entry_price * (1 - self.stop_pct)
                self.liquidate(self.vixy)
            self.log(f"CONTANGO: VIX={vix_price:.1f}, weight={weight:.0%}")

        elif vix_price > 30 or (not vix_declining and vix_price > self.vix_ceiling):
            # VIX spike: exit SVXY, modeste long VIXY
            if self.portfolio[self.svxy].invested:
                self.liquidate(self.svxy)
            weight = min(0.10, self.max_vixy_weight)
            self.set_holdings(self.vixy, weight)
            self.log(f"SPIKE: VIX={vix_price:.1f}, VIXY weight={weight:.0%}")

        elif not contango_signal or not spy_above_sma:
            # Conditions defavorables: cash
            if self.portfolio.invested:
                self.liquidate()
                self.log(f"CASH: VIX={vix_price:.1f}, no contango or SPY bearish")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"VIX TERM STRUCTURE v2: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
