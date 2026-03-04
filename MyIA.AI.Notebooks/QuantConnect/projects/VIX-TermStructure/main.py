# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class VIXTermStructureStrategy(QCAlgorithm):
    """
    VIX Term Structure Strategy v4.0 - SPY Parking + Tighter Threshold

    Key innovation: SPY parking eliminates cash drag.
    Instead of sitting in cash when VIX too high, invest in SPY.
    Tighter VIX threshold (20 vs 22) for higher-quality SVXY entries.

    History:
    v2.0: Sharpe -0.97, Net -8.95%, MaxDD 20.8% (SVXY+VIXY hybrid)
    v3.0: Sharpe -0.35, Net -15.3%, MaxDD 26.4% (SPY filter)
    v3.1: Sharpe -0.27, Net -5.94%, MaxDD 28.0% (SVXY-only, cash)
    v4.0: Sharpe +0.086, Net +42.36%, MaxDD 35.3% (SPY parking)
    v4.1: Sharpe +0.094, Net +39.08%, MaxDD 37.5% (70% SVXY, worse)

    Note: Alpha is negative (-0.06), meaning we underperform SPY.
    SVXY contango premium post-2018 (0.5x leverage) is fundamentally small.
    This is near the strategy's ceiling given structural constraints.

    Ref: Simon & Campasano (2014), research.ipynb H7
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_cash(100000)

        self.vix = self.add_data(CBOE, "VIX", Resolution.DAILY).symbol
        self.svxy = self.add_equity("SVXY", Resolution.DAILY).symbol
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol

        self.vix_sma = self.sma(self.vix, 10, Resolution.DAILY)

        # Strategy parameters
        self.vix_threshold = 20     # Enter SVXY only when VIX < 20
        self.vix_exit = 28          # Force exit SVXY when VIX > 28
        self.stop_pct = 0.12        # 12% trailing stop on SVXY
        self.svxy_size = 0.50       # 50% SVXY position
        self.spy_size = 0.95        # 95% SPY when parking
        self.reentry_delay = 10     # Days to wait after stop-out

        self.trailing_high = 0
        self.days_since_stop = 999

        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 60),
            self._trade
        )

        self.set_benchmark("SPY")
        self.set_warm_up(30, Resolution.DAILY)

    def _trade(self):
        if self.is_warming_up:
            return
        if not self.vix_sma.is_ready:
            return

        vix_price = self.securities[self.vix].price
        if vix_price <= 0:
            return
        svxy_price = self.securities[self.svxy].price
        if svxy_price <= 0:
            return

        vix_ma10 = self.vix_sma.current.value

        # Trailing stop on SVXY
        if self.portfolio[self.svxy].invested:
            if svxy_price > self.trailing_high:
                self.trailing_high = svxy_price
            stop_price = self.trailing_high * (1 - self.stop_pct)
            if svxy_price < stop_price:
                self.liquidate(self.svxy)
                self.days_since_stop = 0
                self.trailing_high = 0
                self.set_holdings(self.spy, self.spy_size)
                self.log(f"STOP->SPY: SVXY={svxy_price:.2f}, VIX={vix_price:.1f}")
                return

        self.days_since_stop += 1

        # VIX force exit
        if self.portfolio[self.svxy].invested and vix_price > self.vix_exit:
            self.liquidate(self.svxy)
            self.trailing_high = 0
            self.set_holdings(self.spy, self.spy_size)
            self.log(f"VIX EXIT->SPY: VIX={vix_price:.1f}")
            return

        # SVXY entry
        vix_calm = vix_price < self.vix_threshold
        vix_declining = vix_price < vix_ma10
        no_recent_stop = self.days_since_stop > self.reentry_delay

        if vix_calm and vix_declining and no_recent_stop and not self.portfolio[self.svxy].invested:
            if self.portfolio[self.spy].invested:
                self.liquidate(self.spy)
            self.set_holdings(self.svxy, self.svxy_size)
            self.trailing_high = svxy_price
            self.log(f"SPY->SVXY: SVXY={svxy_price:.2f}, VIX={vix_price:.1f}")

        elif self.portfolio[self.svxy].invested and vix_price > self.vix_threshold:
            self.liquidate(self.svxy)
            self.trailing_high = 0
            self.set_holdings(self.spy, self.spy_size)
            self.log(f"SVXY->SPY: VIX={vix_price:.1f} > {self.vix_threshold}")

        elif not self.portfolio[self.svxy].invested and not self.portfolio[self.spy].invested:
            self.set_holdings(self.spy, self.spy_size)
            self.log(f"SAFETY->SPY")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"VIX v4.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
