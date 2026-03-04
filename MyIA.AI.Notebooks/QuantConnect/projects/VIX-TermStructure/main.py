# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class VIXTermStructureStrategy(QCAlgorithm):
    """
    VIX Term Structure Strategy v3.1 - Simple Contango Harvesting

    Research-driven SVXY-only approach. No VIXY (permanent decay).
    No SPY filter (too restrictive in QC backtest).
    Long SVXY when VIX < 22 and declining. Cash otherwise.
    Trailing stop 12% for tail risk protection.
    Reentry delay 10 days after stop-out.

    Backtest results comparison:
    v2.0: Sharpe -0.97, Net -8.95%, MaxDD 20.8%
    v3.0: Sharpe -0.35, Net -15.3%, MaxDD 26.4% (with SPY filter)
    v3.1: Sharpe -0.27, Net -5.94%, MaxDD 28.0% (best)
    v3.2: Sharpe -0.30, Net -9.64%, MaxDD 26.5% (wider stop = worse)

    Note: VIX/SVXY strategy fundamentally limited post-2018 VIXplosion.
    SVXY changed from -1x to -0.5x leverage, halving contango premium.

    Ref: Simon & Campasano (2014), research.ipynb
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_cash(100000)

        # VIX index
        self.vix = self.add_data(CBOE, "VIX", Resolution.DAILY).symbol

        # SVXY only (no VIXY - research shows it always loses)
        self.svxy = self.add_equity("SVXY", Resolution.DAILY).symbol
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # Indicators
        self.vix_sma = self.sma(self.vix, 10, Resolution.DAILY)

        # Strategy parameters (from research notebook)
        self.vix_threshold = 22     # Enter only when VIX < 22
        self.vix_exit = 28          # Force exit when VIX > 28
        self.stop_pct = 0.12        # 12% trailing stop
        self.position_size = 0.50   # 50% position
        self.reentry_delay = 10     # Days to wait after stop-out

        # State tracking
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

        # Trailing stop check
        if self.portfolio[self.svxy].invested:
            if svxy_price > self.trailing_high:
                self.trailing_high = svxy_price
            stop_price = self.trailing_high * (1 - self.stop_pct)
            if svxy_price < stop_price:
                self.liquidate(self.svxy)
                self.days_since_stop = 0
                self.trailing_high = 0
                self.log(f"STOP: SVXY={svxy_price:.2f}, VIX={vix_price:.1f}")
                return

        self.days_since_stop += 1

        # VIX exit
        if self.portfolio[self.svxy].invested and vix_price > self.vix_exit:
            self.liquidate(self.svxy)
            self.trailing_high = 0
            self.log(f"VIX EXIT: VIX={vix_price:.1f}")
            return

        # Entry: VIX calm and declining (below its 10d MA)
        vix_calm = vix_price < self.vix_threshold
        vix_declining = vix_price < vix_ma10
        no_recent_stop = self.days_since_stop > self.reentry_delay

        if not self.portfolio[self.svxy].invested and vix_calm and vix_declining and no_recent_stop:
            self.set_holdings(self.svxy, self.position_size)
            self.trailing_high = svxy_price
            self.log(f"ENTER: SVXY={svxy_price:.2f}, VIX={vix_price:.1f}")

        elif self.portfolio[self.svxy].invested and vix_price > self.vix_threshold:
            # Exit if VIX rises above threshold
            self.liquidate(self.svxy)
            self.trailing_high = 0
            self.log(f"EXIT: VIX={vix_price:.1f} > {self.vix_threshold}")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"VIX v3.1: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
