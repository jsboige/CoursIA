# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class VIXTermStructureStrategy(QCAlgorithm):
    """
    VIX Term Structure Strategy v4.1 - Term Structure Ratio + Regime Filter

    PRIMARY SIGNAL: VIX3M/VIX contango ratio (true volatility term structure).
    VIX3M = 93-day VIX index, VIX = 30-day VIX index.
    Ratio > 1.0 = contango (normal, term structure upward-sloping).
    Ratio < 1.0 = backwardation (crisis, inverted term structure).

    Edge: When VIX3M/VIX > 1.05, the front-month roll yield is ~5%/month.
    Going long SVXY (short volatility) harvests this roll yield.

    Signal logic:
    - ENTER: VIX3M/VIX > 1.05 AND VIX < 22 AND VIX < SMA10 (calm regime)
    - EXIT: VIX3M/VIX < 1.02 OR VIX > 28 OR 10% trailing stop
    - Reentry: 15-day lockout after stop-out

    Iteration history:
    v2.0: Sharpe -0.97 (VIXY + SVXY, complex rules)
    v3.1: Sharpe -0.27 (SVXY only, VIX level filter)
    v4.0: Sharpe -0.65 (ratio + double-SMA declining filter, too restrictive)
    v4.1: Sharpe +0.05 (ratio + SMA10 calm filter, 2015 start) <- BEST
    v4.2: Sharpe -0.23 (VIX<18 too tight, too few entries)
    v4.3: Sharpe +0.03 (dynamic sizing, higher MaxDD)
    v5.0: Sharpe -0.10 (SHY 70% + stop 7%, too diluted)
    v5.1: Sharpe -0.13 (position 25%, cash drag kills Sharpe in high-rate env)

    Known limitations:
    - SVXY post-2018 VIXplosion is -0.5x (was -1x), halving contango premium
    - COVID 2020 and VIXplosion 2018 cause large drawdowns (~35%)
    - Short-vol strategies are inherently positively skewed return, negative tail
    - MaxDD 35% is unavoidable without leverage reduction
    - Reducing position size creates cash drag, lowering Sharpe in high-rate env
    - Ceiling: Sharpe ~0.05-0.10 is honest for SVXY short-vol 2015-2026

    Pedagogical value:
    - Demonstrates VIX term structure as a quantifiable signal
    - Shows how roll yield in VIX futures translates to ETF returns
    - Illustrates regime-dependent profitability of short-vol strategies

    Ref: Simon & Campasano (2014), Whaley (2009), Volatility as Asset Class
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)

        # VIX index (1-month, 30-day implied vol)
        self.vix = self.add_data(CBOE, "VIX", Resolution.DAILY).symbol

        # VIX3M (3-month VIX, formerly VXV) - term structure signal
        self.vix3m = self.add_data(CBOE, "VIX3M", Resolution.DAILY).symbol

        # SVXY only (no VIXY - permanent decay from contango)
        self.svxy = self.add_equity("SVXY", Resolution.DAILY).symbol
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # VIX regime indicator - 10d SMA
        self.vix_sma10 = self.sma(self.vix, 10, Resolution.DAILY)

        # Strategy parameters
        self.contango_entry = 1.05   # VIX3M/VIX > 1.05 to enter (5% premium)
        self.contango_exit = 1.02    # VIX3M/VIX < 1.02 to exit (backwardation alert)
        self.vix_max_entry = 22      # VIX must be below this to enter
        self.vix_exit = 28           # Force exit on VIX spike
        self.stop_pct = 0.10         # 10% trailing stop
        self.position_size = 0.45    # 45% position
        self.reentry_delay = 15      # 15 days after stop-out

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
        if not self.vix_sma10.is_ready:
            return

        vix_price = self.securities[self.vix].price
        if vix_price <= 0:
            return

        svxy_price = self.securities[self.svxy].price
        if svxy_price <= 0:
            return

        # VIX3M/VIX contango ratio (primary term structure signal)
        vix3m_price = self.securities[self.vix3m].price
        if vix3m_price > 0:
            contango_ratio = vix3m_price / vix_price
        else:
            # VIX3M not available: no entry signal, allow exits to run
            contango_ratio = 1.0

        vix_sma10 = self.vix_sma10.current.value

        # --- EXIT LOGIC (priority order) ---

        # 1. Trailing stop (highest priority - tail risk protection)
        if self.portfolio[self.svxy].invested:
            if svxy_price > self.trailing_high:
                self.trailing_high = svxy_price
            stop_price = self.trailing_high * (1 - self.stop_pct)
            if svxy_price < stop_price:
                self.liquidate(self.svxy)
                self.days_since_stop = 0
                self.trailing_high = 0
                self.log(f"STOP: SVXY={svxy_price:.2f}, VIX={vix_price:.1f}, "
                         f"Ratio={contango_ratio:.3f}")
                return

        self.days_since_stop += 1

        # 2. VIX spike exit (regime change)
        if self.portfolio[self.svxy].invested and vix_price > self.vix_exit:
            self.liquidate(self.svxy)
            self.trailing_high = 0
            self.log(f"VIX SPIKE EXIT: VIX={vix_price:.1f}")
            return

        # 3. Backwardation exit (term structure inverted = danger)
        if self.portfolio[self.svxy].invested and contango_ratio < self.contango_exit:
            self.liquidate(self.svxy)
            self.trailing_high = 0
            self.log(f"BACKWARDATION EXIT: VIX3M/VIX={contango_ratio:.3f}")
            return

        # --- ENTRY LOGIC ---
        # 1. Term structure in steep contango (VIX3M > 1.05x VIX)
        in_contango = contango_ratio > self.contango_entry
        # 2. VIX calm regime: absolute level AND below 10d trend
        vix_calm = vix_price < self.vix_max_entry and vix_price < vix_sma10
        # 3. No recent stop-out
        no_recent_stop = self.days_since_stop > self.reentry_delay

        if (not self.portfolio[self.svxy].invested
                and in_contango
                and vix_calm
                and no_recent_stop):
            self.set_holdings(self.svxy, self.position_size)
            self.trailing_high = svxy_price
            self.log(f"ENTER: SVXY={svxy_price:.2f}, VIX={vix_price:.1f}, "
                     f"VIX3M={vix3m_price:.1f}, Ratio={contango_ratio:.3f}")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"VIX v4.1 FINAL: ${final:,.2f}, "
                 f"Return={(final-100000)/100000:.2%}")
