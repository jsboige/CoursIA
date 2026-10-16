# [ARCHIVED - Sharpe ceiling ~0.56, cf ARCHIVE.md]
# region imports
from AlgorithmImports import *
# endregion


class SectorDualMomentumStrategy(QCAlgorithm):
    """
    Dual Momentum v3.2 - CONFIRMED BEST

    Iteration history:
    v2:   Sharpe 0.554, CAGR 13.1%, MaxDD 23.0%
    v3.2: Sharpe 0.555, CAGR 13.0%, MaxDD 22.8% (BEST)
    v4.0: Sharpe 0.307 REJECTED (expanded risk-on SPY+QQQ+IWM)
    v4.1: Sharpe 0.263 REJECTED (proportional portfolio)
    v4.2: Sharpe 0.376 REJECTED (classic GEM with tactical hedge)

    Conclusion: Sharpe ceiling ~0.56 for dual momentum on 3-5 assets.
    Target of 0.8 requires fundamentally different approach.

    - Multi-lookback composite (1,3,6,12m, weights 0.4,0.2,0.2,0.2)
    - 3 assets: SPY (risk-on), TLT (bonds), GLD (gold)
    - Daily SMA200 exit protection (intra-month)
    - Monthly rebalance for entries
    Ref: Antonacci (2014), Faber (2007)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.tlt = self.add_equity("TLT", Resolution.DAILY).symbol
        self.gld = self.add_equity("GLD", Resolution.DAILY).symbol

        self.lookback_windows = [21, 63, 126, 252]
        self.max_lookback = max(self.lookback_windows)
        self.lookback_weights = [0.4, 0.2, 0.2, 0.2]

        self.spy_sma = self.SMA(self.spy, 200, Resolution.DAILY)
        self.rebalance_month = -1
        self.in_spy = False
        self._refused = 0

        self.set_benchmark("SPY")
        self.set_warm_up(timedelta(self.max_lookback + 30))

    def _composite_momentum(self, symbol, current_price):
        # On the 13:00 close slice of a US half-session, a daily history request
        # by bar count comes back about 21 bars short (measured in #20286). Ask
        # for twice the bars and keep the most recent ones.
        history = self.history(symbol, 2 * self.max_lookback, Resolution.DAILY)
        history = history.iloc[-self.max_lookback:]
        if len(history) < self.max_lookback:
            return None
        score = 0.0
        for window, weight in zip(self.lookback_windows, self.lookback_weights):
            past_price = history['close'].iloc[-window]
            if past_price > 0:
                momentum = (current_price / past_price) - 1
                score += weight * momentum
        return score

    def _rotate_to(self, target):
        # Hold `target` alone at 98 % of the portfolio. At daily resolution every
        # order becomes MarketOnOpen, and a buy is checked for buying power twice:
        # when it is sent, and again at the next open, in the order the orders
        # were sent. At a 100 % target the buy was refused about one month in ten
        # (#20388): checked at the open against the old position, not yet sold,
        # or already at sending time, short by less than 1 % of the margin it
        # required. The quantity is computed before any sell, as set_holdings
        # did, the sells go out first, and the 2 % left in cash covers the check
        # at sending time.
        quantity = self.calculate_order_quantity(target, 0.98)
        for symbol in (self.spy, self.tlt, self.gld):
            if symbol != target:
                self.liquidate(symbol)
        if quantity != 0:
            self.market_order(target, quantity)

    def _rotate_defensive(self, tlt_score, gld_score):
        if tlt_score >= gld_score:
            self._rotate_to(self.tlt)
            self.log(f"[RISK OFF] TLT={tlt_score:.3f} > GLD={gld_score:.3f}")
        else:
            self._rotate_to(self.gld)
            self.log(f"[RISK OFF] GLD={gld_score:.3f} > TLT={tlt_score:.3f}")
        self.in_spy = False

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not self.spy_sma.is_ready:
            return

        spy_price = self.securities[self.spy].price
        tlt_price = self.securities[self.tlt].price
        gld_price = self.securities[self.gld].price
        if spy_price <= 0 or tlt_price <= 0 or gld_price <= 0:
            return

        spy_above_sma = spy_price > self.spy_sma.current.value

        # Daily exit: if holding SPY and SMA200 breaks
        if self.in_spy and not spy_above_sma:
            tlt_score = self._composite_momentum(self.tlt, tlt_price)
            gld_score = self._composite_momentum(self.gld, gld_price)
            if tlt_score is not None and gld_score is not None:
                self._rotate_defensive(tlt_score, gld_score)
                self.log("[SMA200 EXIT] SPY broke SMA200 intra-month")
                return

        # Monthly rebalance
        if self.time.month == self.rebalance_month:
            return
        # A dividend notice arrives alone in a midnight slice, with no bar (#20264):
        # it must not consume the month's rebalance.
        if not any(data.bars.contains_key(s) for s in (self.spy, self.tlt, self.gld)):
            return
        self.rebalance_month = self.time.month

        spy_score = self._composite_momentum(self.spy, spy_price)
        tlt_score = self._composite_momentum(self.tlt, tlt_price)
        gld_score = self._composite_momentum(self.gld, gld_price)

        if spy_score is None or tlt_score is None or gld_score is None:
            return

        if spy_score > 0 and spy_above_sma and spy_score > max(tlt_score, gld_score):
            self._rotate_to(self.spy)
            self.in_spy = True
            self.log(f"[RISK ON] SPY={spy_score:.3f}")
        else:
            self._rotate_defensive(tlt_score, gld_score)

    def on_order_event(self, order_event):
        if order_event.status == OrderStatus.INVALID:
            self._refused += 1
            self.log(f"REFUSED {order_event.symbol.value} {order_event.quantity:.0f}")

    def on_end_of_algorithm(self):
        self.log(f"done refused={self._refused}")
