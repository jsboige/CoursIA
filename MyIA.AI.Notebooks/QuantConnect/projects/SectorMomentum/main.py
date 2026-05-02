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

        self.set_benchmark("SPY")
        self.set_warm_up(timedelta(self.max_lookback + 30))

    def _composite_momentum(self, symbol, current_price):
        history = self.history(symbol, self.max_lookback, Resolution.DAILY)
        if len(history) < self.max_lookback:
            return None
        score = 0.0
        for window, weight in zip(self.lookback_windows, self.lookback_weights):
            past_price = history['close'].iloc[-window]
            if past_price > 0:
                momentum = (current_price / past_price) - 1
                score += weight * momentum
        return score

    def _rotate_defensive(self, tlt_score, gld_score):
        self.liquidate(self.spy)
        if tlt_score >= gld_score:
            self.set_holdings(self.tlt, 1.0)
            self.liquidate(self.gld)
            self.log(f"[RISK OFF] TLT={tlt_score:.3f} > GLD={gld_score:.3f}")
        else:
            self.liquidate(self.tlt)
            self.set_holdings(self.gld, 1.0)
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
        self.rebalance_month = self.time.month

        spy_score = self._composite_momentum(self.spy, spy_price)
        tlt_score = self._composite_momentum(self.tlt, tlt_price)
        gld_score = self._composite_momentum(self.gld, gld_price)

        if spy_score is None or tlt_score is None or gld_score is None:
            return

        if spy_score > 0 and spy_above_sma and spy_score > max(tlt_score, gld_score):
            self.set_holdings(self.spy, 1.0)
            self.liquidate(self.tlt)
            self.liquidate(self.gld)
            self.in_spy = True
            self.log(f"[RISK ON] SPY={spy_score:.3f}")
        else:
            self._rotate_defensive(tlt_score, gld_score)
