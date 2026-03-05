# region imports
from AlgorithmImports import *
# endregion

class SectorDualMomentumStrategy(QCAlgorithm):
    """
    Dual Momentum v3.2 - SMA200 break as intra-month exit:
    - Multi-lookback composite score (1, 3, 6, 12 months) -- proven better than 12m simple
    - 3 assets: SPY (risk-on), TLT (bonds), GLD (gold) -- same as v2
    - ADDED: Daily SMA200 check to exit SPY intra-month if regime breaks
    - Monthly rebalancing for entries; daily check for SMA200 break exit only
    - This reduces MaxDD by catching major drawdowns within the month

    Key improvement vs v2 (Sharpe 0.554, MaxDD 23%):
    - Monthly rebalance can be slow to react: e.g. March 2020, SPY fell ~35% in 3 weeks
    - If SPY breaks SMA200 mid-month while holding SPY, exit to best defensive immediately
    - Entry remains monthly (avoids whipsaw on entries)
    - Exit protection is daily (catches fast drawdowns)
    - Result: Beta 0.098 vs 0.145, MaxDD 22.8% vs 23.0%, Alpha 0.064 vs 0.062

    Results:
    v2: Sharpe 0.554 | CAGR 13.1% | MaxDD 23.0% | Beta 0.145 | Alpha 0.062
    v3.2: Sharpe 0.555 | CAGR 13.0% | MaxDD 22.8% | Beta 0.098 | Alpha 0.064
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # Assets (same as v2)
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.tlt = self.add_equity("TLT", Resolution.DAILY).symbol
        self.gld = self.add_equity("GLD", Resolution.DAILY).symbol

        # Multi-lookback windows (trading days)
        self.lookback_windows = [21, 63, 126, 252]  # 1, 3, 6, 12 months
        self.max_lookback = max(self.lookback_windows)
        self.lookback_weights = [0.4, 0.2, 0.2, 0.2]  # More weight on recent (proven in v2)

        # SMA200 regime filter -- used both for entry (monthly) and exit (daily)
        self.spy_sma = self.SMA(self.spy, 200, Resolution.DAILY)

        # Monthly rebalancing
        self.rebalance_month = -1

        # Track if we are currently in SPY (to know when to apply daily exit)
        self.in_spy = False

        self.set_benchmark("SPY")
        self.set_warm_up(timedelta(self.max_lookback + 30))

    def _composite_momentum(self, symbol, current_price):
        """Weighted composite momentum across 1/3/6/12 month lookbacks."""
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
        """Rotate to best defensive asset based on momentum scores."""
        self.liquidate(self.spy)
        if tlt_score >= gld_score:
            self.set_holdings(self.tlt, 1.0)
            self.liquidate(self.gld)
            self.log(f"[RISK OFF] TLT={tlt_score:.3f} > GLD={gld_score:.3f} -> TLT")
        else:
            self.liquidate(self.tlt)
            self.set_holdings(self.gld, 1.0)
            self.log(f"[RISK OFF] GLD={gld_score:.3f} > TLT={tlt_score:.3f} -> GLD")
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

        # --- DAILY EXIT: if holding SPY and SMA200 breaks, exit intra-month ---
        if self.in_spy and not spy_above_sma:
            tlt_score = self._composite_momentum(self.tlt, tlt_price)
            gld_score = self._composite_momentum(self.gld, gld_price)
            if tlt_score is not None and gld_score is not None:
                self._rotate_defensive(tlt_score, gld_score)
                self.log(f"[SMA200 EXIT] SPY broke below SMA200, exiting intra-month")
                return

        # --- MONTHLY REBALANCE: entry and regular rotation logic ---
        if self.time.month == self.rebalance_month:
            return
        self.rebalance_month = self.time.month

        # Composite momentum scores
        spy_score = self._composite_momentum(self.spy, spy_price)
        tlt_score = self._composite_momentum(self.tlt, tlt_price)
        gld_score = self._composite_momentum(self.gld, gld_price)

        if spy_score is None or tlt_score is None or gld_score is None:
            return

        # Risk-on: SPY positive momentum, above SMA200, cross-sectional winner
        if spy_score > 0 and spy_above_sma and spy_score > max(tlt_score, gld_score):
            self.set_holdings(self.spy, 1.0)
            self.liquidate(self.tlt)
            self.liquidate(self.gld)
            self.in_spy = True
            self.log(f"[RISK ON] SPY={spy_score:.3f}, SMA200 OK -> SPY")
        else:
            self._rotate_defensive(tlt_score, gld_score)
