# region imports
from AlgorithmImports import *
# endregion

class SectorDualMomentumStrategy(QCAlgorithm):
    """
    Enhanced Dual Momentum (Antonacci + Faber improvements):
    - Multi-lookback: composite score from 1, 3, 6, 12 months
    - 3 assets: SPY (risk-on), TLT (bonds), GLD (gold)
    - SMA200 regime filter on SPY
    - Monthly rebalancing
    - Rotates into best-performing defensive asset when risk-off
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # Assets
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.tlt = self.add_equity("TLT", Resolution.DAILY).symbol
        self.gld = self.add_equity("GLD", Resolution.DAILY).symbol

        # Multi-lookback windows (trading days)
        self.lookback_windows = [21, 63, 126, 252]  # 1, 3, 6, 12 months
        self.max_lookback = max(self.lookback_windows)

        # SMA200 regime filter
        self.spy_sma = self.SMA(self.spy, 200, Resolution.DAILY)

        # Monthly rebalancing
        self.rebalance_month = -1

        self.set_benchmark("SPY")
        self.set_warm_up(timedelta(self.max_lookback + 30))

    def _composite_momentum(self, symbol, current_price):
        """Calculate weighted composite momentum across multiple lookbacks."""
        history = self.history(symbol, self.max_lookback, Resolution.DAILY)
        if len(history) < self.max_lookback:
            return None

        weights = [0.4, 0.2, 0.2, 0.2]  # More weight on recent (1m)
        score = 0.0
        for window, weight in zip(self.lookback_windows, weights):
            past_price = history['close'].iloc[-window]
            momentum = (current_price / past_price) - 1
            score += weight * momentum
        return score

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not self.spy_sma.is_ready:
            return

        # Monthly rebalancing
        if self.time.month == self.rebalance_month:
            return
        self.rebalance_month = self.time.month

        # Current prices
        spy_price = self.securities[self.spy].price
        tlt_price = self.securities[self.tlt].price
        gld_price = self.securities[self.gld].price

        # Composite momentum scores
        spy_score = self._composite_momentum(self.spy, spy_price)
        tlt_score = self._composite_momentum(self.tlt, tlt_price)
        gld_score = self._composite_momentum(self.gld, gld_price)

        if spy_score is None or tlt_score is None or gld_score is None:
            return

        # SMA200 regime filter
        spy_above_sma = spy_price > self.spy_sma.current.value

        # Decision logic
        if spy_score > 0 and spy_above_sma and spy_score > max(tlt_score, gld_score):
            # Risk-on: SPY has positive momentum, above SMA200, and best performer
            self.set_holdings(self.spy, 1.0)
            self.liquidate(self.tlt)
            self.liquidate(self.gld)
            self.log(f"[RISK ON] SPY score={spy_score:.3f}, SMA200 OK -> SPY")
        else:
            # Risk-off: rotate into best defensive asset
            self.liquidate(self.spy)
            if tlt_score >= gld_score:
                self.set_holdings(self.tlt, 1.0)
                self.liquidate(self.gld)
                self.log(f"[RISK OFF] TLT={tlt_score:.3f} > GLD={gld_score:.3f} -> TLT")
            else:
                self.liquidate(self.tlt)
                self.set_holdings(self.gld, 1.0)
                self.log(f"[RISK OFF] GLD={gld_score:.3f} > TLT={tlt_score:.3f} -> GLD")
