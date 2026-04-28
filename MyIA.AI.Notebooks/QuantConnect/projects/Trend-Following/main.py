# region imports
from AlgorithmImports import *
# endregion


class TrendFollowingAQR(QCAlgorithm):
    """
    Trend Following Multi-Asset (AQR-style)
    ========================================
    Dual signal: SMA(200) + 6m momentum confirmation.
    Asset must be above SMA200 AND have positive 6m return.

    Universe: SPY, EFA, EEM, TLT, GLD, DBC
    Rebalance: Monthly, Allocation: 1/N among trending
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100_000)
        self.set_benchmark("SPY")

        self.tickers = ["SPY", "EFA", "EEM", "TLT", "GLD", "DBC"]
        self.symbols = {}
        self.sma_ind = {}

        for ticker in self.tickers:
            security = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = security.symbol
            self.sma_ind[ticker] = self.sma(security.symbol, 200, Resolution.DAILY)

        self.mom_lookback = 126

        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance,
        )

        self.set_warm_up(timedelta(days=280))

    def rebalance(self):
        if self.is_warming_up:
            return

        trending = []
        for ticker in self.tickers:
            ind = self.sma_ind[ticker]
            if not ind.is_ready:
                continue
            sma_val = ind.current.value
            close = self.securities[self.symbols[ticker]].close
            if close <= sma_val:
                continue
            history = self.history(self.symbols[ticker], self.mom_lookback, Resolution.DAILY)
            if len(history) < self.mom_lookback * 0.8:
                continue
            ret_6m = history["close"].iloc[-1] / history["close"].iloc[0] - 1
            if ret_6m > 0:
                trending.append(ticker)

        if not trending:
            self.liquidate()
            self.log("All flat: no trending assets")
            return

        weight = 1.0 / len(trending)
        self.log(f"Trending ({len(trending)}/{len(self.tickers)}): {trending}")

        for ticker in self.tickers:
            if ticker not in trending:
                if self.portfolio[self.symbols[ticker]].invested:
                    self.liquidate(self.symbols[ticker])

        for ticker in trending:
            self.set_holdings(self.symbols[ticker], weight)

    def on_data(self, data: Slice):
        pass
