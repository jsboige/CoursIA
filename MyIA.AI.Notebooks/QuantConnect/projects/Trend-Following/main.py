# region imports
from AlgorithmImports import *
# endregion


class TrendFollowingAQR(QCAlgorithm):
    """
    Trend Following Multi-Asset v6 (Safe Haven) (BEST)
    ==================================================
    Best variant: Sharpe 0.542, CAGR 10.42%, MaxDD 17.2%

    Dual signal: SMA(200) + 6m momentum confirmation.
    BND safe haven: when <2 trending assets, put remainder in BND.

    Iteration results:
    v4: Sharpe 0.373, CAGR 8.46%, MaxDD 22.0% (equal weight)
    v5: Sharpe 0.357, CAGR 8.16%, MaxDD 22.5% (risk parity - worse)
    v6: Sharpe 0.542, CAGR 10.42%, MaxDD 17.2% (BND safe haven) <-- BEST

    Ref: Antonacci (2014), AQR Trend Following
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100_000)
        self.set_benchmark("SPY")

        self.risky_tickers = ["SPY", "EFA", "EEM", "TLT", "GLD", "DBC"]
        self.safe_ticker = "BND"
        self.all_tickers = self.risky_tickers + [self.safe_ticker]
        self.symbols = {}
        self.sma_ind = {}

        for ticker in self.risky_tickers:
            security = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = security.symbol
            self.sma_ind[ticker] = self.sma(security.symbol, 200, Resolution.DAILY)

        safe = self.add_equity(self.safe_ticker, Resolution.DAILY)
        self.symbols[self.safe_ticker] = safe.symbol

        self.mom_lookback = 126
        self.min_trending = 2

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
        for ticker in self.risky_tickers:
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

        targets = {}
        if len(trending) >= self.min_trending:
            weight = 1.0 / len(trending)
            for ticker in trending:
                targets[ticker] = weight
        elif len(trending) > 0:
            risky_weight = len(trending) * 0.25
            per_asset = risky_weight / len(trending)
            for ticker in trending:
                targets[ticker] = per_asset
            targets[self.safe_ticker] = 1.0 - risky_weight
        else:
            targets[self.safe_ticker] = 1.0

        trending_str = ", ".join(trending) if trending else "none"
        self.log(f"Trending ({len(trending)}/{len(self.risky_tickers)}): [{trending_str}]")

        for ticker in self.all_tickers:
            sym = self.symbols[ticker]
            if ticker in targets:
                self.set_holdings(sym, targets[ticker])
            elif self.portfolio[sym].invested:
                self.liquidate(sym)

    def on_data(self, data: Slice):
        pass
