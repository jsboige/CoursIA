# region imports
from AlgorithmImports import *
# endregion


class TrendFollowingAQR(QCAlgorithm):
    """
    Trend Following Multi-Asset v7 (BEST)
    ======================================
    v7: Sharpe 0.577, CAGR 11.52%, MaxDD 15.3% (safe haven + mom tilt) BEST
    v8: Sharpe 0.566, CAGR 10.38%, MaxDD 16.5% (regime + risk parity - worse)
    v9: Sharpe 0.535, CAGR 10.29%, MaxDD 14.6% (regime only - worse)

    Dual signal: SMA(200) + 6m momentum confirmation.
    12m return tilt for weighting (rank-based).

    Ref: Antonacci (2014), AQR Trend Following
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
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

        self.spy_sym = self.symbols["SPY"]
        self.spy_sma = self.sma(self.spy_sym, 200, Resolution.DAILY)

        self.mom_lookback_6m = 126
        self.mom_lookback_12m = 252
        self.min_trending = 2
        self.bear_risky_cap = 0.50

        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance,
        )

        self.set_warm_up(timedelta(days=300))

    def rebalance(self):
        if self.is_warming_up:
            return

        bear_market = False
        if self.spy_sma.is_ready:
            spy_price = self.securities[self.spy_sym].price
            bear_market = spy_price < self.spy_sma.current.value

        trending = {}
        for ticker in self.risky_tickers:
            ind = self.sma_ind[ticker]
            if not ind.is_ready:
                continue
            sma_val = ind.current.value
            close = self.securities[self.symbols[ticker]].close
            if close <= sma_val:
                continue
            hist_6m = self.history(self.symbols[ticker], self.mom_lookback_6m + 5, Resolution.DAILY)
            if len(hist_6m) < self.mom_lookback_6m * 0.8:
                continue
            ret_6m = hist_6m["close"].iloc[-1] / hist_6m["close"].iloc[-self.mom_lookback_6m] - 1
            if ret_6m <= 0:
                continue
            hist_12m = self.history(self.symbols[ticker], self.mom_lookback_12m + 5, Resolution.DAILY)
            if len(hist_12m) < self.mom_lookback_12m * 0.8:
                ret_12m = ret_6m
            else:
                ret_12m = hist_12m["close"].iloc[-1] / hist_12m["close"].iloc[-self.mom_lookback_12m] - 1
            trending[ticker] = ret_12m

        targets = {}
        if len(trending) >= self.min_trending:
            sorted_trending = sorted(trending.items(), key=lambda x: x[1], reverse=True)
            n = len(sorted_trending)
            raw_weights = []
            for i, (ticker, ret) in enumerate(sorted_trending):
                rank_score = (n - i) / n
                raw_weights.append((ticker, rank_score))
            total = sum(w for _, w in raw_weights)
            risky_alloc = self.bear_risky_cap if bear_market else 1.0
            for ticker, w in raw_weights:
                targets[ticker] = (w / total) * risky_alloc
            if bear_market:
                targets[self.safe_ticker] = 1.0 - risky_alloc
        elif len(trending) > 0:
            risky_weight = len(trending) * 0.25
            if bear_market:
                risky_weight = min(risky_weight, self.bear_risky_cap)
            per_asset = risky_weight / len(trending)
            for ticker in trending:
                targets[ticker] = per_asset
            targets[self.safe_ticker] = 1.0 - risky_weight
        else:
            targets[self.safe_ticker] = 1.0

        regime = "BEAR" if bear_market else "BULL"
        trending_str = ", ".join(f"{t}:{r:.1%}" for t, r in sorted(trending.items(), key=lambda x: -x[1]))
        self.log(f"{regime} | Trending ({len(trending)}/{len(self.risky_tickers)}): [{trending_str}]")

        for ticker in self.all_tickers:
            sym = self.symbols[ticker]
            if ticker in targets:
                self.set_holdings(sym, targets[ticker])
            elif self.portfolio[sym].invested:
                self.liquidate(sym)

    def on_data(self, data: Slice):
        pass
