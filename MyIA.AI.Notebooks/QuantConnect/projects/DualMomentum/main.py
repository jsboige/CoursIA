# region imports
from AlgorithmImports import *
# endregion


class DualMomentum(QCAlgorithm):
    """
    Dual Momentum v6b: All Candidates + Momentum Tilt (BEST)
    ========================================================
    Best variant: Sharpe 0.557, CAGR 11.22%, MaxDD 15.3%

    Universe (risky): SPY, EFA, EEM, TLT, GLD, DBC
    Safe refuge: BND
    Absolute filter: price > SMA200 AND 6m return > 0
    Relative ranking: 12m return, ALL candidates, momentum-tilt weighted
    Rebalance: Monthly

    Iteration results:
    v4: Sharpe 0.391, CAGR 9.15%, MaxDD 23.9% (Core5, top-2, equal)
    v5: Sharpe 0.526, CAGR 11.31%, MaxDD 19.0% (+DBC, top-3, weighted)
    v6: Sharpe 0.473, CAGR 9.42%, MaxDD 16.4% (defensive 80/20 - worse Sharpe)
    v6b: Sharpe 0.557, CAGR 11.22%, MaxDD 15.3% (all candidates, mom tilt) <-- BEST

    Reference: Antonacci (2014) + AQR Trend Following
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

        self.lookback_12m = 252
        self.lookback_6m = 126
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

        candidates = {}
        for ticker in self.risky_tickers:
            ind = self.sma_ind[ticker]
            if not ind.is_ready:
                continue
            sym = self.symbols[ticker]
            close = self.securities[sym].close
            if close <= ind.current.value:
                continue
            hist_12m = self.history(sym, self.lookback_12m + 5, Resolution.DAILY)
            if len(hist_12m) < self.lookback_12m * 0.8:
                continue
            ret_12m = hist_12m["close"].iloc[-1] / hist_12m["close"].iloc[-self.lookback_12m] - 1
            hist_6m = self.history(sym, self.lookback_6m + 5, Resolution.DAILY)
            if len(hist_6m) < self.lookback_6m * 0.8:
                continue
            ret_6m = hist_6m["close"].iloc[-1] / hist_6m["close"].iloc[-self.lookback_6m] - 1
            if ret_6m > 0:
                candidates[ticker] = ret_12m

        sorted_assets = sorted(candidates.items(), key=lambda x: x[1], reverse=True)

        targets = {}
        if len(sorted_assets) >= self.min_trending:
            n = len(sorted_assets)
            raw_weights = []
            for i, (ticker, ret) in enumerate(sorted_assets):
                rank_score = (n - i) / n
                raw_weights.append((ticker, rank_score))
            total = sum(w for _, w in raw_weights)
            for ticker, w in raw_weights:
                targets[ticker] = w / total
        elif len(sorted_assets) > 0:
            risky_weight = len(sorted_assets) * 0.25
            per_asset = risky_weight / len(sorted_assets)
            for ticker, _ in sorted_assets:
                targets[ticker] = per_asset
            targets[self.safe_ticker] = 1.0 - risky_weight
        else:
            targets[self.safe_ticker] = 1.0

        passing_str = ", ".join(f"{t}:{r:.1%}" for t, r in sorted_assets[:6])
        self.log(f"Trending ({len(candidates)}/{len(self.risky_tickers)}): [{passing_str}]")

        for ticker in self.all_tickers:
            sym = self.symbols[ticker]
            if ticker in targets:
                self.set_holdings(sym, targets[ticker])
            elif self.portfolio[sym].invested:
                self.liquidate(sym)

    def on_data(self, data: Slice):
        pass
