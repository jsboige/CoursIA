# region imports
from AlgorithmImports import *
# endregion


class RiskParity(QCAlgorithm):
    """
    Risk Parity v4: Trend Filter + Rank-based Risk Parity + BND (BEST)
    ==================================================================
    Best variant: Sharpe 0.515, CAGR 10.04%, MaxDD 20.1%

    Combines inverse-volatility weighting with trend filtering.
    BND safe haven when <2 assets trending.

    Iteration results:
    v1: Sharpe 0.395, CAGR 7.84%, MaxDD 20.9% (baseline risk parity)
    v2: Sharpe 0.436, CAGR 8.64%, MaxDD 20.7% (+ trend filter + BND)
    v3: Sharpe 0.480, CAGR 9.26%, MaxDD 19.8% (+ momentum tilt)
    v4: Sharpe 0.515, CAGR 10.04%, MaxDD 20.1% (+ rank-based RP) <-- BEST
    v5: Sharpe 0.488, CAGR 10.03%, MaxDD 17.1% (equal RP - worse Sharpe)

    Reference: Asness/Frazzini 2012, Bridgewater Risk Parity
    """

    TICKERS = ["SPY", "EFA", "GLD", "DBC", "TLT"]
    SAFE_TICKER = "BND"
    VOL_LOOKBACK = 60
    MOM_LOOKBACK = 252
    WARMUP_DAYS = 280
    MIN_TRENDING = 2

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100_000)
        self.set_benchmark("SPY")

        self.all_tickers = self.TICKERS + [self.SAFE_TICKER]
        self.symbols = {}
        self.sma_ind = {}
        self.std_indicators = {}

        for ticker in self.TICKERS:
            security = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = security.symbol
            self.sma_ind[ticker] = self.sma(security.symbol, 200, Resolution.DAILY)
            self.std_indicators[ticker] = self.STD(security.symbol, self.VOL_LOOKBACK, Resolution.DAILY)

        safe = self.add_equity(self.SAFE_TICKER, Resolution.DAILY)
        self.symbols[self.SAFE_TICKER] = safe.symbol

        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance,
        )

        self.set_warm_up(timedelta(days=self.WARMUP_DAYS))

    def rebalance(self):
        if self.is_warming_up:
            return

        trending = {}
        for ticker in self.TICKERS:
            ind = self.sma_ind[ticker]
            if not ind.is_ready:
                continue
            sym = self.symbols[ticker]
            close = self.securities[sym].close
            if close <= ind.current.value:
                continue
            hist = self.history(sym, self.MOM_LOOKBACK + 5, Resolution.DAILY)
            if len(hist) < self.MOM_LOOKBACK * 0.8:
                continue
            ret_12m = hist["close"].iloc[-1] / hist["close"].iloc[-self.MOM_LOOKBACK] - 1

            std_ind = self.std_indicators[ticker]
            if not std_ind.is_ready:
                continue
            std_val = std_ind.current.value
            if close > 0 and std_val > 0:
                inv_vol = close / std_val
            else:
                inv_vol = 1.0

            trending[ticker] = (inv_vol, ret_12m)

        targets = {}
        if len(trending) >= self.MIN_TRENDING:
            sorted_trending = sorted(trending.items(), key=lambda x: x[1][1], reverse=True)
            n = len(sorted_trending)
            raw_weights = []
            for i, (ticker, (inv_vol, _)) in enumerate(sorted_trending):
                rank_score = (n - i) / n
                raw_weights.append((ticker, rank_score * inv_vol))
            total = sum(w for _, w in raw_weights)
            for ticker, w in raw_weights:
                targets[ticker] = w / total
        elif len(trending) > 0:
            risky_weight = len(trending) * 0.25
            per_asset = risky_weight / len(trending)
            for ticker in trending:
                targets[ticker] = per_asset
            targets[self.SAFE_TICKER] = 1.0 - risky_weight
        else:
            targets[self.SAFE_TICKER] = 1.0

        trending_str = ", ".join(
            f"{t}:{r:.1%}" for t, (_, r) in sorted(
                trending.items(), key=lambda x: x[1][1], reverse=True
            )
        )
        self.log(f"Trending ({len(trending)}/{len(self.TICKERS)}): [{trending_str}]")

        for ticker in self.all_tickers:
            sym = self.symbols[ticker]
            if ticker in targets:
                self.set_holdings(sym, targets[ticker])
            elif self.portfolio[sym].invested:
                self.liquidate(sym)

    def on_data(self, data: Slice):
        pass
