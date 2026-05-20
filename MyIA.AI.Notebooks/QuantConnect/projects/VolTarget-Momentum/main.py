# region imports
from AlgorithmImports import *
# endregion


class VolTargetMomentum(QCAlgorithm):
    """
    VolTarget-Momentum v5: Wider leverage range + 15% target
    ===========================================================
    v1: Sharpe 0.550, CAGR 11.14%, MaxDD 15.1% (norm cancelled vol scalar)
    v2: Sharpe 0.614, CAGR 13.58%, MaxDD 17.9% (no norm, vol_target=15%)
    v3: Sharpe 0.585, CAGR 12.34%, MaxDD 16.6% (vol_target=12% - worse)
    v4: Sharpe 0.599, CAGR 13.53%, MaxDD 18.1% (forward-looking - worse)
    v5: Sharpe 0.651, CAGR 14.72%, MaxDD 21.2% (wider leverage 0.3-1.5)
    v6: Sharpe 0.652, CAGR 15.35%, MaxDD 21.3% (vol_target=18% - marginal)

    Reference: Antonacci (2014) + Bridgewater Vol Targeting
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

        # Volatility targeting parameters
        self.vol_target = 0.15  # 15% annualized target
        self.vol_lookback = 60  # 60-day realized vol
        self.max_leverage = 1.5  # max 150% exposure
        self.min_leverage = 0.3  # min 30% exposure

        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance,
        )

        self.set_warm_up(timedelta(days=280))

    def _get_portfolio_vol(self):
        """Estimate current portfolio volatility from holdings."""
        total_value = self.portfolio.total_portfolio_value
        if total_value <= 0:
            return self.vol_target

        weighted_var = 0.0
        for ticker in self.all_tickers:
            sym = self.symbols[ticker]
            holding = self.portfolio[sym]
            if not holding.invested:
                continue
            weight = holding.holdings_value / total_value
            hist = self.history(sym, self.vol_lookback + 5, Resolution.DAILY)
            if len(hist) < self.vol_lookback * 0.8:
                continue
            returns = hist["close"].pct_change().dropna().tail(self.vol_lookback)
            if len(returns) < 10:
                continue
            daily_var = float(returns.var())
            weighted_var += (weight ** 2) * daily_var

        if weighted_var <= 0:
            return self.vol_target

        return (weighted_var ** 0.5) * (252 ** 0.5)

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

        raw_targets = {}
        if len(sorted_assets) >= self.min_trending:
            n = len(sorted_assets)
            raw_weights = []
            for i, (ticker, ret) in enumerate(sorted_assets):
                rank_score = (n - i) / n
                raw_weights.append((ticker, rank_score))
            total = sum(w for _, w in raw_weights)
            for ticker, w in raw_weights:
                raw_targets[ticker] = w / total
        elif len(sorted_assets) > 0:
            risky_weight = len(sorted_assets) * 0.25
            per_asset = risky_weight / len(sorted_assets)
            for ticker, _ in sorted_assets:
                raw_targets[ticker] = per_asset
            raw_targets[self.safe_ticker] = 1.0 - risky_weight
        else:
            raw_targets[self.safe_ticker] = 1.0

        # Volatility targeting: estimate from holdings
        has_risky = any(t in raw_targets for t in self.risky_tickers)
        vol_scalar = 1.0
        current_vol = self.vol_target
        if has_risky:
            current_vol = self._get_portfolio_vol()
            if current_vol > 0.01:
                vol_scalar = self.vol_target / current_vol
                vol_scalar = max(self.min_leverage, min(self.max_leverage, vol_scalar))

        targets = {}
        for ticker, weight in raw_targets.items():
            if ticker == self.safe_ticker:
                if has_risky:
                    total_risky = sum(w for t, w in raw_targets.items() if t != self.safe_ticker)
                    targets[ticker] = max(0.0, 1.0 - total_risky * vol_scalar)
                else:
                    targets[ticker] = weight
            else:
                targets[ticker] = weight * vol_scalar

        regime = "BULL" if has_risky else "BEAR"
        vol_pct = f"{current_vol:.1%}" if has_risky else "N/A"
        tgt_str = ", ".join(f"{t}:{w:.1%}" for t, w in sorted(targets.items()))
        self.log(f"{regime} | vol={vol_pct} scalar={vol_scalar:.2f} | {tgt_str}")

        for ticker in self.all_tickers:
            sym = self.symbols[ticker]
            if ticker in targets:
                self.set_holdings(sym, targets[ticker])
            elif self.portfolio[sym].invested:
                self.liquidate(sym)

    def on_data(self, data: Slice):
        pass
