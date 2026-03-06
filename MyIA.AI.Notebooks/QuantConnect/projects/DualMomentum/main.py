# region imports
from AlgorithmImports import *
# endregion


class DualMomentum(QCAlgorithm):
    """
    Dual Momentum Strategy (Gary Antonacci)
    =========================================
    Edge: Combine absolute momentum (time-series) and relative momentum (cross-section)
    Reference: "Dual Momentum Investing" (Antonacci, 2014)

    Mechanism:
    1. Relative momentum: Among risky assets (SPY, EFA), pick the best 12m performer
    2. Absolute momentum: If best performer 12m return > 0 -> stay in risky asset
                          If negative -> go to BND (bond refuge)

    Signal:
    - Monthly rebalance
    - 100% concentration in single chosen asset
    - No leverage, long-only

    Universe:
    - SPY: US equities (S&P 500) -- primary risky asset
    - EFA: International equities (MSCI EAFE) -- secondary risky asset
    - BND: Vanguard Total Bond ETF -- defensive refuge

    Backtest: 2015-2026
    Expected Sharpe: 0.3-0.5 on 2015-2026 (literature reports 0.7-1.0
    on longer periods starting 1970s; 2015-2026 has bull market headwinds)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100_000)
        self.set_benchmark("SPY")

        # Universe: risky assets and defensive refuge
        self.risky_assets = ["SPY", "EFA"]
        self.safe_asset = "BND"  # BND tested better than SHY on 2015-2026
        self.all_tickers = self.risky_assets + [self.safe_asset]

        # Add equities at daily resolution (sufficient for monthly rebalance)
        for ticker in self.all_tickers:
            self.add_equity(ticker, Resolution.DAILY)

        # Lookback: 12 months = ~252 trading days
        # Antonacci uses 12-month return -- academically the most robust period
        self.lookback_days = 252

        self.current_holding = None

        # Monthly rebalance: first trading day of each month
        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance
        )

        # Warm-up: 12 months of history needed
        self.set_warm_up(timedelta(days=self.lookback_days + 30))

    def rebalance(self):
        """
        Dual Momentum monthly rebalancing.

        Decision tree:
        1. Get 12m returns for SPY and EFA
        2. Pick the best (relative momentum)
        3. If best return > 0 (absolute momentum) -> invest in best
           Else -> go to BND (defensive)
        """
        if self.is_warming_up:
            return

        # Fetch 12-month price history for risky assets
        history = self.history(
            [self.symbol(t) for t in self.risky_assets],
            self.lookback_days,
            Resolution.DAILY
        )

        if history.empty:
            self.log("Rebalance: No history, skipping")
            return

        # Compute 12m returns
        returns = {}
        for ticker in self.risky_assets:
            sym = self.symbol(ticker)
            if sym in history.index.get_level_values("symbol"):
                prices = history.loc[sym]["close"]
                if len(prices) >= self.lookback_days * 0.8:
                    ret = (prices.iloc[-1] / prices.iloc[0]) - 1
                    returns[ticker] = ret
                    self.log(f"{ticker} 12m: {ret:.2%}")

        if not returns:
            self.log("No valid return data, skipping")
            return

        # Relative momentum: best risky asset
        best_risky = max(returns, key=returns.get)
        best_return = returns[best_risky]

        # Absolute momentum: is best risky > risk-free (0% proxy)?
        if best_return > 0:
            target = best_risky
        else:
            target = self.safe_asset

        self.log(
            f"Signal: best={best_risky}({best_return:.2%}) -> {target}"
            + (" [defensive]" if target == self.safe_asset else "")
        )

        # Execute only if position changes
        if self.current_holding != target:
            self.liquidate()
            self.set_holdings(target, 1.0)
            self.current_holding = target
            self.log(f"Rebalanced -> {target}")

    def on_data(self, data: Slice):
        """All logic handled by scheduled rebalance."""
        pass
