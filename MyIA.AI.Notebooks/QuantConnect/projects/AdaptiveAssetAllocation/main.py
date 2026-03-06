# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class AdaptiveAssetAllocation(QCAlgorithm):
    """
    Adaptive Asset Allocation (Butler, Philbrick, Gordillo)
    ========================================================
    Edge: Combine momentum ranking with minimum-variance optimization
    Reference: "Adaptive Asset Allocation: A Primer" (SSRN 2328254)

    iter2c: Minimal changes from iter1 baseline
    - Vol window 60d (was 20d) for more stable covariance
    - Keep RAW momentum (risk-adj hurts when combined with min-var)
    - No skip-month, no absolute filter, no weight cap
    - Top 4 (was 5) to concentrate on best assets

    Universe: SPY, EFA, EEM, VNQ, GLD, DBC, TLT, IEF, TIP, HYG
    Backtest: 2008-2026
    """

    def initialize(self):
        self.set_start_date(2008, 1, 1)
        self.set_cash(100000)

        # Universe: 10 ETFs covering major asset classes
        self.tickers = ["SPY", "EFA", "EEM", "VNQ", "GLD",
                        "DBC", "TLT", "IEF", "TIP", "HYG"]

        self.symbols = {}
        for ticker in self.tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            equity.set_data_normalization_mode(DataNormalizationMode.ADJUSTED)
            self.symbols[ticker] = equity.symbol

        # Parameters
        self.lookback_momentum = 126      # 6 months momentum ranking
        self.lookback_vol = 60            # 60-day volatility for min-var (was 20)
        self.lookback_corr = 126          # 126-day correlation for min-var
        self.top_n = 4                    # Select top 4 assets (was 5)
        self.warmup_days = 252

        # Monthly rebalance on first trading day
        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance
        )

        self.set_warmup(self.warmup_days, Resolution.DAILY)

    def rebalance(self):
        if self.is_warming_up:
            return

        # Get historical prices
        history = self.history(
            list(self.symbols.values()),
            max(self.lookback_momentum, self.lookback_corr) + 5,
            Resolution.DAILY
        )

        if history.empty:
            return

        # Build price DataFrame
        prices = {}
        for ticker, symbol in self.symbols.items():
            try:
                prices[ticker] = history.loc[symbol]["close"]
            except (KeyError, TypeError):
                continue

        if len(prices) < self.top_n:
            return

        price_df = pd.DataFrame(prices).dropna()
        if len(price_df) < self.lookback_momentum:
            return

        # Step 1: Raw momentum ranking (6-month return)
        momentum = price_df.iloc[-1] / price_df.iloc[-self.lookback_momentum] - 1
        top_assets = momentum.nlargest(self.top_n).index.tolist()

        # Step 2: Minimum-variance weights
        returns = price_df[top_assets].pct_change().dropna()
        recent_returns = returns.iloc[-self.lookback_corr:]

        # Covariance: vol from 60-day window, correlation from 126-day
        vol_returns = returns.iloc[-self.lookback_vol:]
        vols = vol_returns.std()
        corr = recent_returns.corr()

        n = len(top_assets)
        vol_diag = np.diag(vols.values)
        cov_matrix = vol_diag @ corr.values @ vol_diag

        # Minimum variance: w = inv(cov) @ 1 / (1' @ inv(cov) @ 1)
        try:
            cov_inv = np.linalg.inv(cov_matrix)
            ones = np.ones(n)
            raw_weights = cov_inv @ ones
            weights = raw_weights / raw_weights.sum()

            # Enforce long-only: clip negatives, renormalize
            weights = np.maximum(weights, 0)
            if weights.sum() > 0:
                weights = weights / weights.sum()
            else:
                weights = np.ones(n) / n
        except np.linalg.LinAlgError:
            weights = np.ones(n) / n

        # Step 3: Apply weights
        target_holdings = {top_assets[i]: float(weights[i]) for i in range(n)}

        # Liquidate assets not in top N
        for ticker in self.tickers:
            if ticker not in top_assets and self.portfolio[self.symbols[ticker]].invested:
                self.liquidate(self.symbols[ticker])

        # Set target holdings
        for ticker, weight in target_holdings.items():
            self.set_holdings(self.symbols[ticker], weight)

    def on_data(self, data):
        pass
