from AlgorithmImports import *
import numpy as np


class AdaptiveAssetAllocationAlpha(AlphaModel):
    """Alpha Model: Adaptive Asset Allocation.

    Combines momentum ranking with minimum-variance optimization.
    Monthly emission.

    Based on AdaptiveAssetAllocation iter2c standalone.
    Reference: Butler, Philbrick, Gordillo (SSRN 2328254)
    """

    def __init__(self, tickers, lookback_momentum=126, lookback_vol=60,
                 lookback_corr=126, top_n=4):
        super().__init__()
        self.name = "AdaptiveAA"
        self.tickers = tickers
        self.lookback_momentum = lookback_momentum
        self.lookback_vol = lookback_vol
        self.lookback_corr = lookback_corr
        self.top_n = top_n
        self.symbols = {}
        self._last_month = -1

    def update(self, algorithm, data):
        if algorithm.is_warming_up:
            return []

        month = algorithm.time.month
        if month == self._last_month:
            return []
        self._last_month = month

        # Get historical prices
        history = algorithm.history(
            list(self.symbols.values()),
            max(self.lookback_momentum, self.lookback_corr) + 5,
            Resolution.DAILY
        )

        if history.empty:
            return []

        # Build price DataFrame
        prices = {}
        for ticker, symbol in self.symbols.items():
            try:
                prices[ticker] = history.loc[symbol]["close"]
            except (KeyError, TypeError):
                continue

        if len(prices) < self.top_n:
            return []

        price_df = pd.DataFrame(prices).dropna()
        if len(price_df) < self.lookback_momentum:
            return []

        # Step 1: Raw momentum ranking
        momentum = (
            price_df.iloc[-1] / price_df.iloc[-self.lookback_momentum] - 1
        )
        top_assets = momentum.nlargest(self.top_n).index.tolist()

        # Step 2: Minimum-variance weights
        returns = price_df[top_assets].pct_change().dropna()
        recent_returns = returns.iloc[-self.lookback_corr:]

        vol_returns = returns.iloc[-self.lookback_vol:]
        vols = vol_returns.std()
        corr = recent_returns.corr()

        n = len(top_assets)
        vol_diag = np.diag(vols.values)
        cov_matrix = vol_diag @ corr.values @ vol_diag

        try:
            cov_inv = np.linalg.inv(cov_matrix)
            ones = np.ones(n)
            raw_weights = cov_inv @ ones
            weights = raw_weights / raw_weights.sum()
            weights = np.maximum(weights, 0)
            if weights.sum() > 0:
                weights = weights / weights.sum()
            else:
                weights = np.ones(n) / n
        except np.linalg.LinAlgError:
            weights = np.ones(n) / n

        period = timedelta(days=30)
        insights = []

        for i, ticker in enumerate(top_assets):
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue
            insights.append(Insight.price(
                symbol, period, InsightDirection.UP,
                weight=float(weights[i]), source_model=self.name
            ))

        # FLAT for non-selected
        for ticker in self.tickers:
            if ticker not in top_assets:
                symbol = self.symbols.get(ticker)
                if symbol is None:
                    continue
                insights.append(Insight.price(
                    symbol, period, InsightDirection.FLAT,
                    source_model=self.name
                ))

        return insights

    def on_securities_changed(self, algorithm, changes):
        for security in changes.added_securities:
            ticker = security.symbol.value
            if ticker in self.tickers:
                self.symbols[ticker] = security.symbol
