from AlgorithmImports import *
import numpy as np


class AdaptiveAssetAllocationAlpha(AlphaModel):
    """Alpha Model: Adaptive Asset Allocation.

    Combines momentum ranking with minimum-variance optimization.
    Monthly emission, on the first slice of the month that carries a bar.

    Every ticker receives an insight at each emission: UP with its weight for
    the assets held, FLAT with weight 0 for the others. Clipping the negative
    minimum-variance weights can zero a selected asset, so the strategy holds
    between 1 and top_n lines, like the standalone version.

    Based on AdaptiveAssetAllocation iter2c standalone.
    Reference: Butler, Philbrick, Gordillo (SSRN 2328254)
    """

    def __init__(self, tickers, lookback_momentum=126, lookback_vol=60,
                 lookback_corr=126, top_n=4, insight_bars=30):
        super().__init__()
        self.name = "AdaptiveAA"
        self.tickers = tickers
        self.lookback_momentum = lookback_momentum
        self.lookback_vol = lookback_vol
        self.lookback_corr = lookback_corr
        self.top_n = top_n
        # Lean counts a timedelta period in bars of the data resolution: with
        # daily data, 30 days are 30 sessions, about six weeks. Each emission
        # replaces the previous insight of every ticker, so the period only has
        # to outlast the gap between two monthly emissions (at most 23 sessions).
        self.insight_bars = insight_bars
        self.symbols = {}
        self._last_month = -1

    def update(self, algorithm, data):
        if algorithm.is_warming_up:
            return []

        month = algorithm.time.month
        if month == self._last_month:
            return []
        # A dividend notice arrives alone in a midnight slice, with no bar (#20264):
        # it must not consume the month's emission.
        if not any(data.bars.contains_key(s) for s in self.symbols.values()):
            return []
        self._last_month = month

        # On the 13:00 close slice of a US half-session, a daily history request
        # by bar count comes back about 21 bars short (measured in #20286). Ask
        # for twice the bars; the frame below keeps the most recent ones.
        bars = max(self.lookback_momentum, self.lookback_corr) + 5
        history = algorithm.history(
            list(self.symbols.values()), 2 * bars, Resolution.DAILY
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

        price_df = pd.DataFrame(prices).dropna().iloc[-bars:]
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

        period = timedelta(days=self.insight_bars)
        held = {t: float(w) for t, w in zip(top_assets, weights) if w > 0}
        insights = []

        # A FLAT insight carries weight=0: InsightWeightingPortfolioConstructionModel
        # drops insights without a weight, so a FLAT without one would leave the
        # previous UP target in place and the line would never be sold (#20264).
        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue
            if ticker in held:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    weight=held[ticker], source_model=self.name
                ))
            else:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.FLAT,
                    weight=0, source_model=self.name
                ))

        return insights

    def on_securities_changed(self, algorithm, changes):
        for security in changes.added_securities:
            ticker = security.symbol.value
            if ticker in self.tickers:
                self.symbols[ticker] = security.symbol
