from AlgorithmImports import *


class DualMomentumAlpha(AlphaModel):
    """Alpha Model: Dual Momentum No TLT.

    Multi-asset momentum rotation without long-duration bonds.
    Monthly emission.

    Rules:
    - Absolute momentum: 12M return > 0
    - Relative momentum: top 2 by 12M return
    - Cash (FLAT all) if nothing passes absolute filter

    Based on DualMomentumNoTLT standalone.
    Reference: Antonacci (2012)
    """

    def __init__(self, tickers, lookback=252, num_holdings=2):
        super().__init__()
        self.name = "DualMomentum"
        self.tickers = tickers
        self.lookback = lookback
        self.num_holdings = num_holdings
        self.symbols = {}
        self._last_month = -1

    def update(self, algorithm, data):
        if algorithm.is_warming_up:
            return []

        month = algorithm.time.month
        if month == self._last_month:
            return []
        self._last_month = month

        # Compute 12M momentum for each asset
        scores = {}
        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue
            history = algorithm.history(
                symbol, self.lookback + 5, Resolution.DAILY
            )
            if len(history) < self.lookback:
                continue
            closes = history['close']
            mom_12m = (closes.iloc[-1] / closes.iloc[-self.lookback]) - 1
            scores[ticker] = mom_12m

        if not scores:
            return []

        period = timedelta(days=30)
        insights = []

        # Absolute momentum filter
        passing = {t: s for t, s in scores.items() if s > 0}

        if not passing:
            # All negative: cash
            for ticker in self.tickers:
                symbol = self.symbols.get(ticker)
                if symbol is None:
                    continue
                insights.append(Insight.price(
                    symbol, period, InsightDirection.FLAT,
                    source_model=self.name
                ))
            return insights

        # Relative momentum: top N
        sorted_assets = sorted(
            passing.items(), key=lambda x: x[1], reverse=True
        )
        selected = [t for t, s in sorted_assets[:self.num_holdings]]
        weight = 1.0 / len(selected)

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue
            if ticker in selected:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    weight=weight, source_model=self.name
                ))
            else:
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
