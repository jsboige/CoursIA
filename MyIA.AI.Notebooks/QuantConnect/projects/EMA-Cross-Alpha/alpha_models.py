from AlgorithmImports import *


class EMACrossAlpha(AlphaModel):
    """EMA Crossover Alpha Model.

    Generates UP insights when EMA fast > EMA slow, FLAT otherwise.
    Uses explicit ticker filtering (no algorithm.securities iteration).

    Parameters:
    - tickers: List of tickers to trade
    - fast_period: Fast EMA period (default 20)
    - slow_period: Slow EMA period (default 50)
    """

    def __init__(self, tickers, fast_period=20, slow_period=50):
        super().__init__()
        self.name = "EMACross"
        self.tickers = tickers
        self.fast_period = fast_period
        self.slow_period = slow_period
        self._ema_fast = {}
        self._ema_slow = {}
        self.symbols = {}

    def update(self, algorithm, data):
        if algorithm.is_warming_up:
            return []

        insights = []
        period = timedelta(days=1)

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            fast = self._ema_fast.get(ticker)
            slow = self._ema_slow.get(ticker)
            if not fast or not slow or not fast.is_ready or not slow.is_ready:
                continue

            if fast.current.value > slow.current.value:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    source_model=self.name
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
                self._ema_fast[ticker] = algorithm.ema(security.symbol, self.fast_period, Resolution.DAILY)
                self._ema_slow[ticker] = algorithm.ema(security.symbol, self.slow_period, Resolution.DAILY)
