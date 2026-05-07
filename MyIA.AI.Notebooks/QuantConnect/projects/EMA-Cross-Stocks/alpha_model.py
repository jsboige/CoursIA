from AlgorithmImports import *


class EMACrossAlpha(AlphaModel):
    """
    Alpha Model: EMA Crossover on multi-stock universe.

    Emits UP when EMA fast > EMA slow, FLAT otherwise.
    Equal weight among bullish stocks (max 5 positions).

    Based on EMA-Cross-Stocks/main.py (Sharpe 0.872 standalone).
    Daily emission.
    """

    def __init__(self, tickers, fast_period=20, slow_period=50):
        super().__init__()
        self.name = "EMACross"
        self.tickers = tickers
        self.fast_period = fast_period
        self.slow_period = slow_period
        self.symbols = {}
        self.ema_fast = {}
        self.ema_slow = {}
        self._last_day = None

    def update(self, algorithm, data):
        # Daily emission
        today = algorithm.time.date()
        if self._last_day == today:
            return []
        self._last_day = today

        if algorithm.is_warming_up:
            return []

        period = timedelta(days=1)
        insights = []
        bullish_tickers = []

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            ef = self.ema_fast.get(ticker)
            es = self.ema_slow.get(ticker)
            if ef is None or es is None:
                continue
            if not ef.is_ready or not es.is_ready:
                continue

            if ef.current.value > es.current.value:
                bullish_tickers.append(ticker)

        # Equal weight among bullish
        weight = 0.95 / max(len(bullish_tickers), 1) if bullish_tickers else 0

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            ef = self.ema_fast.get(ticker)
            es = self.ema_slow.get(ticker)
            if ef is None or es is None:
                continue
            if not ef.is_ready or not es.is_ready:
                continue

            if ticker in bullish_tickers:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    weight=weight,
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
                self.ema_fast[ticker] = algorithm.ema(
                    security.symbol, self.fast_period, Resolution.DAILY
                )
                self.ema_slow[ticker] = algorithm.ema(
                    security.symbol, self.slow_period, Resolution.DAILY
                )
