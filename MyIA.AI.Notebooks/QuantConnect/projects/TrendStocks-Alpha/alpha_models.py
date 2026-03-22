from AlgorithmImports import *


class TrendStocksAlpha(AlphaModel):
    """Trend Stocks Alpha Model - Double confirmation trend following.

    Generates UP insights when Price > SMA200 AND EMA20 > EMA50.
    Uses explicit ticker filtering and weekly emission guard.
    """

    def __init__(self, tickers, ema_fast=20, ema_slow=50, sma_trend=200):
        super().__init__()
        self.name = "TrendStocks"
        self.tickers = tickers
        self.ema_fast_period = ema_fast
        self.ema_slow_period = ema_slow
        self.sma_trend_period = sma_trend
        self._ema_fast = {}
        self._ema_slow = {}
        self._sma_trend = {}
        self.symbols = {}
        self._last_week = -1

    def update(self, algorithm, data):
        if algorithm.is_warming_up:
            return []

        week = algorithm.time.isocalendar()[1]
        if week == self._last_week:
            return []
        self._last_week = week

        insights = []
        period = timedelta(days=7)

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            fast = self._ema_fast.get(ticker)
            slow = self._ema_slow.get(ticker)
            sma = self._sma_trend.get(ticker)
            if not fast or not slow or not sma:
                continue
            if not fast.is_ready or not slow.is_ready or not sma.is_ready:
                continue

            price = algorithm.securities[symbol].price
            if price <= 0:
                continue

            price_above_sma = price > sma.current.value
            ema_bullish = fast.current.value > slow.current.value

            if price_above_sma and ema_bullish:
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
                self._ema_fast[ticker] = algorithm.ema(security.symbol, self.ema_fast_period, Resolution.DAILY)
                self._ema_slow[ticker] = algorithm.ema(security.symbol, self.ema_slow_period, Resolution.DAILY)
                self._sma_trend[ticker] = algorithm.sma(security.symbol, self.sma_trend_period, Resolution.DAILY)
