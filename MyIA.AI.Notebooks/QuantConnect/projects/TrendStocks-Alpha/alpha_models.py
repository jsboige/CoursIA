# region imports
from AlgorithmImports import *
# endregion


class TrendStocksAlpha(AlphaModel):
    """Trend Stocks Alpha Model - Double confirmation trend following.

    Generates long insights when:
    1. Price > SMA200 (long-term trend confirmation)
    2. EMA20 > EMA50 (short-term momentum)

    Parameters:
    - ema_fast: Fast EMA period (default 20)
    - ema_slow: Slow EMA period (default 50)
    - sma_trend: Trend SMA period (default 200)
    - resolution: Data resolution (default DAILY)
    """

    def __init__(self, ema_fast=20, ema_slow=50, sma_trend=200, resolution=Resolution.DAILY):
        self.ema_fast_period = ema_fast
        self.ema_slow_period = ema_slow
        self.sma_trend_period = sma_trend
        self.resolution = resolution
        self._ema_fast = {}
        self._ema_slow = {}
        self._sma_trend = {}
        self._symbols = {}

    def update(self, algorithm, data):
        """Generate insights based on trend confirmation."""
        insights = []

        # Initialize indicators for new symbols
        for security in algorithm.securities.values():
            if security.type == SecurityType.EQUITY:
                sym = security.symbol
                if sym not in self._ema_fast:
                    self._symbols[sym] = sym
                    self._ema_fast[sym] = algorithm.ema(sym, self.ema_fast_period, self.resolution)
                    self._ema_slow[sym] = algorithm.ema(sym, self.ema_slow_period, self.resolution)
                    self._sma_trend[sym] = algorithm.sma(sym, self.sma_trend_period, self.resolution)

        # Check trend conditions for each symbol
        for sym, fast_ema in self._ema_fast.items():
            # Ensure all indicators are ready
            if not fast_ema.is_ready:
                continue

            slow_ema = self._ema_slow.get(sym)
            trend_sma = self._sma_trend.get(sym)
            if not slow_ema or not trend_sma or not slow_ema.is_ready or not trend_sma.is_ready:
                continue

            # Get current price
            security = algorithm.securities[sym]
            if security.price <= 0:
                continue

            price = security.price

            # Double confirmation needed
            price_above_sma = price > trend_sma.current.value
            ema_bullish = fast_ema.current.value > slow_ema.current.value

            if price_above_sma and ema_bullish:
                # Both conditions met - generate long insight
                # Magnitude based on distance above SMA
                magnitude = min((price - trend_sma.current.value) / trend_sma.current.value * 100, 1.0)

                insight = Insight.price(
                    sym,
                    timedelta(days=7),  # Weekly rebalance
                    InsightDirection.UP,
                    magnitude,
                    None
                )
                insights.append(insight)

        return insights

    def on_securities_changed(self, algorithm, changes):
        """Handle universe changes."""
        # Clean up removed securities
        for removed in changes.removed_securities:
            sym = removed.symbol
            if sym in self._ema_fast:
                del self._ema_fast[sym]
            if sym in self._ema_slow:
                del self._ema_slow[sym]
            if sym in self._sma_trend:
                del self._sma_trend[sym]
            if sym in self._symbols:
                del self._symbols[sym]
