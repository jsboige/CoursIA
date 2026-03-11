# region imports
from AlgorithmImports import *
# endregion


class EMACrossAlpha(AlphaModel):
    """EMA Crossover Alpha Model.

    Generates long insights when EMA fast crosses above EMA slow.
    Flat signal (no insight) when EMA fast <= EMA slow.

    Parameters:
    - fast_period: Fast EMA period (default 20)
    - slow_period: Slow EMA period (default 50)
    - resolution: Data resolution (default DAILY)
    """

    def __init__(self, fast_period=20, slow_period=50, resolution=Resolution.DAILY):
        self.fast_period = fast_period
        self.slow_period = slow_period
        self.resolution = resolution
        self._ema_fast = {}
        self._ema_slow = {}
        self._symbols = {}

    def update(self, algorithm, data):
        """Generate insights based on EMA crossover."""
        insights = []

        # Initialize EMAs for new symbols
        for security in algorithm.securities.values():
            if security.type == SecurityType.EQUITY:
                sym = security.symbol
                if sym not in self._ema_fast:
                    self._symbols[sym] = sym
                    self._ema_fast[sym] = algorithm.ema(sym, self.fast_period, self.resolution)
                    self._ema_slow[sym] = algorithm.ema(sym, self.slow_period, self.resolution)

        # Check EMA crossover for each symbol
        for sym, fast_ema in self._ema_fast.items():
            if not fast_ema.is_ready:
                continue

            slow_ema = self._ema_slow[sym]
            if not slow_ema.is_ready:
                continue

            # Bullish signal: EMA fast > EMA slow
            if fast_ema.current.value > slow_ema.current.value:
                # Emit long insight with magnitude proportional to crossover strength
                fast = fast_ema.current.value
                slow = slow_ema.current.value
                magnitude = min(abs((fast - slow) / slow) * 100, 1.0)  # Cap at 1.0

                insight = Insight.price(
                    sym,
                    timedelta(days=1),  # Daily rebalance
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
            if sym in self._symbols:
                del self._symbols[sym]
