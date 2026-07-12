from AlgorithmImports import *


class TrendStocksAlpha(AlphaModel):
    """
    Alpha Model: Trend Stocks Lite signal with momentum weighting.

    Per stock: Price > SMA200 AND EMA20 > EMA50 -> UP insight.
    Otherwise -> FLAT insight (exit position).

    v1.3: Momentum-weighted insights. Bullish stocks are weighted by
    their 3-month rate of change (stronger uptrend = larger allocation)
    instead of equal weight. This lets the PCM's weight-hint branch
    allocate proportionally to momentum strength.

    Monthly emission.
    """

    def __init__(self, tickers):
        super().__init__()
        self.name = "TrendStocks"
        self.tickers = tickers
        self.sma200 = {}
        self.ema20 = {}
        self.ema50 = {}
        self.roc63 = {}  # 3-month momentum
        self.symbols = {}
        self._last_month = -1

    def update(self, algorithm, data):
        # Monthly emission (first trading day of month)
        if algorithm.time.month == self._last_month:
            return []
        self._last_month = algorithm.time.month

        if algorithm.is_warming_up:
            return []

        # First pass: identify bullish stocks and their momentum
        bullish = []
        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            sma = self.sma200.get(ticker)
            e20 = self.ema20.get(ticker)
            e50 = self.ema50.get(ticker)
            roc = self.roc63.get(ticker)

            if sma is None or not sma.is_ready:
                continue
            if e20 is None or not e20.is_ready:
                continue
            if e50 is None or not e50.is_ready:
                continue

            price = algorithm.securities[symbol].price
            if price <= 0:
                continue

            in_uptrend = (
                price > sma.current.value
                and e20.current.value > e50.current.value
            )

            if in_uptrend:
                mom = roc.current.value if (roc and roc.is_ready) else 0
                bullish.append((ticker, symbol, max(mom, 0.001)))

        # Compute normalized momentum weights
        total_mom = sum(m for _, _, m in bullish)
        mom_weights = {}
        if total_mom > 0:
            for ticker, symbol, mom in bullish:
                mom_weights[ticker] = mom / total_mom

        # Second pass: emit insights
        insights = []
        period = timedelta(days=31)
        bullish_tickers = set(t for t, _, _ in bullish)

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue
            if not all(
                ind is not None and ind.is_ready
                for ind in [self.sma200.get(ticker), self.ema20.get(ticker), self.ema50.get(ticker)]
            ):
                continue
            price = algorithm.securities[symbol].price
            if price <= 0:
                continue

            if ticker in bullish_tickers:
                w = mom_weights.get(ticker, 1.0 / max(len(bullish), 1))
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    weight=w,
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
                sym = security.symbol
                self.symbols[ticker] = sym
                self.sma200[ticker] = algorithm.sma(sym, 200, Resolution.DAILY)
                self.ema20[ticker] = algorithm.ema(sym, 20, Resolution.DAILY)
                self.ema50[ticker] = algorithm.ema(sym, 50, Resolution.DAILY)
                self.roc63[ticker] = algorithm.roc(sym, 63, Resolution.DAILY)


class AllWeatherAlpha(AlphaModel):
    """
    Alpha Model: All Weather static allocation signal.

    Always emits UP insights for SPY/IEF/GLD/XLP with weight hints
    matching the target allocation (30/30/30/10).
    Monthly emission (low turnover strategy).
    """

    def __init__(self, tickers):
        super().__init__()
        self.name = "AllWeather"
        self.tickers = tickers
        self.target_weights = {
            "SPY": 0.30,
            "IEF": 0.30,
            "GLD": 0.30,
            "XLP": 0.10,
        }
        self.symbols = {}
        self._last_month = -1

    def update(self, algorithm, data):
        # Monthly emission (first trading day of month)
        if algorithm.time.month == self._last_month:
            return []
        self._last_month = algorithm.time.month

        if algorithm.is_warming_up:
            return []

        insights = []
        period = timedelta(days=31)

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            price = algorithm.securities[symbol].price
            if price <= 0:
                continue

            weight = self.target_weights.get(ticker, 0)
            insights.append(Insight.price(
                symbol, period, InsightDirection.UP,
                weight=weight,
                source_model=self.name
            ))

        return insights

    def on_securities_changed(self, algorithm, changes):
        for security in changes.added_securities:
            ticker = security.symbol.value
            if ticker in self.tickers:
                self.symbols[ticker] = security.symbol
