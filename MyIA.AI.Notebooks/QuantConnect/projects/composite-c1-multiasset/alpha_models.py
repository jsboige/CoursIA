from AlgorithmImports import *
import numpy as np


class MomentumAlpha(AlphaModel):
    """
    Momentum Alpha: 12m-1m risk-adjusted momentum with trend filter.

    Signal: (12m return - 1m recent) / 63d realized vol.
    Only long when price > SMA200 (trend confirmation).
    Monthly emission.
    """

    def __init__(self, tickers):
        super().__init__()
        self.name = "Momentum"
        self.tickers = tickers
        self.lookback = 252
        self.skip_days = 21
        self.vol_window = 63
        self.symbols = {}
        self.sma200 = {}
        self._last_month = -1

    def update(self, algorithm, data):
        if algorithm.time.month == self._last_month:
            return []
        self._last_month = algorithm.time.month
        if algorithm.is_warming_up:
            return []

        insights = []
        period = timedelta(days=31)
        scores = {}

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue
            score = self._compute_score(algorithm, symbol, ticker)
            if score is not None:
                scores[ticker] = score

        if not scores:
            return []

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue
            score = scores.get(ticker)
            if score is not None and score > 0:
                sma = self.sma200.get(ticker)
                price = algorithm.securities[symbol].price
                if sma and sma.is_ready and price > sma.current.value:
                    insights.append(Insight.price(
                        symbol, period, InsightDirection.UP,
                        magnitude=score,
                        source_model=self.name
                    ))
                    continue
            insights.append(Insight.price(
                symbol, period, InsightDirection.FLAT,
                source_model=self.name
            ))

        return insights

    def _compute_score(self, algorithm, symbol, ticker):
        try:
            history = algorithm.history(symbol, self.lookback + 5, Resolution.DAILY)
            if len(history) < self.lookback:
                return None
            closes = history['close']
            mom = (closes.iloc[-self.skip_days] / closes.iloc[0]) - 1
            vol = closes.iloc[-self.vol_window:].pct_change().std() * np.sqrt(252)
            if vol <= 0:
                return None
            return mom / vol
        except:
            return None

    def on_securities_changed(self, algorithm, changes):
        for security in changes.added_securities:
            ticker = security.symbol.value
            if ticker in self.tickers:
                sym = security.symbol
                self.symbols[ticker] = sym
                self.sma200[ticker] = algorithm.SMA(sym, 200, Resolution.DAILY)


class MACDAlpha(AlphaModel):
    """
    MACD Trend Alpha: MACD(12,26,9) crossover signal.

    Signal: Long when MACD > signal line (bullish crossover).
    Weekly emission for more responsive trend detection.
    """

    def __init__(self, tickers):
        super().__init__()
        self.name = "MACD"
        self.tickers = tickers
        self.symbols = {}
        self.macd = {}
        self._last_week = -1

    def update(self, algorithm, data):
        week = algorithm.time.isocalendar()[1]
        if week == self._last_week:
            return []
        self._last_week = week
        if algorithm.is_warming_up:
            return []

        insights = []
        period = timedelta(days=7)

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue
            macd_ind = self.macd.get(ticker)
            if macd_ind is None or not macd_ind.is_ready:
                continue

            macd_val = macd_ind.current.value
            # MACD > 0 means bullish momentum
            if macd_val > 0:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    magnitude=abs(macd_val),
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
                self.macd[ticker] = algorithm.MACD(
                    sym, 12, 26, 9,
                    MovingAverageType.EXPONENTIAL,
                    Resolution.DAILY
                )


class RelativeStrengthAlpha(AlphaModel):
    """
    Relative Strength Alpha: Compare 3-month returns across assets.

    Signal: Long top 2 assets by relative strength (3m return).
    Short/bottom assets get FLAT. Monthly emission.
    """

    def __init__(self, tickers):
        super().__init__()
        self.name = "RelStrength"
        self.tickers = tickers
        self.symbols = {}
        self._last_month = -1

    def update(self, algorithm, data):
        if algorithm.time.month == self._last_month:
            return []
        self._last_month = algorithm.time.month
        if algorithm.is_warming_up:
            return []

        insights = []
        period = timedelta(days=31)
        returns = {}

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue
            try:
                history = algorithm.history(symbol, 63, Resolution.DAILY)
                if len(history) < 20:
                    continue
                closes = history['close']
                ret = (closes.iloc[-1] / closes.iloc[0]) - 1
                returns[ticker] = ret
            except:
                continue

        if not returns:
            return []

        # Rank by return, long top half
        sorted_rets = sorted(returns.items(), key=lambda x: x[1], reverse=True)
        n_long = max(1, len(sorted_rets) // 2)
        long_set = set(t for t, _ in sorted_rets[:n_long])

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue
            if ticker in long_set and returns.get(ticker, 0) > 0:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    magnitude=returns[ticker],
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


class MeanReversionAlpha(AlphaModel):
    """
    Mean Reversion Alpha: Buy oversold assets within the ETF universe.

    Signal: Long assets that dropped >10% in 3 months (oversold bounce).
    Contrarian signal that diversifies from momentum-based models.
    Monthly emission.
    """

    def __init__(self, tickers):
        super().__init__()
        self.name = "MeanReversion"
        self.tickers = tickers
        self.symbols = {}
        self.sma200 = {}
        self._last_month = -1

    def update(self, algorithm, data):
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
            sma = self.sma200.get(ticker)
            if sma is None or not sma.is_ready:
                continue

            try:
                history = algorithm.history(symbol, 63, Resolution.DAILY)
                if len(history) < 30:
                    continue
                closes = history['close']
                ret_3m = (closes.iloc[-1] / closes.iloc[0]) - 1
                price = algorithm.securities[symbol].price

                # Mean reversion: buy oversold (down >10%) but still above SMA200
                if ret_3m < -0.10 and price > sma.current.value:
                    insights.append(Insight.price(
                        symbol, period, InsightDirection.UP,
                        magnitude=abs(ret_3m),
                        source_model=self.name
                    ))
                else:
                    insights.append(Insight.price(
                        symbol, period, InsightDirection.FLAT,
                        source_model=self.name
                    ))
            except:
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
                self.sma200[ticker] = algorithm.SMA(sym, 200, Resolution.DAILY)
