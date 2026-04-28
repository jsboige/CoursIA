from AlgorithmImports import *
import numpy as np


class ValueAlpha(AlphaModel):
    """
    Value Factor Alpha: Book-to-price and earnings yield.

    Signal: Composite score from book-to-market ratio and earnings yield.
    Quarterly rebalance (fundamentals change slowly).
    Uses fundamental data via FineFundamental.
    """

    def __init__(self):
        super().__init__()
        self.name = "Value"
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

        cache = getattr(algorithm, 'fundamental_cache', {})

        for kvp in algorithm.active_securities:
            security = kvp.value
            symbol = security.symbol

            fund = cache.get(symbol)
            if fund is None:
                continue

            pb = fund.get('price_to_book')
            if pb is None or pb <= 0:
                continue
            book_to_market = 1.0 / pb

            pe = fund.get('price_to_earnings')
            if pe is None or pe <= 0:
                continue
            earnings_yield = 1.0 / pe

            scores[symbol] = book_to_market * 0.6 + earnings_yield * 0.4

        if not scores:
            return []

        # Long top quartile by value score
        sorted_symbols = sorted(scores.items(), key=lambda x: x[1], reverse=True)
        n_long = max(1, len(sorted_symbols) // 4)

        long_set = set(s for s, _ in sorted_symbols[:n_long])

        for symbol, score in scores.items():
            if symbol in long_set:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    magnitude=score,
                    source_model=self.name
                ))
            else:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.FLAT,
                    source_model=self.name
                ))

        return insights


class QualityAlpha(AlphaModel):
    """
    Quality Factor Alpha: ROE + debt-to-equity filter.

    Signal: High ROE with low leverage. Quarterly rebalance.
    """

    def __init__(self):
        super().__init__()
        self.name = "Quality"
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

        cache = getattr(algorithm, 'fundamental_cache', {})

        for kvp in algorithm.active_securities:
            security = kvp.value
            symbol = security.symbol

            fund = cache.get(symbol)
            if fund is None:
                continue

            roe = fund.get('return_on_equity')
            if roe is None or roe <= 0:
                continue

            de = fund.get('debt_to_equity')
            if de is None:
                continue

            quality_score = roe / (1 + abs(de))
            scores[symbol] = quality_score

        if not scores:
            return []

        sorted_symbols = sorted(scores.items(), key=lambda x: x[1], reverse=True)
        n_long = max(1, len(sorted_symbols) // 4)
        long_set = set(s for s, _ in sorted_symbols[:n_long])

        for symbol, score in scores.items():
            if symbol in long_set:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    magnitude=score,
                    source_model=self.name
                ))
            else:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.FLAT,
                    source_model=self.name
                ))

        return insights


class LowVolAlpha(AlphaModel):
    """
    Low Volatility Factor Alpha: Minimum variance selection.

    Signal: Select stocks with lowest 1-year realized volatility.
    Monthly rebalance.
    """

    def __init__(self):
        super().__init__()
        self.name = "LowVol"
        self._last_month = -1

    def update(self, algorithm, data):
        if algorithm.time.month == self._last_month:
            return []
        self._last_month = algorithm.time.month
        if algorithm.is_warming_up:
            return []

        insights = []
        period = timedelta(days=31)
        vols = {}

        for kvp in algorithm.active_securities:
            security = kvp.value
            symbol = security.symbol

            try:
                history = algorithm.history(symbol, 252, Resolution.DAILY)
                if len(history) < 60:
                    continue
                daily_ret = history['close'].pct_change().dropna()
                vol = daily_ret.std() * np.sqrt(252)
                if vol > 0:
                    vols[symbol] = vol
            except:
                continue

        if not vols:
            return []

        # Select bottom quartile by volatility (lowest vol)
        sorted_vols = sorted(vols.items(), key=lambda x: x[1])
        n_long = max(1, len(sorted_vols) // 4)
        long_set = set(s for s, _ in sorted_vols[:n_long])

        for symbol, vol in vols.items():
            if symbol in long_set:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    magnitude=1.0 / vol,
                    source_model=self.name
                ))
            else:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.FLAT,
                    source_model=self.name
                ))

        return insights


class MomentumFactorAlpha(AlphaModel):
    """
    Momentum Factor Alpha: 12m-1m return ranking.

    Signal: Classic Jegadeesh-Titman momentum (12m skip 1m).
    Long top decile, rebalance monthly.
    """

    def __init__(self):
        super().__init__()
        self.name = "MomFactor"
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

        for kvp in algorithm.active_securities:
            security = kvp.value
            symbol = security.symbol

            try:
                history = algorithm.history(symbol, 252, Resolution.DAILY)
                if len(history) < 252:
                    continue
                closes = history['close']
                mom = (closes.iloc[-21] / closes.iloc[0]) - 1
                returns[symbol] = mom
            except:
                continue

        if not returns:
            return []

        sorted_rets = sorted(returns.items(), key=lambda x: x[1], reverse=True)
        n_long = max(1, len(sorted_rets) // 4)
        long_set = set(s for s, _ in sorted_rets[:n_long])

        for symbol, ret in returns.items():
            if symbol in long_set:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    magnitude=ret,
                    source_model=self.name
                ))
            else:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.FLAT,
                    source_model=self.name
                ))

        return insights
