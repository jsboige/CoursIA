from AlgorithmImports import *
import numpy as np


class FamaFrenchAlpha(AlphaModel):
    """
    Alpha Model: Fama-French Factor ETF Rotation signal.

    Emits UP insights for top-2 factor ETFs by risk-adjusted momentum.
    NO SMA200 filter - AllWeather handles defensive positioning.

    Factor ETFs (iShares): VLUE, MTUM, SIZE, QUAL, USMV
    - VLUE: Value factor
    - MTUM: Momentum factor
    - SIZE: Small-cap size factor
    - QUAL: Quality factor
    - USMV: Minimum volatility (defensive)

    Signal: Risk-adjusted momentum (12m-1m return / 63d realized vol)
    Reference: Barroso & Santa-Clara (2015), Daniel & Moskowitz (2016)

    Quarterly emission (aligns with factor rotation cycle).

    LESSON FROM MOMENTUMREGIME: NO SMA200 FILTER.
    - If all factors have negative momentum: emit FLAT for all
    - AllWeather will provide defensive allocation (IEF/GLD/XLP)
    """

    def __init__(self, tickers):
        super().__init__()
        self.name = "FamaFrench"
        self.tickers = tickers
        self.symbols = {}
        self.lookback = 252         # 12-month momentum window
        self.skip_days = 21         # Skip most recent month (reversal avoidance)
        self.vol_window = 63        # 3-month vol for risk adjustment
        self._last_month = -1

    def update(self, algorithm, data):
        # Monthly emission (aligns with AllWeather for proper combination)
        if algorithm.time.month == self._last_month:
            return []
        self._last_month = algorithm.time.month

        if algorithm.is_warming_up:
            return []

        # Calculate risk-adjusted momentum for each factor
        scores = {}
        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            score = self._risk_adjusted_momentum(algorithm, symbol)
            if score is not None:
                scores[ticker] = (symbol, score)

        if not scores:
            return []

        # Select top-2 by risk-adjusted momentum score
        sorted_factors = sorted(scores.items(), key=lambda x: x[1][1], reverse=True)
        top_2 = sorted_factors[:2]

        # Only select factors with positive momentum
        positive_factors = [(ticker, symbol, score) for ticker, (symbol, score) in top_2 if score > 0]

        if not positive_factors:
            # All negative -> emit FLAT for all (AllWeather handles defense)
            period = timedelta(days=31)
            insights = []
            for ticker in self.tickers:
                symbol = self.symbols.get(ticker)
                if symbol:
                    insights.append(Insight.price(
                        symbol, period, InsightDirection.FLAT,
                        source_model=self.name
                    ))
            return insights

        # Emit UP for top-2 positive factors with proportional weights
        period = timedelta(days=31)
        insights = []

        # Calculate weights proportional to momentum score
        total_score = sum(score for _, _, score in positive_factors)

        for ticker, symbol, score in positive_factors:
            weight = score / total_score if total_score > 0 else 0.5
            insights.append(Insight.price(
                symbol, period, InsightDirection.UP,
                weight=weight,
                source_model=self.name
            ))

        # FLAT for others
        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol and not any(t == ticker for t, _, _ in positive_factors):
                insights.append(Insight.price(
                    symbol, period, InsightDirection.FLAT,
                    source_model=self.name
                ))

        return insights

    def _risk_adjusted_momentum(self, algorithm, symbol):
        """
        Risk-adjusted momentum: 12m-1m return / 63d realized volatility.

        This is the 'momentum sharpe ratio' - a cleaner factor signal that
        penalizes high-volatility momentum (which tends to crash harder).
        """
        history = algorithm.history(symbol, self.lookback + 5, Resolution.DAILY)
        if len(history) < self.lookback:
            return None

        closes = history['close']

        # 12m-1m momentum: from oldest to 21 days ago (skip recent month)
        past_price = closes.iloc[0]
        skip_price = closes.iloc[-self.skip_days] if len(closes) >= self.skip_days else closes.iloc[-1]

        if past_price <= 0:
            return None

        momentum_return = (skip_price / past_price) - 1

        # 63-day realized volatility (annualized)
        recent_closes = closes.iloc[-self.vol_window:]
        if len(recent_closes) < 20:
            return None

        daily_returns = recent_closes.pct_change().dropna()
        realized_vol = daily_returns.std() * np.sqrt(252)

        if realized_vol <= 0:
            return None

        return momentum_return / realized_vol

    def on_securities_changed(self, algorithm, changes):
        for security in changes.added_securities:
            ticker = security.symbol.value
            if ticker in self.tickers:
                self.symbols[ticker] = security.symbol


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
        # Monthly emission
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
