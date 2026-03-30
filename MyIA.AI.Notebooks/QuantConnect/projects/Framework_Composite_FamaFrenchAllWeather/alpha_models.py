from AlgorithmImports import *
import numpy as np


class FamaFrenchAlpha(AlphaModel):
    """
    Alpha Model: Fama-French Factor ETF Rotation.

    Signal: Risk-adjusted momentum (12m-1m return / 63d realized vol).
    Selects all factors with positive risk-adjusted score, with USMV fallback.

    Monthly emission, matching the standalone FamaFrench strategy.
    Base Sharpe: 0.540 (2015-2025).
    """

    def __init__(self, tickers):
        super().__init__()
        self.name = "FamaFrench"
        self.tickers = tickers
        self.lookback = 252
        self.skip_days = 21
        self.vol_window = 63
        self.symbols = {}
        self.sma200 = {}
        self.momentum_data = {}
        self._last_month = -1

    def update(self, algorithm, data):
        # Monthly emission (first trading day of month)
        if algorithm.time.month == self._last_month:
            return []
        self._last_month = algorithm.time.month

        if algorithm.is_warming_up:
            return []

        # Get SPY SMA200 for regime filter
        spy_sma = self.sma200.get("SPY")
        if spy_sma is None or not spy_sma.is_ready:
            return []

        spy = self.symbols.get("SPY")
        if spy is None or spy not in algorithm.securities:
            return []
        
        spy_price = algorithm.securities[spy].price
        if spy_price <= 0:
            return []

        risk_on = spy_price > spy_sma.current.value

        # Calculate risk-adjusted momentum scores
        scores = {}
        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            score = self._risk_adjusted_momentum(algorithm, symbol)
            if score is not None:
                scores[ticker] = score

        if len(scores) < 2:
            # Not enough data - emit flat for all
            return self._emit_flat(algorithm)

        period = timedelta(days=31)

        if risk_on:
            # Take ALL factors with positive risk-adjusted momentum
            positive_factors = [t for t, s in scores.items() if s > 0]

            if len(positive_factors) == 0:
                # All negative -> USMV only
                return self._emit_usmv_only(algorithm, period)

            # Equal weight among positive factors
            weight = 1.0 / len(positive_factors)
            insights = []

            for ticker in self.tickers:
                symbol = self.symbols.get(ticker)
                if symbol is None:
                    continue

                if ticker in positive_factors:
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
        else:
            # Risk-off -> USMV only
            return self._emit_usmv_only(algorithm, period)

    def _risk_adjusted_momentum(self, algorithm, symbol):
        """Risk-adjusted momentum: 12m-1m return / 63d realized volatility."""
        try:
            history = algorithm.history(symbol, self.lookback + 5, Resolution.DAILY)
            if len(history) < self.lookback:
                return None

            closes = history['close']

            # 12m-1m momentum (skip recent month to avoid reversal)
            past_price = closes.iloc[0]
            skip_price = closes.iloc[-self.skip_days] if len(closes) >= self.skip_days else closes.iloc[-1]

            if past_price <= 0:
                return None

            momentum_return = (skip_price / past_price) - 1

            # 63-day realized volatility
            recent_closes = closes.iloc[-self.vol_window:]
            if len(recent_closes) < 20:
                return None

            daily_returns = recent_closes.pct_change().dropna()
            realized_vol = daily_returns.std() * np.sqrt(252)

            if realized_vol <= 0:
                return None

            return momentum_return / realized_vol
        except:
            return None

    def _emit_flat(self, algorithm):
        """Emit FLAT insights for all tickers."""
        insights = []
        period = timedelta(days=31)

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            insights.append(Insight.price(
                symbol, period, InsightDirection.FLAT,
                source_model=self.name
            ))

        return insights

    def _emit_usmv_only(self, algorithm, period):
        """Emit UP for USMV only, FLAT for others."""
        insights = []

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            if ticker == "USMV":
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    weight=1.0,
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
                if ticker == "SPY":
                    self.sma200[ticker] = algorithm.sma(sym, 200, Resolution.DAILY)


class AllWeatherAlpha(AlphaModel):
    """
    Alpha Model: All Weather static allocation signal.

    Always emits UP insights for SPY/IEF/GLD/XLP with weight hints
    matching the target allocation (30/30/30/10).
    Monthly emission (low turnover strategy).

    Base Sharpe: 0.667 (2015-2025).
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
