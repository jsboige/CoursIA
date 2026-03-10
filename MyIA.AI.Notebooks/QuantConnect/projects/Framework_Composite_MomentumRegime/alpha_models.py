from AlgorithmImports import *


class SectorMomentumAlpha(AlphaModel):
    """
    Alpha Model: Sector Dual Momentum signal.

    Emits UP insight for best asset among SPY/IEF/GLD based on
    multi-lookback composite momentum (1/3/6/12 months).

    Note: IEF used instead of TLT (TLT destroys value 2015-2026).

    Monthly emission.
    """

    def __init__(self, tickers):
        super().__init__()
        self.name = "SectorMomentum"
        self.tickers = tickers
        self.symbols = {}
        self.spy_sma200 = None
        self.lookback_windows = [21, 63, 126, 252]  # 1, 3, 6, 12 months
        self.max_lookback = max(self.lookback_windows)
        self.lookback_weights = [0.4, 0.2, 0.2, 0.2]
        self._last_month = -1

    def update(self, algorithm, data):
        # Monthly emission
        if algorithm.time.month == self._last_month:
            return []
        self._last_month = algorithm.time.month

        if algorithm.is_warming_up:
            return []

        if self.spy_sma200 is None or not self.spy_sma200.is_ready:
            return []

        # Compute composite momentum scores
        scores = {}
        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            price = algorithm.securities[symbol].price
            if price <= 0:
                continue

            score = self._composite_momentum(algorithm, symbol, price)
            if score is not None:
                scores[ticker] = (symbol, score)

        if not scores:
            return []

        # SMA200 filter for SPY
        spy_symbol = self.symbols.get("SPY")
        spy_above_sma = False
        if spy_symbol:
            spy_price = algorithm.securities[spy_symbol].price
            spy_above_sma = spy_price > self.spy_sma200.current.value

        # Select best asset
        best_ticker = max(scores, key=lambda k: scores[k][1])
        best_symbol, best_score = scores[best_ticker]

        # SPY only if positive momentum AND above SMA200
        if best_ticker == "SPY":
            if best_score <= 0 or not spy_above_sma:
                # Fallback to best defensive (IEF instead of TLT)
                defensive_scores = {k: v for k, v in scores.items() if k in ["IEF", "GLD"]}
                if defensive_scores:
                    best_ticker = max(defensive_scores, key=lambda k: defensive_scores[k][1])
                    best_symbol = defensive_scores[best_ticker][0]

        period = timedelta(days=31)
        insights = []

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            if ticker == best_ticker:
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

    def _composite_momentum(self, algorithm, symbol, current_price):
        """Weighted composite momentum across 1/3/6/12 month lookbacks."""
        history = algorithm.history(symbol, self.max_lookback, Resolution.DAILY)
        if len(history) < self.max_lookback:
            return None

        score = 0.0
        for window, weight in zip(self.lookback_windows, self.lookback_weights):
            past_price = history['close'].iloc[-window]
            if past_price > 0:
                momentum = (current_price / past_price) - 1
                score += weight * momentum
        return score

    def on_securities_changed(self, algorithm, changes):
        for security in changes.added_securities:
            ticker = security.symbol.value
            if ticker in self.tickers:
                self.symbols[ticker] = security.symbol
                if ticker == "SPY":
                    self.spy_sma200 = algorithm.sma(security.symbol, 200, Resolution.DAILY)


class RegimeSwitchingAlpha(AlphaModel):
    """
    Alpha Model: Regime-Switching signal (Momentum in bull, Mean-Reversion in bear/sideways).

    Detects market regime using SPY SMA50/SMA200:
    - Bull: momentum strategy (risk-adjusted momentum on SPY/QQQ)
    - Bear/Sideways: mean reversion (RSI oversold) + defensive (GLD/IEF)

    Monthly emission + regime-change trigger.
    """

    def __init__(self, tickers):
        super().__init__()
        self.name = "RegimeSwitching"
        self.risky = ["SPY", "QQQ"]
        self.defensive = ["IEF", "GLD"]
        self.all_tickers = tickers
        self.symbols = {}
        self.sma50 = None
        self.sma200 = None
        self.rsi_indicators = {}
        self.current_regime = None
        self.momentum_lookback = 63
        self.rsi_oversold = 30
        self.rsi_exit = 50
        self._last_month = -1
        self._need_rebalance = False
        self.algorithm = None  # Store algorithm reference for price access

    def update(self, algorithm, data):
        # Store algorithm reference for price access
        self.algorithm = algorithm

        # Monthly emission
        if algorithm.time.month == self._last_month:
            # Check for regime change
            regime = self._detect_regime()
            if regime != "unknown" and regime != self.current_regime:
                if self.current_regime is not None:
                    self._need_rebalance = True
                self.current_regime = regime
            if not self._need_rebalance:
                return []
        else:
            self._last_month = algorithm.time.month
            regime = self._detect_regime()
            if regime != "unknown":
                self.current_regime = regime
            self._need_rebalance = False

        if algorithm.is_warming_up:
            return []

        if not self.sma50.is_ready or not self.sma200.is_ready:
            return []

        self._need_rebalance = False
        period = timedelta(days=31)

        if self.current_regime == "bull":
            return self._apply_momentum(algorithm, period)
        else:
            return self._apply_mean_reversion(algorithm, period, self.current_regime)

    def _detect_regime(self):
        if not self.sma50.is_ready or not self.sma200.is_ready:
            return "unknown"

        spy_price = self._spy_price()
        if spy_price <= 0:
            return "unknown"

        sma50_val = self.sma50.current.value
        sma200_val = self.sma200.current.value

        if spy_price > sma200_val and sma50_val > sma200_val:
            return "bull"
        elif spy_price < sma200_val and sma50_val < sma200_val:
            return "bear"
        else:
            return "sideways"

    def _spy_price(self):
        # Helper to get SPY price
        spy_symbol = self.symbols.get("SPY")
        if spy_symbol and self.algorithm:
            return self.algorithm.securities[spy_symbol].price
        return 0

    def _apply_momentum(self, algorithm, period):
        # Risk-adjusted momentum for SPY/QQQ
        insights = []
        spy_symbol = self.symbols.get("SPY")
        qqq_symbol = self.symbols.get("QQQ")

        if not spy_symbol or not qqq_symbol:
            return []

        # Risk-adjusted momentum calculation
        risk_adj_mom = {}
        for ticker in ["SPY", "QQQ"]:
            symbol = self.symbols.get(ticker)
            if not symbol:
                continue
            price = algorithm.securities[symbol].price
            if price <= 0:
                continue

            history = algorithm.history(symbol, self.momentum_lookback + 5, Resolution.DAILY)
            if len(history) < self.momentum_lookback:
                continue

            try:
                prices = history.loc[symbol]["close"] if symbol in history.index else history["close"]
                if len(prices) >= self.momentum_lookback:
                    raw_return = prices.iloc[-1] / prices.iloc[-self.momentum_lookback] - 1
                    daily_returns = prices.pct_change().dropna()
                    vol = daily_returns.std() * (252 ** 0.5)
                    if vol > 0.01:
                        risk_adj_mom[ticker] = raw_return / vol
                    else:
                        risk_adj_mom[ticker] = raw_return
            except (KeyError, TypeError):
                continue

        if not risk_adj_mom:
            return []

        best = max(risk_adj_mom, key=risk_adj_mom.get)
        other = "QQQ" if best == "SPY" else "SPY"

        # Best gets 70%, other gets 30%
        best_weight = 0.70
        other_weight = 0.30

        insights.append(Insight.price(
            self.symbols[best], period, InsightDirection.UP,
            weight=best_weight,
            source_model=self.name
        ))
        insights.append(Insight.price(
            self.symbols[other], period, InsightDirection.UP,
            weight=other_weight,
            source_model=self.name
        ))

        # Defensive assets to FLAT
        for ticker in self.defensive:
            if ticker in self.symbols:
                insights.append(Insight.price(
                    self.symbols[ticker], period, InsightDirection.FLAT,
                    source_model=self.name
                ))

        return insights

    def _apply_mean_reversion(self, algorithm, period, regime):
        insights = []
        oversold = []

        # Check RSI for oversold
        for ticker in self.risky:
            if ticker in self.rsi_indicators and self.rsi_indicators[ticker].is_ready:
                rsi_val = self.rsi_indicators[ticker].current.value
                if rsi_val < self.rsi_oversold:
                    oversold.append(ticker)

        if oversold:
            weight_per_asset = 0.30 / len(oversold)
            for ticker in oversold:
                insights.append(Insight.price(
                    self.symbols[ticker], period, InsightDirection.UP,
                    weight=weight_per_asset,
                    source_model=self.name
                ))

            # Defensive allocation
            insights.append(Insight.price(
                self.symbols["GLD"], period, InsightDirection.UP,
                weight=0.35,
                source_model=self.name
            ))
            insights.append(Insight.price(
                self.symbols["IEF"], period, InsightDirection.UP,
                weight=0.35,
                source_model=self.name
            ))
        else:
            # No oversold stocks - allocate based on regime
            if regime == "bear":
                # Bear: 100% defensive (GLD 50%, IEF 50%)
                for ticker in self.risky:
                    insights.append(Insight.price(
                        self.symbols[ticker], period, InsightDirection.FLAT,
                        source_model=self.name
                    ))
                insights.append(Insight.price(
                    self.symbols["GLD"], period, InsightDirection.UP,
                    weight=0.50,
                    source_model=self.name
                ))
                insights.append(Insight.price(
                    self.symbols["IEF"], period, InsightDirection.UP,
                    weight=0.50,
                    source_model=self.name
                ))
            else:  # sideways
                # Sideways: reduced equity (SPY 30%) + defensive (GLD 35%, IEF 35%)
                insights.append(Insight.price(
                    self.symbols["SPY"], period, InsightDirection.UP,
                    weight=0.30,
                    source_model=self.name
                ))
                insights.append(Insight.price(
                    self.symbols["QQQ"], period, InsightDirection.FLAT,
                    source_model=self.name
                ))
                insights.append(Insight.price(
                    self.symbols["GLD"], period, InsightDirection.UP,
                    weight=0.35,
                    source_model=self.name
                ))
                insights.append(Insight.price(
                    self.symbols["IEF"], period, InsightDirection.UP,
                    weight=0.35,
                    source_model=self.name
                ))

        return insights

    def on_securities_changed(self, algorithm, changes):
        for security in changes.added_securities:
            ticker = security.symbol.value
            if ticker in self.all_tickers:
                self.symbols[ticker] = security.symbol

                if ticker == "SPY":
                    self.sma50 = algorithm.sma(security.symbol, 50, Resolution.DAILY)
                    self.sma200 = algorithm.sma(security.symbol, 200, Resolution.DAILY)

                if ticker in self.risky:
                    indicator = RelativeStrengthIndex(14, MovingAverageType.WILDERS)
                    algorithm.register_indicator(security.symbol, indicator, Resolution.DAILY)
                    self.rsi_indicators[ticker] = indicator
