from AlgorithmImports import *


class SectorMomentumAlpha(AlphaModel):
    """Alpha Model: Sector ETF Momentum Rotation.

    Skip-month vol-adjusted momentum + dual regime filter + stop-loss.
    Based on SectorMomentumETFRotation v4.0 (Sharpe 0.472 standalone).

    Emits UP for top N sectors with positive momentum, FLAT otherwise.
    In risk-off mode, only XLP and XLU get UP insights.
    Monthly emission.

    Every FLAT carries weight 0. InsightWeightingPortfolioConstructionModel
    only builds a target for a weighted insight: an unweighted FLAT left the
    previous UP in charge, so a deselected or stopped line was never sold
    (#20264).
    """

    def __init__(self, sector_tickers, top_n=4, lookback=252,
                 skip_days=21, vol_window=63, stop_loss_pct=-0.10):
        super().__init__()
        self.name = "SectorMomentum"
        self.sector_tickers = sector_tickers
        self.top_n = top_n
        self.lookback = lookback
        self.skip_days = skip_days
        self.vol_window = vol_window
        self.stop_loss_pct = stop_loss_pct
        self.symbols = {}
        self.spy = None
        self.spy_sma200 = None
        self.spy_sma20 = None
        self._last_month = -1
        self.entry_prices = {}
        # Insight life in daily bars: longer than the gap between two monthly
        # emissions, so the next emission always replaces the previous one.
        self.period = timedelta(days=30)

    def _flat(self, symbol):
        return Insight.price(
            symbol, self.period, InsightDirection.FLAT,
            weight=0, source_model=self.name
        )

    def _arm_stop(self, algorithm, ticker, symbol):
        """Arm the stop-loss of a retained line.

        A line bought at this emission takes the current price, as in the
        standalone version. A line already held without an entry price takes
        the average price of the position.
        """
        holding = algorithm.portfolio[symbol]
        if not holding.invested:
            self.entry_prices[ticker] = algorithm.securities[symbol].price
        elif ticker not in self.entry_prices:
            self.entry_prices[ticker] = holding.average_price

    def update(self, algorithm, data):
        if algorithm.is_warming_up:
            return []

        if self.spy_sma200 is None or self.spy_sma20 is None:
            return []
        if not self.spy_sma200.is_ready or not self.spy_sma20.is_ready:
            return []

        insights = []

        # Daily stop-loss check: emit FLAT for stopped positions. The FLAT lives
        # as long as a monthly insight, so the UP of the month cannot take over
        # again when a shorter FLAT expires and buy the line back.
        for ticker in list(self.entry_prices.keys()):
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue
            if not algorithm.portfolio[symbol].invested:
                del self.entry_prices[ticker]
                continue
            current_price = algorithm.securities[symbol].price
            entry = self.entry_prices[ticker]
            if current_price > 0 and entry > 0:
                pct = (current_price / entry) - 1
                if pct < self.stop_loss_pct:
                    insights.append(self._flat(symbol))
                    del self.entry_prices[ticker]

        # Monthly rebalancing
        month = algorithm.time.month
        if month == self._last_month:
            return insights
        self._last_month = month

        # Compute momentum scores
        scores = {}
        raw_scores = {}
        for ticker in self.sector_tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue
            result = self._momentum_score(algorithm, symbol)
            if result is not None:
                vol_adj, raw_mom = result
                scores[ticker] = vol_adj
                raw_scores[ticker] = raw_mom

        if len(scores) < self.top_n:
            return insights

        # Dual regime filter
        spy_price = algorithm.securities[self.spy].price
        below_sma200 = spy_price < self.spy_sma200.current.value
        below_sma20 = spy_price < self.spy_sma20.current.value
        risk_off = below_sma200 and below_sma20

        period = self.period

        if not risk_off:
            sorted_sectors = sorted(
                scores.items(), key=lambda x: x[1], reverse=True
            )
            top_sectors = [
                t for t, s in sorted_sectors[:self.top_n]
                if raw_scores.get(t, 0) > 0
            ]

            if len(top_sectors) == 0:
                # Defensive fallback
                for ticker in self.sector_tickers:
                    symbol = self.symbols.get(ticker)
                    if symbol is None:
                        continue
                    if ticker in ("XLP", "XLU"):
                        insights.append(Insight.price(
                            symbol, period, InsightDirection.UP,
                            weight=0.5, source_model=self.name
                        ))
                        self._arm_stop(algorithm, ticker, symbol)
                    else:
                        insights.append(self._flat(symbol))
                        self.entry_prices.pop(ticker, None)
                return insights

            weight = 1.0 / len(top_sectors)

            for ticker in self.sector_tickers:
                symbol = self.symbols.get(ticker)
                if symbol is None:
                    continue
                if ticker in top_sectors:
                    insights.append(Insight.price(
                        symbol, period, InsightDirection.UP,
                        weight=weight, source_model=self.name
                    ))
                    self._arm_stop(algorithm, ticker, symbol)
                else:
                    insights.append(self._flat(symbol))
                    self.entry_prices.pop(ticker, None)
        else:
            # Risk-off: only XLP and XLU
            for ticker in self.sector_tickers:
                symbol = self.symbols.get(ticker)
                if symbol is None:
                    continue
                if ticker in ("XLP", "XLU"):
                    insights.append(Insight.price(
                        symbol, period, InsightDirection.UP,
                        weight=0.5, source_model=self.name
                    ))
                    self._arm_stop(algorithm, ticker, symbol)
                else:
                    insights.append(self._flat(symbol))
                    self.entry_prices.pop(ticker, None)

        return insights

    def _momentum_score(self, algorithm, symbol):
        # On the 13:00 close slice of a US half-session, a daily history request
        # by bar count comes back short (44 bars out of 257 measured on this
        # alpha, #20264). Ask for twice the bars and keep the most recent ones,
        # as in the standalone main.py (#20286).
        history = algorithm.history(
            symbol, 2 * (self.lookback + 5), Resolution.DAILY
        )
        history = history.iloc[-(self.lookback + 5):]
        if len(history) < self.lookback:
            return None

        closes = history['close']
        current_price = closes.iloc[-self.skip_days]
        past_price = closes.iloc[0]
        if past_price <= 0 or current_price <= 0:
            return None

        raw_momentum = (current_price / past_price) - 1

        recent_closes = closes.iloc[-self.vol_window:]
        if len(recent_closes) < 20:
            return None

        daily_returns = recent_closes.pct_change().dropna()
        vol = daily_returns.std()
        if vol <= 0:
            return None

        vol_adj_score = raw_momentum / vol
        return vol_adj_score, raw_momentum

    def on_securities_changed(self, algorithm, changes):
        for security in changes.added_securities:
            ticker = security.symbol.value
            if ticker in self.sector_tickers:
                self.symbols[ticker] = security.symbol
            elif ticker == "SPY":
                self.spy = security.symbol
                self.spy_sma200 = algorithm.sma(
                    security.symbol, 200, Resolution.DAILY
                )
                self.spy_sma20 = algorithm.sma(
                    security.symbol, 20, Resolution.DAILY
                )
