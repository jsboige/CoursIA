# region imports
from AlgorithmImports import *
# endregion


class SectorMomentumAlpha(AlphaModel):
    """Sector Momentum Alpha Model.

    Generates UP insights for sector ETFs above SMA200 with positive momentum.
    Weekly emission with momentum-weighted confidence.
    """

    def __init__(self, tickers, lookback=126, sma_period=200):
        super().__init__()
        self.name = "SectorMomentum"
        self.tickers = tickers
        self.lookback = lookback
        self.sma_period = sma_period
        self.symbols = {}
        self._sma = {}
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

            sma = self._sma.get(ticker)
            if not sma or not sma.is_ready:
                continue

            price = algorithm.securities[symbol].price
            if price <= 0:
                continue

            price_above_sma = price > sma.current.value

            # Calculate momentum via history
            try:
                history = algorithm.history(symbol, self.lookback, Resolution.DAILY)
                if history.empty or len(history) < self.lookback:
                    continue
                momentum = (history["close"].iloc[-1] / history["close"].iloc[0]) - 1
            except Exception:
                momentum = 0

            if price_above_sma and momentum > 0:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    source_model=self.name,
                ))
            else:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.FLAT,
                    source_model=self.name,
                ))

        return insights

    def on_securities_changed(self, algorithm, changes):
        for security in changes.added_securities:
            ticker = security.symbol.value
            if ticker in self.tickers:
                self.symbols[ticker] = security.symbol
                self._sma[ticker] = algorithm.sma(security.symbol, self.sma_period, Resolution.DAILY)


class DefensiveAlpha(AlphaModel):
    """Defensive Alpha Model.

    Allocates to safe-haven assets (TLT, GLD, XLU) when SPY is below SMA200.
    Provides portfolio protection during bear markets.
    """

    def __init__(self, tickers, spy_ticker="SPY", sma_period=200):
        super().__init__()
        self.name = "Defensive"
        self.tickers = tickers
        self.spy_ticker = spy_ticker
        self.sma_period = sma_period
        self.symbols = {}
        self.spy_symbol = None
        self._spy_sma = None
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

        if not self._spy_sma or not self._spy_sma.is_ready:
            return []

        spy_price = algorithm.securities[self.spy_symbol].price
        is_bear = spy_price < self._spy_sma.current.value

        for ticker in self.tickers:
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue

            if is_bear:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.UP,
                    source_model=self.name,
                ))
            else:
                insights.append(Insight.price(
                    symbol, period, InsightDirection.FLAT,
                    source_model=self.name,
                ))

        return insights

    def on_securities_changed(self, algorithm, changes):
        for security in changes.added_securities:
            ticker = security.symbol.value
            if ticker == self.spy_ticker:
                self.spy_symbol = security.symbol
                self._spy_sma = algorithm.sma(security.symbol, self.sma_period, Resolution.DAILY)
            elif ticker in self.tickers:
                self.symbols[ticker] = security.symbol


class MultiStrategyPCM(PortfolioConstructionModel):
    """Portfolio construction that allocates capital slices per alpha model."""

    def __init__(self, alpha_allocations, rebalance=timedelta(days=7)):
        super().__init__()
        self.alpha_allocations = alpha_allocations
        self.set_rebalancing_func(lambda dt: dt + rebalance)

    def determine_target_percent(self, active_insights):
        result = {}
        if not active_insights:
            return result

        by_alpha = {}
        for insight in active_insights:
            source = insight.source_model or "Unknown"
            by_alpha.setdefault(source, []).append(insight)

        for alpha_name, insights in by_alpha.items():
            capital_slice = self.alpha_allocations.get(alpha_name, 0)
            if capital_slice <= 0:
                for insight in insights:
                    result[insight] = 0
                continue

            active = [i for i in insights if i.direction != InsightDirection.FLAT]
            flat = [i for i in insights if i.direction == InsightDirection.FLAT]

            for insight in flat:
                result[insight] = 0

            if not active:
                continue

            per_symbol = capital_slice / len(active)
            for insight in active:
                result[insight] = insight.direction * per_symbol

        return result


class ESGFFrameworkComposite(QCAlgorithm):
    """
    ESGF Kit - Framework Composite Strategy.

    Combines three complementary alpha models via QC Algorithm Framework:
    1. SectorMomentum: Long sector ETFs with positive momentum above SMA200
    2. Defensive: Safe-haven rotation during bear markets (SPY < SMA200)
    3. MultiStrategyPCM: Capital allocation 70% momentum / 30% defensive

    Architecture:
        - Universe: 9 sector ETFs + 3 safe-haven assets (TLT, GLD, XLU)
        - Alpha: 2 models (SectorMomentum + Defensive)
        - PCM: MultiStrategyPCM (70/30 allocation)
        - Risk: MaxDrawdown 15% circuit breaker
        - Execution: ImmediateExecutionModel

    Performance (2015-2024 backtest):
        - Target Sharpe: >= 0.79
        - v1: 70/30 allocation, 15% circuit breaker -> Sharpe 0.376, CAGR 7.60%, MaxDD 20.6%
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.SetEndDate(2024, 12, 31)
        self.SetCash(100000)
        self.SetBrokerageModel(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # Universe
        sector_tickers = ["XLK", "XLF", "XLV", "XLE", "XLY", "XLP", "XLI", "XLU", "XLRE"]
        defensive_tickers = ["TLT", "GLD", "XLU"]

        # Add SPY for benchmark and regime detection
        self.AddEquity("SPY", Resolution.DAILY)

        # Add all assets
        all_tickers = list(set(sector_tickers + defensive_tickers))
        for ticker in all_tickers:
            self.AddEquity(ticker, Resolution.DAILY)

        # Alpha models
        self.SetAlpha(CompositeAlphaModel(
            SectorMomentumAlpha(sector_tickers, lookback=126, sma_period=200),
            DefensiveAlpha(defensive_tickers, spy_ticker="SPY", sma_period=200),
        ))

        # Portfolio construction: 70% sector momentum, 30% defensive
        self.SetPortfolioConstruction(MultiStrategyPCM(
            alpha_allocations={
                "SectorMomentum": 0.70,
                "Defensive": 0.30,
            },
            rebalance=timedelta(days=7),
        ))

        # Risk management: max drawdown circuit breaker
        self.SetRiskManagement(MaxDrawdownCircuitBreaker(0.15))

        # Execution
        self.SetExecution(ImmediateExecutionModel())

        self.SetBenchmark("SPY")
        self.SetWarmUp(210, Resolution.DAILY)

        # Track drawdown for logging
        self.peak_value = self.Portfolio.TotalPortfolioValue

    def OnEndOfDay(self, symbol):
        """Track peak and drawdown for logging."""
        current = self.Portfolio.TotalPortfolioValue
        if current > self.peak_value:
            self.peak_value = current

    def OnEndOfAlgorithm(self):
        final = self.Portfolio.TotalPortfolioValue
        self.Log(f"FRAMEWORK COMPOSITE: Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")


class MaxDrawdownCircuitBreaker(RiskManagementModel):
    """Circuit breaker that liquidates all positions when max drawdown exceeded."""

    def __init__(self, max_drawdown=0.15):
        super().__init__()
        self.max_drawdown = max_drawdown
        self.peak_value = None

    def manage_risk(self, algorithm, targets):
        portfolio_value = algorithm.portfolio.total_portfolio_value

        if self.peak_value is None or portfolio_value > self.peak_value:
            self.peak_value = portfolio_value

        if self.peak_value > 0:
            drawdown = (self.peak_value - portfolio_value) / self.peak_value
            if drawdown > self.max_drawdown:
                algorithm.Log(f"CIRCUIT BREAKER: DD={drawdown:.2%} > {self.max_drawdown:.0%}, liquidating")
                targets = []
                for holding in algorithm.portfolio.Values:
                    if holding.Invested:
                        targets.append(PortfolioTarget(holding.Symbol, 0))
                self.peak_value = portfolio_value
                return targets

        return []
