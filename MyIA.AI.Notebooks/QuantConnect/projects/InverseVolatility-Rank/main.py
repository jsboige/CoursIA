#region imports
from AlgorithmImports import *

from sklearn.linear_model import Ridge
# endregion


class InverseVolatilityRankAlgorithm(QCAlgorithm):
    """
    Inverse Volatility Rank and Allocate to Future Contracts.

    This strategy uses Ridge regression to forecast future volatility and
    allocates portfolio weights inversely proportional to expected volatility
    across a basket of futures contracts.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 11

    How it works:
    1. Subscribe to a basket of 12 futures contracts (indices, energy, grains)
    2. Track factors: std of returns, ATR, open interest
    3. Train Ridge regression to predict future volatility
    4. Allocate inverse-volatility weights (lower vol = higher weight)
    5. Rebalance weekly

    Factors (per contract):
    - Standard deviation of daily close returns (60-day)
    - Average True Range (60-day)
    - Open interest

    Label: Standard deviation of open price returns over next 6 days

    Parameters:
    - std_months: Months for std indicator (default: 3)
    - atr_months: Months for ATR indicator (default: 3)
    - training_set_duration: Days of training data (default: 365)
    """

    def initialize(self):
        self.set_start_date(2018, 12, 31)
        self.set_end_date(2024, 4, 1)
        self.set_cash(100_000_000)

        self._std_period = self.get_parameter('std_months', 3) * 26
        self._atr_period = self.get_parameter('atr_months', 3) * 26
        self._training_set_duration = timedelta(
            self.get_parameter('training_set_duration', 365)
        )
        self._future_std_period = 6

        self._contracts = []

        # Subscribe to 12 futures contracts across asset classes
        tickers = [
            Futures.Indices.VIX,
            Futures.Indices.SP_500_E_MINI,
            Futures.Indices.NASDAQ_100_E_MINI,
            Futures.Indices.DOW_30_E_MINI,
            Futures.Energy.BRENT_CRUDE,
            Futures.Energy.GASOLINE,
            Futures.Energy.HEATING_OIL,
            Futures.Energy.NATURAL_GAS,
            Futures.Grains.CORN,
            Futures.Grains.OATS,
            Futures.Grains.SOYBEANS,
            Futures.Grains.WHEAT,
        ]
        for ticker in tickers:
            future = self.add_future(ticker, extended_market_hours=True)
            future.set_filter(lambda universe: universe.front_month())

        # Weekly rebalancing schedule
        schedule_symbol = Symbol.create(
            "SPY", SecurityType.EQUITY, Market.USA
        )
        self.schedule.on(
            self.date_rules.week_start(schedule_symbol),
            self.time_rules.after_market_open(schedule_symbol, 1),
            self._trade
        )

    def _trade(self):
        """Predict volatility and rebalance with inverse-vol weights."""
        # Get open interest data for factor
        open_interest = self.history(
            OpenInterest,
            [c.symbol for c in self._contracts],
            self._training_set_duration,
            fill_forward=False
        )
        open_interest.index = open_interest.index.droplevel(0)

        # Predict next-week volatility for each contract
        expected_volatility_by_security = {}
        for security in self._contracts:
            symbol = security.symbol
            if symbol not in open_interest.index:
                continue

            # Combine indicator history with open interest
            factors = pd.concat(
                [
                    security.indicator_history,
                    open_interest.loc[symbol]
                ],
                axis=1
            ).ffill().loc[security.indicator_history.index].dropna()
            if factors.empty:
                continue

            label = security.label_history

            # Align factors and labels
            idx = sorted(
                list(
                    set(factors.index).intersection(set(label.index))
                )
            )
            if len(idx) < 20:
                continue

            # Train Ridge regression
            model = Ridge()
            model.fit(factors.loc[idx], label.loc[idx])

            # Predict volatility
            prediction = model.predict([factors.iloc[-1]])[0]
            if prediction > 0:
                expected_volatility_by_security[security] = prediction
            self.plot(
                "Predictions",
                security.symbol.canonical.value,
                prediction
            )

        # Compute inverse-volatility portfolio weights
        portfolio_targets = []
        std_sum = sum(
            1 / vol
            for vol in expected_volatility_by_security.values()
        )
        for security, expected_vol in (
            expected_volatility_by_security.items()
        ):
            weight = (
                3
                / expected_vol
                / std_sum
                / security.symbol_properties.contract_multiplier
            )
            portfolio_targets.append(
                PortfolioTarget(security.symbol, weight)
            )
        self.set_holdings(portfolio_targets, True)

    def on_securities_changed(self, changes):
        """Handle futures contract rollovers."""
        for security in changes.added_securities:
            if security.symbol.is_canonical():
                continue  # Skip continuous contracts

            # Create indicators
            security.close_roc = RateOfChange(1)
            security.std_of_close_returns = IndicatorExtensions.of(
                StandardDeviation(self._std_period),
                security.close_roc
            )
            security.atr = AverageTrueRange(self._atr_period)
            security.open_roc = RateOfChange(1)
            security.std_of_open_returns = IndicatorExtensions.of(
                StandardDeviation(self._future_std_period),
                security.open_roc
            )

            # Storage for ML training data
            security.indicator_history = pd.DataFrame()
            security.label_history = pd.Series()

            # Daily consolidator for indicators
            security.consolidator = self.consolidate(
                security.symbol, Resolution.DAILY,
                self._consolidation_handler
            )

            # Warm up with historical data
            warm_up_length = (
                max(self._std_period + 1, self._atr_period)
                + self._training_set_duration.days
            )
            bars = self.history[TradeBar](
                security.symbol, warm_up_length, Resolution.DAILY
            )
            for bar in bars:
                security.consolidator.update(bar)

            self._contracts.append(security)

        for security in changes.removed_securities:
            self.subscription_manager.remove_consolidator(
                security.symbol, security.consolidator
            )
            security.close_roc.reset()
            security.std_of_close_returns.reset()
            security.atr.reset()
            security.open_roc.reset()
            security.std_of_open_returns.reset()
            if security in self._contracts:
                self._contracts.remove(security)

    def _consolidation_handler(self, consolidated_bar):
        """Update indicators and track training labels."""
        security = self.securities[consolidated_bar.symbol]
        t = consolidated_bar.end_time

        # Update indicators
        if security.atr.update(consolidated_bar):
            security.indicator_history.loc[t, 'atr'] = (
                security.atr.current.value
            )
        security.close_roc.update(t, consolidated_bar.close)
        if security.std_of_close_returns.is_ready:
            security.indicator_history.loc[
                t, 'std_of_close_returns'
            ] = security.std_of_close_returns.current.value
        security.open_roc.update(t, consolidated_bar.open)

        # Update label: future std of open returns
        if (security.std_of_open_returns.is_ready and
                len(security.indicator_history.index) >
                self._future_std_period):
            security.label_history.loc[
                security.indicator_history.index[
                    -self._future_std_period - 1
                ]
            ] = security.std_of_open_returns.current.value

        # Trim to training window
        security.indicator_history = security.indicator_history[
            security.indicator_history.index >=
            self.time - self._training_set_duration
        ]
        security.label_history = security.label_history[
            security.label_history.index >=
            self.time - self._training_set_duration
        ]
