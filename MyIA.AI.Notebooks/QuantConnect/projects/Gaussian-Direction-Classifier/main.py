# region imports
from AlgorithmImports import *

from sklearn.naive_bayes import GaussianNB
import numpy as np
import pandas as pd
# endregion


class GaussianDirectionClassifier(QCAlgorithm):
    """
    Direction Prediction using Gaussian Naive Bayes Classifier.

    This strategy demonstrates ML classification to predict the direction
    of future stock returns using Gaussian Naive Bayes.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 15

    How it works:
    1. Build features from trailing daily returns (open-to-close)
    2. Create labels based on future returns (positive/negative)
    3. Train GaussianNB classifier weekly
    4. Predict direction for each asset
    5. Go long on assets predicted to have positive returns

    Features: Last 4 daily open-to-close returns of universe constituents
    Labels: Sign of future 30-day return (1=positive, -1=negative, 0=flat)
    """

    def initialize(self):
        self.set_start_date(2019, 1, 1)
        self.set_end_date(2024, 1, 1)
        self.set_cash(1_000_000)

        # Model parameters
        self._days_per_sample = self.get_parameter('days_per_sample', 4)
        self._samples = self.get_parameter('samples', 100)
        self._holding_period = 30  # Calendar days

        self._lookback = (
            self._days_per_sample + self._samples + self._holding_period + 1
        )

        # Schedule: Train weekly on Monday, trade on Monday after open
        schedule_symbol = Symbol.create("SPY", SecurityType.EQUITY, Market.USA)
        date_rule = self.date_rules.week_start(schedule_symbol)

        # Training schedule
        self.train(date_rule, self.time_rules.at(9, 0), self._train)

        # Trading schedule
        self.schedule.on(
            date_rule,
            self.time_rules.after_market_open(schedule_symbol, 30),
            self._trade
        )

        # Universe selection: Top tech stocks by market cap
        self._universe_size = self.get_parameter("universe_size", 5)
        self.universe_settings.data_normalization_mode = DataNormalizationMode.RAW
        self.universe_settings.schedule.on(date_rule)
        self._universe = self.add_universe(self._select_assets)

        self.log(f"GaussianClassifier initialized: {self._universe_size} assets, {self._days_per_sample}-day features")

    def _select_assets(self, fundamental):
        """Select largest tech stocks by market cap."""
        tech_stocks = [
            f for f in fundamental
            if f.asset_classification.morningstar_sector_code == MorningstarSectorCode.TECHNOLOGY
        ]
        sorted_by_market_cap = sorted(tech_stocks, key=lambda x: x.market_cap)
        return [x.symbol for x in sorted_by_market_cap[-self._universe_size:]]

    def on_securities_changed(self, changes):
        """Initialize securities when they enter the universe."""
        for security in changes.added_securities:
            self._initialize_security(security)

    def _initialize_security(self, security):
        """Set up data structures for a security."""
        security.roc_window = np.array([])
        security.previous_opens = pd.Series()
        security.labels_by_day = pd.Series()
        security.features_by_day = pd.DataFrame({
            f'{security.symbol.id}_(t-{i})': []
            for i in range(1, self._days_per_sample + 1)
        })
        security.model = None

        # Warm up with historical data
        history = self.history(
            security.symbol, self._lookback, Resolution.DAILY,
            data_normalization_mode=DataNormalizationMode.SCALED_RAW
        )
        if history.empty or 'close' not in history:
            return

        history = history.loc[security.symbol]
        history['open_close_return'] = (history.close - history.open) / history.open

        # Calculate future returns for labels
        start = history.shift(-1).open
        end = history.shift(-22).open  # ~30 calendar days
        history['future_return'] = (end - start) / start

        for day, row in history.iterrows():
            security.previous_opens[day] = row.open

            # Update features
            if not self._update_features(security, day, row.open_close_return):
                continue

            # Update labels
            if not pd.isnull(row.future_return):
                security.labels_by_day[day] = np.sign(row.future_return)
                security.labels_by_day = security.labels_by_day[-self._samples:]

        security.previous_opens = security.previous_opens[-self._holding_period:]

    def _update_features(self, security, day, open_close_return):
        """Update feature window for a security."""
        security.roc_window = np.append(
            open_close_return, security.roc_window
        )[:self._days_per_sample]

        if len(security.roc_window) < self._days_per_sample:
            return False

        security.features_by_day.loc[day] = security.roc_window
        security.features_by_day = security.features_by_day[
            -(self._samples + self._holding_period + 2):
        ]
        return True

    def _train(self):
        """Train Gaussian Naive Bayes classifier for each security."""
        features = pd.DataFrame()
        labels_by_symbol = {}
        tradable_securities = []

        for symbol in self._universe.selected:
            security = self.securities[symbol]
            if self._is_ready(security):
                tradable_securities.append(security)
                features = pd.concat([features, security.features_by_day], axis=1)
                labels_by_symbol[symbol] = security.labels_by_day

        if not tradable_securities:
            self.log("No securities ready for training")
            return

        # Remove NaN rows from features
        features.dropna(inplace=True)

        # Find common dates
        idx = set(features.index)
        for labels in labels_by_symbol.values():
            idx &= set(labels.index)
        idx = sorted(list(idx))

        if not idx:
            self.log("No common dates for training")
            return

        # Train model for each security
        for security in tradable_securities:
            symbol = security.symbol
            if symbol in labels_by_symbol:
                try:
                    security.model = GaussianNB().fit(
                        features.loc[idx],
                        labels_by_symbol[symbol].loc[idx]
                    )
                    self.log(f"Trained model for {symbol}")
                except Exception as e:
                    self.log(f"Training error for {symbol}: {e}")

    def _is_ready(self, security):
        """Check if security has enough data."""
        return (
            hasattr(security, 'features_by_day') and
            security.features_by_day.shape[0] >= self._samples + self._holding_period
        )

    def _trade(self):
        """Execute trades based on model predictions."""
        # Get current features
        features = [[]]
        tradable = [s for s in self.securities.values() if hasattr(s, 'model') and s.model is not None]

        for security in tradable:
            if hasattr(security, 'features_by_day') and not security.features_by_day.empty:
                features[0].extend(security.features_by_day.iloc[-1].values)

        if not features[0]:
            return

        # Select assets predicted to have positive returns
        long_symbols = []
        for security in tradable:
            try:
                prediction = security.model.predict(features)
                if prediction[0] == 1:  # Positive direction predicted
                    long_symbols.append(security.symbol)
            except Exception as e:
                self.log(f"Prediction error: {e}")

        if not long_symbols:
            return

        # Equal weight allocation
        weight = 1.0 / len(long_symbols)
        targets = [PortfolioTarget(symbol, weight) for symbol in long_symbols]
        self.set_holdings(targets, True)

        self.plot("Trades", "Positions", len(long_symbols))

    def on_end_of_algorithm(self):
        final_value = self.portfolio.total_portfolio_value
        returns = (final_value - 1000000) / 1000000
        self.log(f"Gaussian Classifier: Final=${final_value:,.0f}, Return={returns:.2%}")
