#region imports
from AlgorithmImports import *

from sklearn.naive_bayes import GaussianNB
import pickle
# endregion
# Hands-On AI Trading - Ex15: Gaussian Classifier for Direction Prediction
# Uses a Gaussian Naive Bayes classifier to forecast daily returns of tech
# stocks. Features are the last N daily open-close returns of all universe
# constituents. Labels are positive/negative/flat future returns.
# Source: HandsOnAITradingBook, Section 06, Example 15


class GaussianNaiveBayesAlgorithm(QCAlgorithm):
    """
    Gaussian Naive Bayes Direction Prediction.

    This strategy uses a GNB classifier to predict the direction of future
    returns for technology stocks. The model is trained on cross-sectional
    features (open-close returns of all universe constituents) and predicts
    whether each stock will have positive, negative, or flat returns over
    the next ~22 trading days.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 15

    How it works:
    1. Select top tech stocks by market cap
    2. Collect open-close returns as features for each stock
    3. Train GaussianNB per stock using cross-sectional features
    4. Weekly retrain + rebalance
    5. Long stocks predicted to have positive returns, equal weight

    Parameters:
    - universe_size: Number of tech stocks (default: 10)
    - days_per_sample: Number of lagged returns as features (default: 4)
    - samples: Training window size (default: 100)
    """

    def initialize(self):
        self.set_start_date(2019, 1, 1)
        self.set_end_date(2026, 1, 1)
        self.set_cash(100_000)

        # Model parameters
        self._days_per_sample = self.get_parameter(
            'days_per_sample', 4
        )
        self._samples = self.get_parameter('samples', 100)
        self._holding_period = 30
        self._lookback = (
            self._days_per_sample + self._samples
            + self._holding_period + 1
        )
        self._universe_size = self.get_parameter(
            'universe_size', 10
        )

        # Schedule weekly training and trading
        schedule_symbol = Symbol.create(
            "SPY", SecurityType.EQUITY, Market.USA
        )
        date_rule = self.date_rules.week_start(schedule_symbol)
        self.train(
            date_rule, self.time_rules.at(9, 0), self._train
        )
        self.schedule.on(
            date_rule,
            self.time_rules.after_market_open(schedule_symbol, 2),
            self._trade
        )

        # Universe selection - top tech stocks by market cap
        self.universe_settings.data_normalization_mode = (
            DataNormalizationMode.RAW
        )
        self.universe_settings.schedule.on(date_rule)
        self._universe = self.add_universe(self._select_assets)

        # Pre-trained model storage for live mode
        self._models_by_symbol = {}
        self._key = 'gnb_models.pkl'
        if self.live_mode:
            if self.object_store.contains_key(self._key):
                self._models_by_symbol = pickle.loads(
                    self.object_store.read_bytes(self._key)
                )

    def _select_assets(self, fundamental):
        """Select the largest tech stocks by market cap."""
        tech_stocks = [
            f for f in fundamental
            if f.asset_classification.morningstar_sector_code
            == MorningstarSectorCode.TECHNOLOGY
        ]
        sorted_by_market_cap = sorted(
            tech_stocks, key=lambda x: x.market_cap
        )
        return [
            x.symbol for x in sorted_by_market_cap[-self._universe_size:]
        ]

    def on_securities_changed(self, changes):
        """Set up consolidators and warm up data for new securities."""
        for security in changes.added_securities:
            security.model = None
            self._set_up_consolidator(security)
            self._warm_up(security)

        for security in changes.removed_securities:
            self.subscription_manager.remove_consolidator(
                security.symbol, security.consolidator
            )

    def _set_up_consolidator(self, security):
        """Attach daily consolidator to security."""
        security.consolidator = self.consolidate(
            security.symbol, Resolution.DAILY,
            self._consolidation_handler
        )

    def _warm_up(self, security):
        """Initialize feature/label storage and populate from history."""
        security.roc_window = np.array([])
        security.previous_opens = pd.Series()
        security.labels_by_day = pd.Series()
        security.features_by_day = pd.DataFrame({
            f'{security.Symbol.ID}_(t-{i})': []
            for i in range(1, self._days_per_sample + 1)
        })

        # Get historical prices
        history = self.history(
            security.symbol, self._lookback, Resolution.DAILY,
            data_normalization_mode=DataNormalizationMode.SCALED_RAW
        )
        if history.empty or 'close' not in history:
            self.log(
                f"Not enough history for {security.symbol} yet"
            )
            return

        # Calculate features and labels
        history = history.loc[security.symbol]
        history['open_close_return'] = (
            (history.close - history.open) / history.open
        )

        start = history.shift(-1).open
        end = history.shift(-22).open
        history['future_return'] = (end - start) / start

        for day, row in history.iterrows():
            security.previous_opens[day] = row.open

            if not self._update_features(
                security, day, row.open_close_return
            ):
                continue

            if not pd.isnull(row.future_return):
                security.labels_by_day[day] = np.sign(
                    row.future_return
                )
                security.labels_by_day = security.labels_by_day[
                    -self._samples:
                ]
        security.previous_opens = security.previous_opens[
            -self._holding_period:
        ]

    def _consolidation_handler(self, bar):
        """Process new daily bar and update features/labels."""
        security = self.securities[bar.symbol]
        time = bar.end_time
        open_ = bar.open
        close = bar.close

        # Update features
        open_close_return = (close - open_) / open_
        if not self._update_features(
            security, time, open_close_return
        ):
            return

        # Update labels for completed holding periods
        open_days = security.previous_opens[
            security.previous_opens.index
            <= time - timedelta(self._holding_period)
        ]
        if len(open_days) == 0:
            return
        open_day = open_days.index[-1]
        previous_open = security.previous_opens[open_day]
        open_open_return = (
            (open_ - previous_open) / previous_open
        )
        security.labels_by_day[open_day] = np.sign(
            open_open_return
        )
        security.labels_by_day = security.labels_by_day[
            -self._samples:
        ]

        security.previous_opens.loc[time] = open_
        security.previous_opens = security.previous_opens[
            -self._holding_period:
        ]

    def _update_features(self, security, day, open_close_return):
        """
        Update the rolling feature window for a security.

        Returns True when enough features are collected for training.
        """
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
        """Train GaussianNB classifier for each security."""
        features = pd.DataFrame()
        labels_by_symbol = {}

        self._tradable_securities = []
        for symbol in self._universe.selected:
            security = self.securities[symbol]
            if self._is_ready(security):
                self._tradable_securities.append(security)
                features = pd.concat(
                    [features, security.features_by_day], axis=1
                )
                labels_by_symbol[symbol] = security.labels_by_day

        # Drop rows with NaN (from universe change timing)
        features.dropna(inplace=True)

        # Find intersection of feature and label indices
        idx = set(features.index.tolist())
        for symbol, labels in labels_by_symbol.items():
            idx &= set(labels.index.tolist())
        idx = sorted(list(idx))

        if len(idx) < 20:
            return

        for security in self._tradable_securities:
            symbol = security.symbol
            try:
                security.model = GaussianNB().fit(
                    features.loc[idx],
                    labels_by_symbol[symbol].loc[idx]
                )
            except Exception:
                security.model = None
                continue

            # Save model for live trading persistence
            if self.live_mode:
                key = str(symbol.id)
                self._models_by_symbol[key] = pickle.dumps(
                    security.model
                )

    def _is_ready(self, security):
        """Check if security has enough data for training."""
        return (
            security.features_by_day.shape[0]
            == self._samples + self._holding_period + 2
        )

    def on_splits(self, splits):
        """Reset consolidators after stock splits."""
        for symbol, split in splits.items():
            if split.type != SplitType.SPLIT_OCCURRED:
                continue
            security = self.securities[symbol]
            self.subscription_manager.remove_consolidator(
                symbol, security.consolidator
            )
            self._set_up_consolidator(security)
            self._warm_up(security)

    def _trade(self):
        """Execute trades based on GNB predictions."""
        features = [[]]
        for security in self._tradable_securities:
            features[0].extend(
                security.features_by_day.iloc[-1].values.tolist()
            )

        # Select assets predicted to have positive returns
        long_symbols = []
        for security in self._tradable_securities:
            key = str(security.symbol.id)
            if (
                self.live_mode
                and not hasattr(security, 'model')
                and key in self._models_by_symbol
            ):
                security.model = pickle.loads(
                    self._models_by_symbol[key]
                )

            if security.model is None:
                continue

            try:
                prediction = security.model.predict(features)
                if prediction[0] == 1:
                    long_symbols.append(security.symbol)
            except Exception:
                continue

        if len(long_symbols) == 0:
            # Liquidate if no positive predictions
            for holding in self.portfolio.values():
                if holding.invested:
                    self.liquidate(holding.symbol)
            return

        # Equal weight allocation to predicted winners
        weight = float(1.0 / len(long_symbols))
        self.set_holdings(
            [
                PortfolioTarget(symbol, weight)
                for symbol in long_symbols
            ],
            True
        )

        # Plot trading metrics
        self.plot(
            "Trades", "Tradable Securities",
            len(self._tradable_securities)
        )
        self.plot("Trades", "Target Assets", len(long_symbols))

    def on_end_of_algorithm(self):
        """Persist trained models for live redeployment."""
        if self.live_mode:
            self.object_store.save_bytes(
                self._key, pickle.dumps(self._models_by_symbol)
            )
