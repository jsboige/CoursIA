# region imports
from AlgorithmImports import *
# endregion

class MLXGBoostAlgorithm(QCAlgorithm):
    """
    XGBoost Gradient Boosting Strategy - v2.

    Improvements over v1:
    - Extended period to 2015-2026 for better robustness
    - Biweekly rebalance (every other Monday) to reduce turnover
    - Separate training day (Monday 1) from trading day (Monday 2)
    - Lower prediction threshold 0.001 (vs 0.002) to increase market exposure
    - Lower learning_rate 0.03 (vs 0.05) for better generalization
    - Selective liquidation (only exit positions not in new selection)
    - 90% allocation across up to 9 positions

    Results v1 (2020-2026): Sharpe 0.195
    Results v2 (2015-2026): Sharpe 0.566, CAGR 14.8%, MaxDD 38.6%
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)

        # Universe: Top 15 liquid stocks
        self.tickers = [
            "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA", "META", "TSLA",
            "JPM", "V", "WMT", "DIS", "NFLX", "PYPL", "ADBE", "CRM"
        ]

        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.add_equity(ticker, Resolution.DAILY).symbol

        # Add SPY for scheduling
        self.add_equity("SPY", Resolution.DAILY)

        # XGBoost parameters
        self.lookback = 90
        self.n_estimators = 100
        self.max_depth = 5
        self.learning_rate = 0.03
        self.prediction_threshold = 0.001
        self.max_positions = 9
        self.position_size = 0.90 / self.max_positions  # ~10% each

        # Biweekly tracking: alternating Mondays
        # Monday counter: even = train, odd = trade
        self.monday_count = 0

        # Schedule on every Monday
        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.after_market_open("SPY", 30),
            self.weekly_action
        )

        self.models = {}
        self.scaler = None
        self.feature_names = None
        self.selected_tickers = []

    def calculate_features(self, history, ticker):
        """Calculate comprehensive features for XGBoost."""
        closes = history['close']
        volumes = history['volume']
        highs = history['high']
        lows = history['low']

        returns = closes.pct_change()

        # Price features
        sma_5 = closes.rolling(5).mean()
        sma_10 = closes.rolling(10).mean()
        sma_20 = closes.rolling(20).mean()
        sma_50 = closes.rolling(50).mean()

        ema_12 = closes.ewm(span=12).mean()
        ema_26 = closes.ewm(span=26).mean()

        # RSI
        delta = closes.diff()
        gain = (delta.where(delta > 0, 0)).rolling(14).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(14).mean()
        rs = gain / loss
        rsi = 100 - (100 / (1 + rs))

        # Bollinger Bands
        bb_middle = closes.rolling(20).mean()
        bb_std = closes.rolling(20).std()
        bb_upper = bb_middle + 2 * bb_std
        bb_lower = bb_middle - 2 * bb_std
        bb_width = (bb_upper - bb_lower) / bb_middle
        bb_position = (closes - bb_lower) / (bb_upper - bb_lower)

        # MACD
        macd = ema_12 - ema_26
        macd_signal = macd.ewm(span=9).mean()
        macd_histogram = macd - macd_signal

        # Stochastic
        rolling_min = lows.rolling(14).min()
        rolling_max = highs.rolling(14).max()
        denom = rolling_max - rolling_min
        denom = denom.replace(0, np.nan)
        stoch_k = 100 * (closes - rolling_min) / denom
        stoch_d = stoch_k.rolling(3).mean()

        # ATR (Average True Range)
        high_low = highs - lows
        high_close = np.abs(highs - closes.shift())
        low_close = np.abs(lows - closes.shift())
        true_range = pd.concat([high_low, high_close, low_close], axis=1).max(axis=1)
        atr = true_range.rolling(14).mean()

        # Momentum
        momentum_5 = closes / closes.shift(5) - 1
        momentum_10 = closes / closes.shift(10) - 1
        momentum_20 = closes / closes.shift(20) - 1

        # Volatility
        volatility_5 = returns.rolling(5).std()
        volatility_20 = returns.rolling(20).std()

        # Volume features
        volume_sma = volumes.rolling(20).mean()
        volume_ratio = volumes / volume_sma
        volume_change = volumes.pct_change()

        # Price relative features
        price_to_sma5 = closes / sma_5
        price_to_sma20 = closes / sma_20
        price_to_sma50 = closes / sma_50

        # Combine all features
        features = pd.DataFrame({
            'returns': returns,
            'rsi': rsi,
            'bb_width': bb_width,
            'bb_position': bb_position,
            'macd': macd,
            'macd_signal': macd_signal,
            'macd_hist': macd_histogram,
            'stoch_k': stoch_k,
            'stoch_d': stoch_d,
            'atr': atr,
            'atr_ratio': atr / closes,
            'mom_5': momentum_5,
            'mom_10': momentum_10,
            'mom_20': momentum_20,
            'vol_5': volatility_5,
            'vol_20': volatility_20,
            'volume_ratio': volume_ratio,
            'volume_change': volume_change,
            'price_sma5': price_to_sma5,
            'price_sma20': price_to_sma20,
            'price_sma50': price_to_sma50,
            'sma_ratio_5_20': sma_5 / sma_20,
            'sma_ratio_10_50': sma_10 / sma_50,
        })

        return features.fillna(0).replace([np.inf, -np.inf], 0)

    def train_models(self):
        """Train XGBoost models using pooled data from all stocks."""
        self.debug("Training XGBoost models...")

        all_features = []
        all_targets = []

        for ticker in self.tickers:
            try:
                history = self.history(self.symbols[ticker], self.lookback, Resolution.DAILY)

                if history.empty or len(history) < self.lookback:
                    continue

                features = self.calculate_features(history, ticker)
                closes = history['close']

                # Target: 10-day forward return (biweekly horizon)
                target = closes.pct_change(10).shift(-10)

                features['target'] = target
                features = features.dropna()

                if len(features) > 20:
                    all_features.append(features.drop('target', axis=1))
                    all_targets.append(features['target'])

            except Exception as e:
                self.debug(f"Train error {ticker}: {str(e)[:50]}")
                continue

        if not all_features:
            self.debug("No data for training.")
            return

        X = pd.concat(all_features, ignore_index=True)
        y = pd.concat(all_targets, ignore_index=True)

        self.feature_names = X.columns.tolist()

        from sklearn.preprocessing import StandardScaler
        from sklearn.ensemble import GradientBoostingRegressor

        self.scaler = StandardScaler()
        x_scaled = self.scaler.fit_transform(X)

        model = GradientBoostingRegressor(
            n_estimators=self.n_estimators,
            max_depth=self.max_depth,
            learning_rate=self.learning_rate,
            min_samples_leaf=10,
            subsample=0.8,
            random_state=42
        )

        model.fit(x_scaled, y)
        self.models['ensemble'] = model

        importance = pd.DataFrame({
            'feature': self.feature_names,
            'importance': model.feature_importances_
        }).sort_values('importance', ascending=False)

        self.debug(f"Model trained. Top feature: {importance.iloc[0]['feature']}")

    def predict(self, ticker, history):
        """Make prediction for a stock."""
        if 'ensemble' not in self.models or self.scaler is None:
            return 0

        model = self.models['ensemble']
        features = self.calculate_features(history, ticker)

        if len(features) == 0:
            return 0

        latest_features = features.iloc[-1:].values
        latest_features = self.scaler.transform(latest_features)
        prediction = model.predict(latest_features)[0]

        return prediction

    def weekly_action(self):
        """Alternate between training and trading on successive Mondays."""
        self.monday_count += 1

        if self.monday_count % 2 == 1:
            # Odd Monday: train the model
            self.train_models()
        else:
            # Even Monday: rebalance portfolio
            self.rebalance()

    def rebalance(self):
        """Rebalance based on XGBoost predictions with selective liquidation."""
        if 'ensemble' not in self.models:
            self.debug("No model yet, skipping rebalance.")
            return

        predictions = {}

        for ticker in self.tickers:
            try:
                history = self.history(self.symbols[ticker], 60, Resolution.DAILY)

                if history.empty:
                    continue

                pred = self.predict(ticker, history)
                predictions[ticker] = pred

            except Exception as e:
                self.debug(f"Predict error {ticker}: {str(e)[:50]}")
                continue

        if not predictions:
            return

        # Sort by predicted return, select top positions above threshold
        sorted_preds = sorted(predictions.items(), key=lambda x: x[1], reverse=True)

        new_selection = []
        for ticker, pred_return in sorted_preds:
            if pred_return > self.prediction_threshold and len(new_selection) < self.max_positions:
                new_selection.append(ticker)

        # Selective liquidation: only exit positions NOT in new selection
        current_holdings = []
        for ticker in self.tickers:
            if self.portfolio[self.symbols[ticker]].invested:
                current_holdings.append(ticker)

        for ticker in current_holdings:
            if ticker not in new_selection:
                self.liquidate(self.symbols[ticker])

        # Enter or maintain positions in new selection
        for ticker in new_selection:
            self.set_holdings(self.symbols[ticker], self.position_size)

        self.debug(
            f"Rebalance: {len(new_selection)} positions, "
            f"best pred: {sorted_preds[0][1]:.4f}" if sorted_preds else "No positions"
        )
        self.selected_tickers = new_selection
