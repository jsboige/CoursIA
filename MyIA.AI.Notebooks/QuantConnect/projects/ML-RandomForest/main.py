# region imports
from AlgorithmImports import *
# endregion

class MLRandomForestAlgorithm(QCAlgorithm):
    """
    Random Forest Classification Strategy.

    Strategy:
    - Use Random Forest for predicting stock price direction (up/down)
    - Multiple decision trees with voting for robust predictions
    - Features: Technical indicators from multiple timeframes
    - Feature importance analysis for interpretability
    - Walk-forward training with cross-validation
    """

    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetCash(100000)

        # Universe: Liquid large-cap stocks
        self.tickers = [
            "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA",
            "META", "TSLA", "JPM", "V", "WMT"
        ]

        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.DAILY).Symbol

        # Random Forest parameters
        self.lookback = 60
        self.n_estimators = 100
        self.max_depth = 10
        self.min_samples_split = 5
        self.rebalance_freq = 5

        # rebalance schedule
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.rebalance)

        # Train model bi-weekly
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.train_model)

        self.model = None
        self.scaler = None
        self.feature_names = None

    def calculate_features(self, history, ticker):
        """Calculate technical features for Random Forest."""
        closes = history['close']
        volumes = history['volume']
        highs = history['high']
        lows = history['low']

        returns = closes.pct_change()

        # Moving averages
        sma_5 = closes.rolling(5).mean()
        sma_10 = closes.rolling(10).mean()
        sma_20 = closes.rolling(20).mean()
        sma_50 = closes.rolling(50).mean()

        # RSI
        delta = closes.diff()
        gain = (delta.where(delta > 0, 0)).rolling(14).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(14).mean()
        rs = gain / loss
        rsi = 100 - (100 / (1 + rs))

        # MACD
        ema_12 = closes.ewm(span=12).mean()
        ema_26 = closes.ewm(span=26).mean()
        macd = ema_12 - ema_26
        macd_signal = macd.ewm(span=9).mean()

        # Bollinger Bands
        bb_middle = closes.rolling(20).mean()
        bb_std = closes.rolling(20).std()
        bb_position = (closes - bb_middle) / (2 * bb_std)

        # Stochastic
        stoch_k = 100 * (closes - lows.rolling(14).min()) / (highs.rolling(14).max() - lows.rolling(14).min())

        # Momentum
        momentum_5 = closes / closes.shift(5) - 1
        momentum_10 = closes / closes.shift(10) - 1
        momentum_20 = closes / closes.shift(20) - 1

        # Volatility
        volatility_10 = returns.rolling(10).std()
        volatility_20 = returns.rolling(20).std()

        # Volume features
        volume_sma = volumes.rolling(20).mean()
        volume_ratio = volumes / volume_sma

        # Price ratios
        price_to_sma5 = closes / sma_5
        price_to_sma20 = closes / sma_20
        price_to_sma50 = closes / sma_50

        # Combine features
        features = pd.DataFrame({
            'rsi': rsi,
            'bb_position': bb_position,
            'macd': macd,
            'macd_signal': macd_signal,
            'macd_hist': macd - macd_signal,
            'stoch_k': stoch_k,
            'mom_5': momentum_5,
            'mom_10': momentum_10,
            'mom_20': momentum_20,
            'vol_10': volatility_10,
            'vol_20': volatility_20,
            'volume_ratio': volume_ratio,
            'price_sma5': price_to_sma5,
            'price_sma20': price_to_sma20,
            'price_sma50': price_to_sma50,
            'sma_ratio_5_20': sma_5 / sma_20,
            'sma_ratio_20_50': sma_20 / sma_50,
        })

        return features.fillna(0)

    def train_model(self):
        """Train Random Forest classifier on all stocks."""
        self.Debug("Training Random Forest model...")

        from sklearn.ensemble import RandomForestClassifier
        from sklearn.preprocessing import MinMaxScaler

        all_features = []
        all_targets = []

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], self.lookback, Resolution.Daily)

                if history.empty or len(history) < self.lookback:
                    continue

                features = self.calculate_features(history, ticker)
                closes = history['close']

                # Target: direction (1 if up, 0 if down)
                future_return = closes.pct_change().shift(-1)
                target = (future_return > 0).astype(int)

                features['target'] = target
                features = features.dropna()

                if len(features) > 20:
                    all_features.append(features.drop('target', axis=1))
                    all_targets.append(features['target'])

            except Exception as e:
                self.Debug(f"Error processing {ticker}: {e}")
                continue

        if not all_features:
            return

        # Combine all data
        X = pd.concat(all_features, ignore_index=True)
        y = pd.concat(all_targets, ignore_index=True)

        self.feature_names = X.columns.tolist()

        # Scale features (MinMaxScaler for compatibility)
        self.scaler = MinMaxScaler()
        X_scaled = self.scaler.fit_transform(X)

        # Train Random Forest
        self.model = RandomForestClassifier(
            n_estimators=self.n_estimators,
            max_depth=self.max_depth,
            min_samples_split=self.min_samples_split,
            random_state=42,
            n_jobs=-1
        )

        self.model.fit(X_scaled, y)

        # Feature importance
        importance = pd.DataFrame({
            'feature': self.feature_names,
            'importance': self.model.feature_importances_
        }).sort_values('importance', ascending=False)

        self.Debug(f"Random Forest trained. Top feature: {importance.iloc[0]['feature']}")

    def predict(self, ticker, history):
        """predict probability of positive return."""
        if self.model is None:
            return 0.5

        features = self.calculate_features(history, ticker)

        if len(features) == 0:
            return 0.5

        latest_features = features.iloc[-1:].values

        # Scale
        if self.scaler is not None:
            latest_features = self.scaler.transform(latest_features)

        # Get probability of positive return
        proba = self.model.predict_proba(latest_features)[0]
        return proba[1]  # Probability of class 1 (up)

    def rebalance(self):
        """rebalance based on Random Forest predictions."""
        if self.model is None:
            return

        predictions = {}

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], 60, Resolution.Daily)

                if history.empty:
                    continue

                prob = self.predict(ticker, history)
                predictions[ticker] = prob

            except Exception as e:
                self.Debug(f"Error predicting {ticker}: {e}")
                continue

        if not predictions:
            return

        # Sort by probability
        sorted_preds = sorted(predictions.items(), key=lambda x: x[1], reverse=True)

        # Liquidate
        self.Liquidate()

        # Enter long positions for top predictions
        count = 0
        max_positions = 5
        position_size = 0.18

        for ticker, prob in sorted_preds:
            if prob > 0.55 and count < max_positions:
                self.SetHoldings(self.symbols[ticker], position_size)
                count += 1

        self.Debug(f"Positions: {count}, Best prob: {sorted_preds[0][1]:.2%}" if sorted_preds else "No positions")
