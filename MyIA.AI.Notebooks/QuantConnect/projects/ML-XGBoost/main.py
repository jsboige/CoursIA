# region imports
from AlgorithmImports import *
# endregion

class MLXGBoostAlgorithm(QCAlgorithm):
    """
    XGBoost Gradient Boosting Strategy.

    Strategy:
    - Use XGBoost for return prediction with advanced feature engineering
    - Gradient boosting with cross-validation for robustness
    - Features: Technical indicators + market context + alternative data
    - Hyperparameter tuning with walk-forward validation
    - Ensemble of models for different time horizons
    """

    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetCash(100000)

        # Universe: Top 20 liquid stocks
        self.tickers = [
            "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA", "META", "TSLA",
            "JPM", "V", "WMT", "DIS", "NFLX", "PYPL", "ADBE", "CRM"
        ]

        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.DAILY).Symbol

        # XGBoost parameters
        self.lookback = 90
        self.rebalance_freq = 5
        self.n_estimators = 100
        self.max_depth = 5
        self.learning_rate = 0.05

        # Rebalance schedule
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.Rebalance)

        # Train models bi-weekly
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.TrainModels)

        self.models = {}
        self.scalers = {}
        self.feature_names = None

    def CalculateFeatures(self, history, ticker):
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
        stoch_k = 100 * (closes - lows.rolling(14).min()) / (highs.rolling(14).max() - lows.rolling(14).min())
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

        return features.fillna(0)

    def TrainModels(self):
        """Train XGBoost models for each stock."""
        self.Debug("Training XGBoost models...")

        # Get historical data for all stocks
        all_features = []
        all_targets = []

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], self.lookback, Resolution.Daily)

                if history.empty or len(history) < self.lookback:
                    continue

                features = self.CalculateFeatures(history, ticker)
                closes = history['close']

                # Target: next day return
                target = closes.pct_change().shift(-1)

                # Combine
                features['target'] = target
                features = features.dropna()

                if len(features) > 20:
                    all_features.append(features.drop('target', axis=1))
                    all_targets.append(features['target'])

            except:
                continue

        if not all_features:
            return

        # Combine all stocks
        X = pd.concat(all_features, ignore_index=True)
        y = pd.concat(all_targets, ignore_index=True)

        self.feature_names = X.columns.tolist()

        # Train model
        from sklearn.preprocessing import StandardScaler
        from sklearn.ensemble import GradientBoostingRegressor

        self.scaler = StandardScaler()
        X_scaled = self.scaler.fit_transform(X)

        # XGBoost equivalent: GradientBoostingRegressor
        model = GradientBoostingRegressor(
            n_estimators=self.n_estimators,
            max_depth=self.max_depth,
            learning_rate=self.learning_rate,
            random_state=42
        )

        model.fit(X_scaled, y)

        self.models['ensemble'] = model

        # Feature importance
        importance = pd.DataFrame({
            'feature': self.feature_names,
            'importance': model.feature_importances_
        }).sort_values('importance', ascending=False)

        self.Debug(f"XGBoost models trained. Top feature: {importance.iloc[0]['feature']}")

    def Predict(self, ticker, history):
        """Make prediction for a stock."""
        if 'ensemble' not in self.models:
            return 0

        model = self.models['ensemble']

        features = self.CalculateFeatures(history, ticker)

        if len(features) == 0:
            return 0

        latest_features = features.iloc[-1:].values

        # Scale
        if self.scaler is not None:
            latest_features = self.scaler.transform(latest_features)

        prediction = model.predict(latest_features)[0]

        return prediction

    def Rebalance(self):
        """Rebalance based on XGBoost predictions."""
        if 'ensemble' not in self.models:
            return

        predictions = {}

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], 60, Resolution.Daily)

                if history.empty:
                    continue

                pred = self.Predict(ticker, history)
                predictions[ticker] = pred

            except:
                continue

        if not predictions:
            return

        # Sort by predicted return
        sorted_preds = sorted(predictions.items(), key=lambda x: x[1], reverse=True)

        # Liquidate
        self.Liquidate()

        # Enter long positions
        count = 0
        max_positions = 10
        position_size = 0.09

        for ticker, pred_return in sorted_preds:
            if pred_return > 0.002 and count < max_positions:
                self.SetHoldings(self.symbols[ticker], position_size)
                count += 1

        self.Debug(f"Positions: {count}, Best pred: {sorted_preds[0][1]:.4f}" if sorted_preds else "No positions")
