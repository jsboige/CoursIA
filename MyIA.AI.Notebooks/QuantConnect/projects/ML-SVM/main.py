# region imports
from AlgorithmImports import *
# endregion

class MLSVMAlgorithm(QCAlgorithm):
    """
    Support Vector Machine Classification Strategy.

    Strategy:
    - Use SVM for predicting stock price direction
    - RBF kernel for non-linear decision boundaries
    - Feature standardization for optimal SVM performance
    - Probability estimates via Platt scaling
    - Margin analysis for confidence-weighted position sizing
    """

    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetCash(100000)

        # Universe: Major ETFs for diversification
        self.tickers = ["SPY", "QQQ", "IWM", "DIA", "TLT", "GLD", "VNQ", "EEM"]

        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.DAILY).Symbol

        # SVM parameters
        self.lookback = 90
        self.C = 1.0  # Regularization parameter
        self.kernel = 'rbf'
        self.gamma = 'scale'
        self.rebalance_freq = 5

        # Rebalance schedule
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.Rebalance)

        # Train model monthly
        self.Schedule.On(self.DateRules.MonthStart("SPY"),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.TrainModel)

        self.model = None
        self.scaler = None
        self.feature_names = None

    def CalculateFeatures(self, history, ticker):
        """Calculate features optimized for SVM."""
        closes = history['close']
        volumes = history['volume']
        highs = history['high']
        lows = history['low']

        returns = closes.pct_change()

        # Price-based features
        sma_5 = closes.rolling(5).mean()
        sma_20 = closes.rolling(20).mean()
        sma_50 = closes.rolling(50).mean()

        # RSI (normalized 0-1 for SVM)
        delta = closes.diff()
        gain = (delta.where(delta > 0, 0)).rolling(14).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(14).mean()
        rs = gain / loss
        rsi = (100 - (100 / (1 + rs))) / 100  # Normalize to 0-1

        # MACD
        ema_12 = closes.ewm(span=12).mean()
        ema_26 = closes.ewm(span=26).mean()
        macd = ema_12 - ema_26
        macd_signal = macd.ewm(span=9).mean()

        # Bollinger Band position (-1 to 1)
        bb_middle = closes.rolling(20).mean()
        bb_std = closes.rolling(20).std()
        bb_position = (closes - bb_middle) / (2 * bb_std)
        bb_position = bb_position.clip(-2, 2) / 2  # Clip and normalize

        # Momentum
        momentum_5 = closes / closes.shift(5) - 1
        momentum_10 = closes / closes.shift(10) - 1
        momentum_20 = closes / closes.shift(20) - 1

        # Volatility (normalized)
        volatility_20 = returns.rolling(20).std()

        # Volume features
        volume_sma = volumes.rolling(20).mean()
        volume_ratio = volumes / volume_sma
        volume_ratio = volume_ratio.clip(0, 5) / 5  # Normalize

        # Price relative to SMAs
        price_to_sma5 = closes / sma_5 - 1
        price_to_sma20 = closes / sma_20 - 1
        price_to_sma50 = closes / sma_50 - 1

        # Trend strength
        adx = self.CalculateADX(highs, lows, closes, 14)

        # Combine features
        features = pd.DataFrame({
            'rsi': rsi,
            'bb_position': bb_position,
            'macd': macd / closes.iloc[-1] if len(closes) > 0 else macd,
            'macd_hist': (macd - macd_signal) / closes.iloc[-1] if len(closes) > 0 else macd - macd_signal,
            'mom_5': momentum_5,
            'mom_10': momentum_10,
            'mom_20': momentum_20,
            'volatility': volatility_20,
            'volume_ratio': volume_ratio,
            'price_sma5': price_to_sma5,
            'price_sma20': price_to_sma20,
            'price_sma50': price_to_sma50,
            'adx': adx / 100,  # Normalize to 0-1
        })

        return features.fillna(0)

    def CalculateADX(self, highs, lows, closes, period=14):
        """Calculate Average Directional Index."""
        high_diff = highs.diff()
        low_diff = -lows.diff()

        plus_dm = high_diff.where((high_diff > low_diff) & (high_diff > 0), 0)
        minus_dm = low_diff.where((low_diff > high_diff) & (low_diff > 0), 0)

        high_low = highs - lows
        high_close = abs(highs - closes.shift())
        low_close = abs(lows - closes.shift())
        tr = pd.concat([high_low, high_close, low_close], axis=1).max(axis=1)

        atr = tr.rolling(period).mean()

        plus_di = 100 * (plus_dm.rolling(period).mean() / atr)
        minus_di = 100 * (minus_dm.rolling(period).mean() / atr)

        dx = 100 * abs(plus_di - minus_di) / (plus_di + minus_di + 0.0001)
        adx = dx.rolling(period).mean()

        return adx.fillna(25)  # Default neutral value

    def TrainModel(self):
        """Train SVM classifier."""
        self.Debug("Training SVM model...")

        from sklearn.svm import SVC
        from sklearn.preprocessing import StandardScaler

        all_features = []
        all_targets = []

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], self.lookback, Resolution.Daily)

                if history.empty or len(history) < self.lookback:
                    continue

                features = self.CalculateFeatures(history, ticker)
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

        # Standardize features (critical for SVM)
        self.scaler = StandardScaler()
        X_scaled = self.scaler.fit_transform(X)

        # Train SVM with probability estimates
        self.model = SVC(
            C=self.C,
            kernel=self.kernel,
            gamma=self.gamma,
            probability=True,
            random_state=42
        )

        self.model.fit(X_scaled, y)

        # Calculate accuracy
        train_accuracy = (self.model.predict(X_scaled) == y).mean()
        self.Debug(f"SVM trained. Accuracy: {train_accuracy:.2%}")

    def Predict(self, ticker, history):
        """Predict probability of positive return."""
        if self.model is None:
            return 0.5

        features = self.CalculateFeatures(history, ticker)

        if len(features) == 0:
            return 0.5

        latest_features = features.iloc[-1:].values

        # Scale
        if self.scaler is not None:
            latest_features = self.scaler.transform(latest_features)

        # Get probability of positive return
        proba = self.model.predict_proba(latest_features)[0]
        return proba[1]

    def GetDecisionMargin(self, ticker, history):
        """Get decision function margin for confidence."""
        if self.model is None:
            return 0

        features = self.CalculateFeatures(history, ticker)

        if len(features) == 0:
            return 0

        latest_features = features.iloc[-1:].values

        if self.scaler is not None:
            latest_features = self.scaler.transform(latest_features)

        return self.model.decision_function(latest_features)[0]

    def Rebalance(self):
        """Rebalance based on SVM predictions with confidence weighting."""
        if self.model is None:
            return

        predictions = {}

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], 60, Resolution.Daily)

                if history.empty:
                    continue

                prob = self.Predict(ticker, history)
                margin = self.GetDecisionMargin(ticker, history)

                predictions[ticker] = {
                    'prob': prob,
                    'margin': margin
                }

            except Exception as e:
                self.Debug(f"Error predicting {ticker}: {e}")
                continue

        if not predictions:
            return

        # Sort by probability
        sorted_preds = sorted(predictions.items(), key=lambda x: x[1]['prob'], reverse=True)

        # Liquidate
        self.Liquidate()

        # Enter long positions with confidence-weighted sizing
        count = 0
        max_positions = 4
        base_size = 0.22

        for ticker, pred in sorted_preds:
            prob = pred['prob']
            margin = pred['margin']

            if prob > 0.55 and count < max_positions:
                # Confidence-weighted position size
                confidence = min(abs(margin) / 2, 1)  # Normalize margin
                position_size = base_size * (0.5 + 0.5 * confidence)

                self.SetHoldings(self.symbols[ticker], position_size)
                count += 1

        self.Debug(f"Positions: {count}, Best prob: {sorted_preds[0][1]['prob']:.2%}" if sorted_preds else "No positions")
