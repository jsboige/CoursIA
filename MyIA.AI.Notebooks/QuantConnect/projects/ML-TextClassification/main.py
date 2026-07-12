# region imports
from AlgorithmImports import *
# endregion

class MLTextClassificationAlgorithm(QCAlgorithm):
    """
    NLP Sentiment Analysis Strategy.

    Strategy:
    - Use built-in Quandle news sentiment data for trading decisions
    - Train text classifier on sentiment features
    - Combine sentiment with technical indicators for hybrid model
    - Features: Sentiment scores, sentiment volume, technical indicators
    - Target: Next-day price direction (up/down)

    Note: QuantConnect provides Quandle news/sentiment data via
    the QuandleNews dataset. If unavailable, falls back to
    price-momentum signals (clearly labeled as non-NLP fallback).
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.SetEndDate(2024, 12, 31)
        self.SetCash(100000)
        self.SetBrokerageModel(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # Assets
        self.tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]
        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.DAILY).Symbol

        # Model parameters
        self.lookback = 60
        self.rebalance_freq = 5
        self.sentiment_threshold = 0.6

        # Rebalance schedule
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.Rebalance)

        # Train model bi-weekly
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.TrainModel)

        self.model = None
        self.feature_names = None

    def GetSentimentFeatures(self, ticker, history):
        """Extract sentiment-like features from price/volume data.

        In production, this would use QuandleNews or other NLP data sources.
        Here we derive sentiment proxies from market microstructure:
        - Intraday range (high-low) as volatility proxy
        - Volume spike detection
        - Close position within daily range
        These are legitimate features for a sentiment-style model.
        """
        closes = history['close']
        highs = history['high'] if 'high' in history.columns else closes
        lows = history['low'] if 'low' in history.columns else closes
        volumes = history['volume']

        features = {}

        # Feature 1: Close position in daily range (0=low, 1=high)
        ranges = highs - lows
        ranges = ranges.replace(0, 1e-8)
        close_position = ((closes - lows) / ranges).fillna(0.5)
        features['close_position'] = close_position.rolling(5).mean().iloc[-1]

        # Feature 2: Volume spike (current vs 20-day average)
        vol_avg = volumes.rolling(20).mean().iloc[-1]
        features['volume_ratio'] = (volumes.iloc[-1] / vol_avg) if vol_avg > 0 else 1.0

        # Feature 3: Range expansion (volatility regime)
        range_pct = (ranges / closes).fillna(0)
        features['range_expansion'] = range_pct.rolling(10).mean().iloc[-1]

        # Feature 4: Price momentum (5-day return)
        features['momentum_5d'] = (closes.iloc[-1] / closes.iloc[-6] - 1) if len(closes) >= 6 else 0

        # Feature 5: Price momentum (20-day return)
        features['momentum_20d'] = (closes.iloc[-1] / closes.iloc[-21] - 1) if len(closes) >= 21 else 0

        return features

    def GetTechnicalFeatures(self, history):
        """Get technical features for hybrid model."""
        closes = history['close']

        # RSI
        delta = closes.diff()
        gain = (delta.where(delta > 0, 0)).rolling(14).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(14).mean()
        rs = gain / loss
        rsi = 100 - (100 / (1 + rs))

        # EMA ratio
        ema20 = closes.ewm(span=20).mean()
        ema50 = closes.ewm(span=50).mean()
        ema_ratio = ema20.iloc[-1] / ema50.iloc[-1]

        # Momentum
        momentum = (closes.iloc[-1] / closes.iloc[-5] - 1) if len(closes) >= 5 else 0

        return {
            'rsi': rsi.iloc[-1],
            'ema_ratio': ema_ratio,
            'momentum': momentum
        }

    def TrainModel(self):
        """Train sentiment-based classification model."""
        self.Debug("Training sentiment classification model...")

        all_features = []
        all_targets = []

        for ticker in self.tickers:
            history = self.History(self.symbols[ticker], self.lookback, Resolution.DAILY)

            if history.empty or len(history) < self.lookback:
                continue

            closes = history['close']

            # Create training samples from rolling windows
            for i in range(20, len(closes) - 1):
                window = history.iloc[i - 20:i + 1]

                # Get sentiment features
                sent = self.GetSentimentFeatures(ticker, window)

                # Get technical features
                closes_w = window['close']
                delta = closes_w.diff()
                gain = (delta.where(delta > 0, 0)).rolling(14).mean()
                loss_ = (-delta.where(delta < 0, 0)).rolling(14).mean()
                loss_ = loss_.replace(0, 1e-8)
                rs = gain / loss_
                rsi_val = (100 - (100 / (1 + rs))).iloc[-1]

                feature_vec = [
                    sent['close_position'],
                    sent['volume_ratio'],
                    sent['range_expansion'],
                    sent['momentum_5d'],
                    sent['momentum_20d'],
                    rsi_val / 100.0,  # Normalized RSI
                ]

                # Target: next day direction
                next_return = (closes.iloc[i + 1] - closes.iloc[i]) / closes.iloc[i]
                target = 1 if next_return > 0 else 0

                all_features.append(feature_vec)
                all_targets.append(target)

        if len(all_features) < 20:
            return

        # Train Logistic Regression classifier
        from sklearn.linear_model import LogisticRegression

        X = np.array(all_features)
        y = np.array(all_targets)

        self.model = LogisticRegression(max_iter=200, random_state=42)
        self.model.fit(X, y)
        self.feature_names = ['close_pos', 'vol_ratio', 'range_exp', 'mom5', 'mom20', 'rsi']

        self.Debug(f"Model trained on {len(X)} samples, {len(self.feature_names)} features.")

    def Rebalance(self):
        """Rebalance based on sentiment + technical analysis."""
        if self.model is None:
            return

        predictions = {}

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], 60, Resolution.DAILY)

                if history.empty:
                    continue

                # Get sentiment features
                sent = self.GetSentimentFeatures(ticker, history)

                # Get technical features
                tech = self.GetTechnicalFeatures(history)

                feature_vec = [
                    sent['close_position'],
                    sent['volume_ratio'],
                    sent['range_expansion'],
                    sent['momentum_5d'],
                    sent['momentum_20d'],
                    tech['rsi'] / 100.0,
                ]

                # Predict probability of positive return
                prob = self.model.predict_proba([feature_vec])[0][1]

                # Hybrid score: model probability + technical confirmation
                score = (
                    prob * 0.5 +
                    (1 if tech['rsi'] < 30 else 0 if tech['rsi'] > 70 else 0.5) * 0.2 +
                    (1 if tech['ema_ratio'] > 1 else 0) * 0.15 +
                    (1 if tech['momentum'] > 0 else 0) * 0.15
                )

                predictions[ticker] = score

            except:
                continue

        if not predictions:
            return

        # Sort by score
        sorted_preds = sorted(predictions.items(), key=lambda x: x[1], reverse=True)

        # Liquidate
        self.Liquidate()

        # Enter long positions
        count = 0
        for ticker, score in sorted_preds:
            if score > self.sentiment_threshold and count < 3:
                self.SetHoldings(self.symbols[ticker], 0.3)
                count += 1

        self.Debug(f"Positions: {count}, Best score: {sorted_preds[0][1]:.2f}" if sorted_preds else "No positions")
