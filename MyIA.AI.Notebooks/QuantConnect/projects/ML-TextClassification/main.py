# region imports
from AlgorithmImports import *
# endregion

class MLTextClassificationAlgorithm(QCAlgorithm):
    """
    NLP Text Classification Strategy.

    Strategy:
    - Use simulated news sentiment for trading decisions
    - Train text classifier (Naive Bayes) on sentiment labels
    - Features: Bag-of-words, TF-IDF from news headlines
    - Target: Next-day price direction (up/down)
    - Combine sentiment with technical indicators for hybrid model
    """

    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetCash(100000)

        # Assets
        self.tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]
        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.DAILY).Symbol

        # Text classification parameters
        self.lookback = 60
        self.rebalance_freq = 5
        self.vocabulary_size = 1000
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
        self.vectorizer = None
        self.scaler = None

    def SimulateNewsHeadlines(self, ticker, prices, volumes):
        """Simulate news headlines based on price/volume action.

        In production, this would use real news APIs.
        """
        headlines = []

        # Calculate recent changes
        returns = prices.pct_change()
        vol_changes = volumes.pct_change()

        for i in range(len(prices)):
            if i == 0:
                headlines.append("Market opens steady")
                continue

            ret = returns.iloc[i]
            vol_change = vol_changes.iloc[i] if i < len(vol_changes) else 0

            # Generate headline based on market action
            if ret > 0.03:
                if vol_change > 0.2:
                    headlines.append(f"{ticker} surges on heavy volume")
                else:
                    headlines.append(f"{ticker} rallies strongly")
            elif ret > 0.01:
                headlines.append(f"{ticker} gains ground")
            elif ret > -0.01:
                headlines.append(f"{ticker} trades mixed")
            elif ret > -0.03:
                headlines.append(f"{ticker} declines")
            else:
                if vol_change > 0.2:
                    headlines.append(f"{ticker} plummets on high volume")
                else:
                    headlines.append(f"{ticker} drops sharply")

        return headlines

    def CreateVocabulary(self, headlines):
        """Create vocabulary from headlines."""
        # Simple word tokenization
        all_words = []
        for headline in headlines:
            words = headline.lower().split()
            all_words.extend(words)

        # Count word frequencies
        from collections import Counter
        word_counts = Counter(all_words)

        # Get top words
        vocabulary = [word for word, _ in word_counts.most_common(self.vocabulary_size)]
        return {word: idx for idx, word in enumerate(vocabulary)}

    def HeadlineToFeatures(self, headline, vocabulary):
        """Convert headline to feature vector (bag-of-words)."""
        words = headline.lower().split()
        features = np.zeros(self.vocabulary_size)

        for word in words:
            if word in vocabulary:
                features[vocabulary[word]] = 1

        return features

    def TrainModel(self):
        """Train text classification model."""
        self.Debug("Training text classification model...")

        all_features = []
        all_targets = []

        for ticker in self.tickers:
            history = self.History(self.symbols[ticker], self.lookback, Resolution.Daily)

            if history.empty or len(history) < self.lookback:
                continue

            closes = history['close']
            volumes = history['volume']

            # Simulate headlines
            headlines = self.SimulateNewsHeadlines(ticker, closes, volumes)

            # Create vocabulary
            self.vocabulary = self.CreateVocabulary(headlines)

            # Create features and targets
            for i in range(1, len(headlines) - 1):
                features = self.HeadlineToFeatures(headlines[i], self.vocabulary)

                # Target: next day direction
                next_return = (closes.iloc[i + 1] - closes.iloc[i]) / closes.iloc[i]
                target = 1 if next_return > 0 else 0

                all_features.append(features)
                all_targets.append(target)

        if len(all_features) < 20:
            return

        # Train Naive Bayes classifier
        from sklearn.naive_bayes import MultinomialNB
        from sklearn.preprocessing import StandardScaler

        X = np.array(all_features)
        y = np.array(all_targets)

        self.scaler = StandardScaler()
        X_scaled = self.scaler.fit_transform(X)

        self.model = MultinomialNB()
        self.model.fit(X_scaled + 1, y)  # NB requires non-negative

        self.Debug("Text classification model trained.")

    def GetSentiment(self, ticker, history):
        """Get sentiment score from recent headlines."""
        if self.model is None or self.vocabulary is None:
            return 0.5

        closes = history['close']
        volumes = history['volume']

        # Simulate recent headlines
        headlines = self.SimulateNewsHeadlines(ticker, closes, volumes)

        # Get sentiment from last few headlines
        recent_headlines = headlines[-5:]
        sentiments = []

        for headline in recent_headlines:
            features = self.HeadlineToFeatures(headline, self.vocabulary)
            features_scaled = self.scaler.transform([features + 1])[0]
            prob = self.model.predict_proba([features_scaled])[0][1]
            sentiments.append(prob)

        return np.mean(sentiments)

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

    def Rebalance(self):
        """Rebalance based on sentiment + technical analysis."""
        if self.model is None:
            return

        predictions = {}

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], 60, Resolution.Daily)

                if history.empty:
                    continue

                # Get sentiment
                sentiment = self.GetSentiment(ticker, history)

                # Get technical features
                tech = self.GetTechnicalFeatures(history)

                # Hybrid score: sentiment + technical
                score = (
                    sentiment * 0.5 +
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
