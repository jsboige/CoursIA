# region imports
from AlgorithmImports import *
# endregion

class MLDeepLearningAlgorithm(QCAlgorithm):
    """
    Deep Learning Strategy with LSTM/GRU models.

    Strategy:
    - Use LSTM (Long Short-Term Memory) networks for time series prediction
    - Sequence modeling: predict next returns from past price sequences
    - Features: OHLCV, technical indicators as input sequences
    - Architecture: LSTM layers + Dense output
    - Walk-forward training with periodic retraining
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.SetCash(100000)

        # Assets
        self.tickers = ["SPY", "QQQ", "IWM"]
        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.DAILY).Symbol

        # Deep learning parameters
        self.sequence_length = 20  # Lookback window
        self.epochs = 50
        self.batch_size = 32
        self.rebalance_freq = 5

        # Rebalance schedule
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.Rebalance)

        # Train model monthly
        self.Schedule.On(self.DateRules.MonthStart("SPY"),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.TrainModel)

        self.models = {}
        self.scalers = {}

    def PrepareSequences(self, prices, sequence_length=20):
        """Prepare sequences for LSTM training."""
        # Calculate returns
        returns = prices.pct_change().fillna(0)

        # Normalize
        mean = returns.mean()
        std = returns.std()
        normalized = (returns - mean) / std

        # Create sequences
        X, y = [], []
        for i in range(sequence_length, len(normalized)):
            X.append(normalized.iloc[i-sequence_length:i].values)
            y.append(normalized.iloc[i])

        return np.array(X), np.array(y), mean, std

    def BuildLSTMModel(self, input_shape):
        """Build LSTM model architecture."""
        from sklearn.linear_model import Ridge
        # Simplified: use Ridge as proxy (would use TensorFlow/PyTorch in production)
        return Ridge(alpha=1.0)

    def TrainModel(self):
        """Train LSTM models for each asset."""
        self.Debug("Training LSTM models...")

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], 252, Resolution.Daily)

                if history.empty or len(history) < 60:
                    continue

                closes = history['close']

                # Prepare sequences
                X, y, mean, std = self.PrepareSequences(closes, self.sequence_length)

                if len(X) < 30:
                    continue

                # Flatten for Ridge (simplified)
                X_flat = X.reshape(X.shape[0], -1)

                # Train model
                model = self.BuildLSTMModel(None)
                model.fit(X_flat, y)

                self.models[ticker] = model
                self.scalers[ticker] = {'mean': mean, 'std': std}

            except Exception as e:
                self.Debug(f"Error training {ticker}: {e}")
                continue

        self.Debug("LSTM models trained.")

    def Predict(self, ticker, history):
        """Make prediction using trained model."""
        if ticker not in self.models:
            return 0

        model = self.models[ticker]
        scaler = self.scalers[ticker]

        closes = history['close']
        returns = closes.pct_change().fillna(0)

        # Normalize
        normalized = (returns - scaler['mean']) / scaler['std']

        # Get last sequence
        if len(normalized) < self.sequence_length:
            return 0

        sequence = normalized.iloc[-self.sequence_length:].values
        X = sequence.reshape(1, -1)

        # Predict
        prediction = model.predict(X)[0]

        # Denormalize
        pred_return = prediction * scaler['std'] + scaler['mean']

        return pred_return

    def Rebalance(self):
        """Rebalance based on LSTM predictions."""
        if not self.models:
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
        for ticker, pred_return in sorted_preds:
            if pred_return > 0.001 and count < len(self.tickers):
                weight = 1.0 / len(self.tickers)
                self.SetHoldings(self.symbols[ticker], weight * 0.95)
                count += 1

        self.Debug(f"Positions: {count}, Best pred: {sorted_preds[0][1]:.4f}" if sorted_preds else "No positions")
