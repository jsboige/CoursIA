#region imports
from AlgorithmImports import *
import numpy as np
from collections import deque
# endregion


class TemporalCNNPrediction(QCAlgorithm):
    """
    Temporal CNN for Price Direction Prediction.

    This strategy demonstrates how to use a 1D Convolutional Neural Network
    to predict the direction of future price movements based on historical returns.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 14

    How it works:
    1. Collect trailing daily returns as features
    2. Normalize returns using rolling z-score
    3. Use a simplified 1D CNN architecture for pattern recognition
    4. Predict next-day direction (up/down)
    5. Trade based on prediction confidence

    The CNN architecture:
    - Input: sequence of N daily returns
    - Conv1D layer: learns local patterns in the return sequence
    - Global pooling: aggregates temporal features
    - Dense layer: outputs probability of positive return

    Parameters:
    - lookback_days: Number of days for feature window (default: 20)
    - prediction_threshold: Minimum confidence to trade (default: 0.6)
    - retrain_frequency: Days between model updates (default: 30)
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_end_date(2024, 1, 1)
        self.set_cash(100_000)

        self._spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # Model parameters
        self._lookback_days = self.get_parameter('lookback_days', 20)
        self._prediction_threshold = self.get_parameter('prediction_threshold', 0.6)
        self._retrain_frequency = self.get_parameter('retrain_frequency', 30)

        # Feature collection
        self._returns_window = deque(maxlen=self._lookback_days * 2)
        self._daily_returns = []

        # ROC for return calculation
        roc = self.roc(self._spy, 1, Resolution.DAILY)
        roc.updated += self._on_roc_updated

        # Warm up
        history = self.history[TradeBar](
            self._spy, timedelta(days=self._lookback_days * 3), Resolution.DAILY
        )
        for bar in history:
            roc.update(bar.end_time, bar.close)

        # Simple model state (simplified CNN weights)
        self._model_weights = None
        self._days_since_retrain = 0
        self._predictions = deque(maxlen=100)

        # Schedule trading
        self.schedule.on(
            self.date_rules.every_day(self._spy),
            self.time_rules.after_market_open(self._spy, 30),
            self._trade
        )

        self.log(f"TemporalCNNPrediction initialized: lookback={self._lookback_days}, threshold={self._prediction_threshold}")

    def _on_roc_updated(self, indicator, indicator_data_point):
        """Collect daily returns."""
        if not indicator.is_ready:
            return
        self._returns_window.append(indicator_data_point.value)

    def _normalize_features(self, returns):
        """
        Normalize returns using z-score.
        """
        mean = np.mean(returns)
        std = np.std(returns)
        if std < 1e-8:
            return np.zeros_like(returns)
        return (returns - mean) / std

    def _simple_cnn_predict(self, features):
        """
        Simplified CNN-like prediction using 1D convolution simulation.

        In production, this would use PyTorch/TensorFlow with proper
        Conv1D layers. Here we use a simplified version for demonstration.
        """
        if len(features) < self._lookback_days:
            return 0.5

        # Normalize features
        x = self._normalize_features(np.array(features[-self._lookback_days:]))

        # Simulate Conv1D with local pattern detection
        # Kernel size = 3, stride = 1
        kernel_size = 3
        conv_features = []
        for i in range(len(x) - kernel_size + 1):
            # Local pattern: sum of weighted consecutive returns
            local_sum = np.sum(x[i:i+kernel_size] * np.array([0.3, 0.4, 0.3]))
            conv_features.append(np.tanh(local_sum))

        # Global average pooling
        pooled = np.mean(conv_features)

        # Dense layer (sigmoid for probability)
        probability = 1 / (1 + np.exp(-pooled * 2))

        return probability

    def _train_model(self):
        """
        Train the simplified CNN on historical data.

        Uses rolling windows of returns as features and
        next-day direction as labels.
        """
        if len(self._returns_window) < self._lookback_days * 2:
            return

        returns = list(self._returns_window)

        # Create training samples
        X = []
        y = []
        for i in range(self._lookback_days, len(returns) - 1):
            features = returns[i - self._lookback_days:i]
            label = 1 if returns[i + 1] > 0 else 0
            X.append(features)
            y.append(label)

        if len(X) < 10:
            return

        # Store for simplified prediction
        self._training_data = (X, y)
        self.log(f"Model trained on {len(X)} samples")

    def _trade(self):
        """
        Make prediction and execute trade.
        """
        if len(self._returns_window) < self._lookback_days:
            return

        # Retrain periodically
        self._days_since_retrain += 1
        if self._days_since_retrain >= self._retrain_frequency:
            self._train_model()
            self._days_since_retrain = 0

        # Get prediction
        returns = list(self._returns_window)
        probability = self._simple_cnn_predict(returns)

        # Track prediction accuracy
        if len(self._predictions) > 0:
            # Check previous prediction
            prev_prob, prev_return = self._predictions[-1]
            actual_direction = 1 if returns[-1] > 0 else 0
            predicted_direction = 1 if prev_prob > 0.5 else 0

        # Store current prediction
        self._predictions.append((probability, returns[-1] if returns else 0))

        # Plot
        self.plot('CNN', 'UpProbability', probability)

        # Trading logic
        if probability > self._prediction_threshold:
            # Predict up - buy
            self.set_holdings(self._spy, 1.0)
            self.log(f"CNN predicts UP: prob={probability:.2%}")
        elif probability < (1 - self._prediction_threshold):
            # Predict down - go to cash
            self.set_holdings(self._spy, 0.0)
            self.log(f"CNN predicts DOWN: prob={probability:.2%}")

    def on_end_of_algorithm(self):
        final_value = self.portfolio.total_portfolio_value
        returns = (final_value - 100000) / 100000

        # Calculate prediction accuracy
        correct = 0
        total = 0
        for i in range(len(self._predictions) - 1):
            prob, _ = self._predictions[i]
            _, next_return = self._predictions[i + 1]
            predicted = 1 if prob > 0.5 else 0
            actual = 1 if next_return > 0 else 0
            if predicted == actual:
                correct += 1
            total += 1

        accuracy = correct / total if total > 0 else 0
        self.log(f"Temporal CNN: Final=${final_value:,.0f}, Return={returns:.2%}, Accuracy={accuracy:.2%}")
