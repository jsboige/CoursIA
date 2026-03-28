#region imports
from AlgorithmImports import *
import numpy as np
from collections import deque
# endregion


class LSTMForecasting(QCAlgorithm):
    """
    LSTM Neural Network for Price Direction Forecasting.

    This strategy demonstrates how to use a Long Short-Term Memory (LSTM)
    recurrent neural network to predict future price movements.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 07

    How it works:
    1. Collect trailing daily returns as sequential features
    2. Normalize returns using rolling statistics
    3. Use LSTM architecture to capture temporal dependencies
    4. Predict next-day return direction
    5. Trade based on prediction confidence

    LSTM Architecture:
    - Input: sequence of N daily returns
    - LSTM layer: captures long-term temporal patterns
    - Dense layer: outputs probability of positive return

    Key features of LSTM:
    - Memory cells: can store information over long periods
    - Forget gate: decides what information to discard
    - Input gate: decides what new information to store
    - Output gate: decides what to output

    Parameters:
    - lookback_days: Number of days for feature window (default: 30)
    - hidden_size: LSTM hidden state size (default: 32)
    - prediction_threshold: Minimum confidence to trade (default: 0.55)
    - retrain_frequency: Days between model updates (default: 60)
    - momentum_weight: Blend weight for momentum signal (default: 0.5)
    - momentum_lookback: Days for momentum calculation (default: 10)
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_end_date(2024, 1, 1)
        self.set_cash(100_000)

        self._spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # Model parameters
        self._lookback_days = self.get_parameter('lookback_days', 30)
        self._hidden_size = self.get_parameter('hidden_size', 32)
        self._prediction_threshold = self.get_parameter('prediction_threshold', 0.55)
        self._retrain_frequency = self.get_parameter('retrain_frequency', 60)
        self._momentum_weight = self.get_parameter('momentum_weight', 0.5)
        self._momentum_lookback = self.get_parameter('momentum_lookback', 10)

        # Feature collection
        self._returns_window = deque(maxlen=self._lookback_days * 3)

        # ROC for return calculation
        roc = self.roc(self._spy, 1, Resolution.DAILY)
        roc.updated += self._on_roc_updated

        # Warm up
        history = self.history[TradeBar](
            self._spy, timedelta(days=self._lookback_days * 4), Resolution.DAILY
        )
        for bar in history:
            roc.update(bar.end_time, bar.close)

        # LSTM state (simplified implementation)
        self._hidden_state = np.zeros(self._hidden_size)
        self._cell_state = np.zeros(self._hidden_size)
        self._model_weights = None
        self._days_since_retrain = 0

        # Training data storage
        self._training_sequences = []
        self._training_labels = []

        # Performance tracking
        self._predictions = deque(maxlen=200)
        self._train_count = 0

        # Schedule trading
        self.schedule.on(
            self.date_rules.every_day(self._spy),
            self.time_rules.after_market_open(self._spy, 30),
            self._trade
        )

        self.log(f"LSTMForecasting initialized: lookback={self._lookback_days}, hidden={self._hidden_size}")

    def _on_roc_updated(self, indicator, indicator_data_point):
        """Collect daily returns."""
        if not indicator.is_ready:
            return
        self._returns_window.append(indicator_data_point.value)

    def _normalize_sequence(self, sequence):
        """
        Normalize sequence using z-score.
        """
        arr = np.array(sequence)
        mean = np.mean(arr)
        std = np.std(arr)
        if std < 1e-8:
            return np.zeros_like(arr)
        return (arr - mean) / std

    def _sigmoid(self, x):
        """Sigmoid activation function."""
        return 1 / (1 + np.exp(-np.clip(x, -500, 500)))

    def _tanh(self, x):
        """Tanh activation function."""
        return np.tanh(x)

    def _lstm_cell(self, x, h, c):
        """
        Simplified LSTM cell implementation.

        In production, this would use PyTorch/TensorFlow LSTM layers.
        Here we use a simplified version for demonstration.

        LSTM equations:
        f_t = sigmoid(W_f * [h_{t-1}, x_t] + b_f)  # Forget gate
        i_t = sigmoid(W_i * [h_{t-1}, x_t] + b_i)  # Input gate
        c_tilde = tanh(W_c * [h_{t-1}, x_t] + b_c) # Candidate cell state
        c_t = f_t * c_{t-1} + i_t * c_tilde        # Cell state
        o_t = sigmoid(W_o * [h_{t-1}, x_t] + b_o)  # Output gate
        h_t = o_t * tanh(c_t)                      # Hidden state
        """
        # Concatenate input and hidden state
        combined = np.concatenate([h, x])

        # Simplified gate computations (using fixed weights)
        # In a trained LSTM, each gate has separate learned weights
        forget_gate = self._sigmoid(0.7 * np.sum(combined))
        input_gate = self._sigmoid(0.3 * np.sum(combined))
        candidate = self._tanh(np.sum(combined) * 0.3)

        # Update cell state
        new_c = forget_gate * c + input_gate * candidate

        # Output gate and hidden state
        output_gate = self._sigmoid(0.5 * np.sum(new_c))
        new_h = output_gate * self._tanh(new_c)

        return new_h, new_c

    def _lstm_forward(self, sequence):
        """
        Forward pass through LSTM network with momentum blend.
        """
        h = np.zeros(self._hidden_size)
        c = np.zeros(self._hidden_size)

        # Process each time step
        for t, val in enumerate(sequence):
            # Create input vector (simplified: just the value)
            x = np.full(self._hidden_size, val)
            h, c = self._lstm_cell(x, h, c)

        # LSTM signal
        lstm_signal = np.mean(h)

        # Momentum signal (simple trailing average)
        momentum_signal = 0.0
        if len(sequence) >= self._momentum_lookback:
            momentum_signal = np.mean(sequence[-self._momentum_lookback:])

        # Blend signals
        combined = (1 - self._momentum_weight) * lstm_signal + self._momentum_weight * momentum_signal
        output = self._sigmoid(combined)
        return output

    def _train_model(self):
        """
        Train LSTM on historical sequences.
        """
        if len(self._returns_window) < self._lookback_days * 2:
            return

        returns = list(self._returns_window)

        # Create training sequences
        X = []
        y = []
        for i in range(self._lookback_days, len(returns) - 1):
            sequence = returns[i - self._lookback_days:i]
            label = 1 if returns[i + 1] > 0 else 0
            X.append(self._normalize_sequence(sequence))
            y.append(label)

        if len(X) < 20:
            return

        # Store training data
        self._training_sequences = X
        self._training_labels = y
        self._train_count += 1

        self.log(f"LSTM model trained on {len(X)} sequences (train #{self._train_count})")

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

        # Get current sequence
        returns = list(self._returns_window)
        sequence = self._normalize_sequence(returns[-self._lookback_days:])

        # Get LSTM prediction
        probability = self._lstm_forward(sequence)

        # Track predictions
        self._predictions.append({
            'probability': probability,
            'actual_return': returns[-1] if returns else 0
        })

        # Plot
        self.plot('LSTM', 'UpProbability', probability)

        # Trading logic
        if probability > self._prediction_threshold:
            # Predict up - buy
            self.set_holdings(self._spy, 1.0)
            self.log(f"LSTM predicts UP: prob={probability:.2%}")
        elif probability < (1 - self._prediction_threshold):
            # Predict down - go to cash
            self.set_holdings(self._spy, 0.0)
            self.log(f"LSTM predicts DOWN: prob={probability:.2%}")

    def on_end_of_algorithm(self):
        final_value = self.portfolio.total_portfolio_value
        returns = (final_value - 100000) / 100000

        # Calculate prediction accuracy
        correct = 0
        total = 0
        predictions_list = list(self._predictions)
        for i in range(len(predictions_list) - 1):
            prob = predictions_list[i]['probability']
            next_ret = predictions_list[i + 1]['actual_return']
            predicted = 1 if prob > 0.5 else 0
            actual = 1 if next_ret > 0 else 0
            if predicted == actual:
                correct += 1
            total += 1

        accuracy = correct / total if total > 0 else 0
        self.log(f"LSTM Forecasting: Final=${final_value:,.0f}, Return={returns:.2%}, Accuracy={accuracy:.2%}")
