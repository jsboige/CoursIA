#region imports
from AlgorithmImports import *
import numpy as np
from collections import deque
# endregion


class ChronosFoundationForecasting(QCAlgorithm):
    """
    Chronos Foundation Model for Time Series Forecasting.

    This strategy demonstrates how to use the Chronos foundation model
    (Amazon's pretrained time-series model) for financial forecasting.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 18

    About Chronos:
    - Developed by Amazon Science (2024)
    - Pretrained on large corpus of time series data
    - Zero-shot forecasting capability
    - Based on T5 transformer architecture
    - Tokenizes continuous values into discrete tokens
    - Treats forecasting as language modeling

    How it works:
    1. Collect historical price data
    2. Quantize values into discrete tokens
    3. Use transformer to predict future tokens
    4. Dequantize to get forecast distribution
    5. Trade based on predicted direction

    Note: This is a simplified implementation demonstrating the concept.
    Full implementation would use the chronos-forecasting package:
    ```
    from chronos import ChronosPipeline
    pipeline = ChronosPipeline.from_pretrained("amazon/chronos-t5-small")
    forecast = pipeline.predict(context, prediction_length=1)
    ```

    Parameters:
    - context_length: Number of historical points (default: 64)
    - prediction_length: Forecast horizon (default: 1)
    - num_samples: Monte Carlo samples for uncertainty (default: 100)
    - confidence_threshold: Minimum confidence to trade (default: 0.6)
    """

    def initialize(self):
        self.set_start_date(2019, 1, 1)
        self.set_end_date(2024, 1, 1)
        self.set_cash(100_000)

        self._spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # Model parameters
        self._context_length = self.get_parameter('context_length', 64)
        self._prediction_length = self.get_parameter('prediction_length', 1)
        self._num_samples = self.get_parameter('num_samples', 100)
        self._confidence_threshold = self.get_parameter('confidence_threshold', 0.6)

        # Tokenizer parameters (simplified quantization)
        self._num_tokens = self.get_parameter('num_tokens', 32)
        self._center = 0.0
        self._scale = 0.02  # For returns normalization

        # Signal smoothing
        self._smooth_window = self.get_parameter('smooth_window', 5)
        self._recent_signals = deque(maxlen=self._smooth_window)

        # Data collection
        self._price_window = deque(maxlen=self._context_length * 2)
        self._return_window = deque(maxlen=self._context_length * 2)

        # ROC for return calculation
        roc = self.roc(self._spy, 1, Resolution.DAILY)
        roc.updated += self._on_roc_updated

        # Warm up with historical data
        history = self.history[TradeBar](
            self._spy, timedelta(days=self._context_length * 2), Resolution.DAILY
        )
        for bar in history:
            roc.update(bar.end_time, bar.close)
            self._price_window.append(bar.close)

        # Transformer-like attention weights (simplified)
        # In reality, these would be learned during pretraining
        self._attention_scale = 1.0 / np.sqrt(self._context_length)

        # Predictions tracking
        self._predictions = deque(maxlen=100)
        self._forecast_samples = []

        # Schedule trading
        self.schedule.on(
            self.date_rules.every_day(self._spy),
            self.time_rules.after_market_open(self._spy, 30),
            self._trade
        )

        self.log(f"Chronos initialized: context={self._context_length}, confidence={self._confidence_threshold}")

    def _on_roc_updated(self, indicator, indicator_data_point):
        """Collect daily returns."""
        if not indicator.is_ready:
            return
        self._return_window.append(indicator_data_point.value / 100)

    def _quantize(self, values):
        """
        Quantize continuous values to discrete tokens.

        Chronos uses learned quantization. Here we use a simplified
        uniform quantization scheme.
        """
        normalized = (np.array(values) - self._center) / self._scale
        tokens = np.clip(
            np.floor(normalized + self._num_tokens / 2),
            0, self._num_tokens - 1
        ).astype(int)
        return tokens

    def _dequantize(self, tokens):
        """
        Dequantize tokens back to continuous values.
        """
        return (tokens - self._num_tokens / 2) * self._scale + self._center

    def _attention(self, query, keys):
        """
        Simplified attention mechanism.

        In Chronos, this would be a full transformer attention.
        """
        # Dot-product attention
        scores = np.dot(keys, query) * self._attention_scale
        weights = np.exp(scores - np.max(scores))
        weights = weights / np.sum(weights)
        return weights

    def _transformer_forward(self, context):
        """
        Simplified transformer forward pass.

        Demonstrates the concept of using attention for time series.
        Real Chronos uses T5 encoder-decoder architecture.
        """
        if len(context) < self._context_length:
            return 0.0, 0.5

        # Get recent context
        recent = np.array(context[-self._context_length:])

        # Quantize to tokens
        tokens = self._quantize(recent)

        # Embed tokens (simplified: use token values directly)
        embeddings = tokens / self._num_tokens - 0.5

        # Self-attention (simplified)
        # Query: last token embedding
        query = embeddings[-1]
        # Keys: all token embeddings
        keys = embeddings

        attention_weights = self._attention(query, keys)

        # Weighted sum of embeddings
        context_vector = np.sum(attention_weights[:, np.newaxis] * keys[:, np.newaxis])

        # Predict next token (simplified)
        # In reality, this would be a language model head
        predicted_token_offset = np.tanh(context_vector * 2) * 100
        predicted_token = tokens[-1] + predicted_token_offset

        # Dequantize prediction
        predicted_value = self._dequantize(predicted_token)

        return predicted_value, np.std(attention_weights)

    def _forecast_with_uncertainty(self, context, num_samples=100):
        """
        Generate forecast samples with uncertainty quantification.

        Chronos provides probabilistic forecasts via sampling.
        """
        samples = []
        for _ in range(num_samples):
            # Add noise for Monte Carlo sampling
            noisy_context = np.array(context) + np.random.normal(0, 0.001, len(context))
            prediction, _ = self._transformer_forward(noisy_context)
            samples.append(prediction)

        samples = np.array(samples)
        median = np.median(samples)
        q10 = np.percentile(samples, 10)
        q90 = np.percentile(samples, 90)

        return median, q10, q90

    def _trade(self):
        """
        Make forecast and execute trade.
        """
        if len(self._return_window) < self._context_length:
            return

        # Update normalization statistics
        returns = np.array(list(self._return_window))
        self._center = np.mean(returns[-self._context_length:])
        self._scale = max(np.std(returns[-self._context_length:]), 0.001)

        # Get forecast with uncertainty
        context = list(self._return_window)
        median, q10, q90 = self._forecast_with_uncertainty(context, self._num_samples)

        # Calculate confidence based on uncertainty
        uncertainty = q90 - q10
        confidence = 1 / (1 + uncertainty * 50)

        # Direction confidence
        prob_up = np.mean([s > 0 for s in [median]])
        direction_confidence = abs(prob_up - 0.5) * 2

        # Signal smoothing: average recent predictions
        self._recent_signals.append(median)
        smooth_median = np.mean(list(self._recent_signals))

        # Combined confidence
        combined_confidence = confidence * direction_confidence

        # Plot
        self.plot('Chronos', 'MedianForecast', median)
        self.plot('Chronos', 'Confidence', combined_confidence)
        self.plot('Chronos', 'Uncertainty', uncertainty)

        # Track predictions
        actual_return = self._return_window[-1] if self._return_window else 0
        self._predictions.append({
            'predicted': median,
            'actual': actual_return,
            'confidence': combined_confidence
        })

        # Trading logic: use smoothed signal for direction
        if combined_confidence > self._confidence_threshold:
            if smooth_median > 0:
                self.set_holdings(self._spy, 1.0)
                self.log(f"Chronos: UP forecast={smooth_median:.4f}, confidence={combined_confidence:.2%}")
            else:
                self.set_holdings(self._spy, 0.0)
                self.log(f"Chronos: DOWN forecast={smooth_median:.4f}, confidence={combined_confidence:.2%}")

    def on_end_of_algorithm(self):
        final_value = self.portfolio.total_portfolio_value
        returns = (final_value - 100000) / 100000

        # Calculate forecast accuracy
        correct = 0
        total = 0
        predictions_list = list(self._predictions)
        for i in range(len(predictions_list) - 1):
            pred = predictions_list[i]['predicted']
            next_actual = predictions_list[i + 1]['actual']
            predicted_up = pred > 0
            actual_up = next_actual > 0
            if predicted_up == actual_up:
                correct += 1
            total += 1

        accuracy = correct / total if total > 0 else 0

        self.log(f"Chronos Foundation: Final=${final_value:,.0f}, Return={returns:.2%}")
        self.log(f"Direction Accuracy: {accuracy:.2%}, Samples: {total}")
