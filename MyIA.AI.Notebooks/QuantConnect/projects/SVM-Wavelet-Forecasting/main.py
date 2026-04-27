# region imports
from AlgorithmImports import *

from sklearn.svm import SVR
import pywt
import numpy as np
import pandas as pd
# endregion


class SVMWaveletForecasting(QCAlgorithm):
    """
    FX Forecasting using SVM with Wavelet Decomposition.

    This strategy demonstrates how to use wavelet transforms to decompose
    price series into different frequency components, then apply SVM
    regression to predict each component separately.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 05

    How it works:
    1. Decompose EUR/USD returns using Discrete Wavelet Transform (DWT)
    2. Train separate SVR models on each wavelet component
    3. Predict each component and reconstruct the signal
    4. Trade based on the predicted direction

    Wavelet decomposition (level 3, Daubechies 4):
    - cA3: Approximation (low frequency trend)
    - cD3: Detail level 3 (medium-low frequency)
    - cD2: Detail level 2 (medium-high frequency)
    - cD1: Detail level 1 (high frequency noise)

    Parameters:
    - lookback_days: Number of days for training window (default: 252)
    - wavelet: Wavelet family (default: 'db4')
    - decomposition_level: DWT decomposition level (default: 3)
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_end_date(2024, 1, 1)
        self.set_cash(100_000)

        # FX pair for prediction
        self._eurusd = self.add_forex("EURUSD", Resolution.DAILY, Market.OANDA).symbol

        # Model parameters
        self._lookback_days = self.get_parameter('lookback_days', 252)
        self._wavelet = self.get_parameter('wavelet', 'db4')
        self._decomp_level = self.get_parameter('decomposition_level', 3)

        # Data storage
        self._price_history = []
        self._models = {}  # SVR models for each wavelet component

        # Schedule weekly training and trading
        schedule_symbol = Symbol.create("SPY", SecurityType.EQUITY, Market.USA)
        date_rule = self.date_rules.week_start(schedule_symbol)

        # Train on Sunday evening
        self.train(date_rule, self.time_rules.at(20, 0), self._train_models)

        # Trade on Monday after FX market open
        self.schedule.on(
            date_rule,
            self.time_rules.at(9, 30),
            self._trade
        )

        # Warm up with historical data
        history = self.history[QuoteBar](
            self._eurusd, timedelta(days=self._lookback_days + 30), Resolution.DAILY
        )
        for bar in history:
            self._price_history.append(bar.close)

        self.log(f"SVMWaveletForecasting initialized: {self._wavelet} level {self._decomp_level}")

    def _train_models(self):
        """
        Train SVR models on wavelet-decomposed components.

        Process:
        1. Get log returns from price history
        2. Apply DWT to decompose into approximation + details
        3. Train SVR on each component
        4. Store models for prediction
        """
        if len(self._price_history) < self._lookback_days:
            self.log("Not enough data for training")
            return

        try:
            # Get recent prices and compute log returns
            prices = np.array(self._price_history[-self._lookback_days:])
            returns = np.diff(np.log(prices))

            # Pad returns for wavelet decomposition (must be power of 2)
            padded_len = 2 ** int(np.ceil(np.log2(len(returns))))
            if len(returns) < padded_len:
                returns = np.pad(returns, (0, padded_len - len(returns)), mode='edge')

            # Wavelet decomposition
            coeffs = pywt.wavedec(returns, self._wavelet, level=self._decomp_level)
            # coeffs = [cA3, cD3, cD2, cD1] for level 3

            # Train SVR on each component
            self._models = {}
            for i, coeff in enumerate(coeffs):
                # Create features: lagged values
                X, y = self._create_features(coeff)
                if len(X) < 50:
                    continue

                # Train SVR with RBF kernel
                model = SVR(kernel='rbf', C=1.0, gamma='scale')
                model.fit(X, y)
                self._models[i] = model

            self.log(f"Trained {len(self._models)} SVR models on wavelet components")

        except Exception as e:
            self.log(f"Training error: {e}")

    def _create_features(self, series, lag=5):
        """Create lagged features for time series prediction."""
        X, y = [], []
        for i in range(lag, len(series)):
            X.append(series[i-lag:i])
            y.append(series[i])
        return np.array(X), np.array(y)

    def _trade(self):
        """
        Predict next return using wavelet-SVM approach.

        Process:
        1. Get recent returns and decompose with DWT
        2. Predict each component using trained SVR models
        3. Reconstruct signal from predicted components
        4. Trade based on predicted direction
        """
        if not self._models or len(self._price_history) < 50:
            return

        try:
            # Get recent returns
            prices = np.array(self._price_history[-100:])
            returns = np.diff(np.log(prices))

            # Pad for wavelet decomposition
            padded_len = 2 ** int(np.ceil(np.log2(len(returns))))
            if len(returns) < padded_len:
                returns = np.pad(returns, (0, padded_len - len(returns)), mode='edge')

            # Decompose
            coeffs = pywt.wavedec(returns, self._wavelet, level=self._decomp_level)

            # Predict each component
            predicted_coeffs = []
            for i, coeff in enumerate(coeffs):
                if i in self._models:
                    # Use last lag values as features
                    model = self._models[i]
                    lag = 5
                    features = coeff[-lag:].reshape(1, -1)
                    pred = model.predict(features)[0]
                    # Replace last value with prediction
                    predicted_coeff = coeff.copy()
                    predicted_coeff[-1] = pred
                    predicted_coeffs.append(predicted_coeff)
                else:
                    predicted_coeffs.append(coeff)

            # Reconstruct signal
            predicted_returns = pywt.waverec(predicted_coeffs, self._wavelet)

            # Get the predicted next return (last value)
            next_return = predicted_returns[-1]

            # Plot prediction
            self.plot('Prediction', 'Next Return', next_return)

            # Trading logic: go long EUR if predicted positive return
            current_price = self._price_history[-1]
            if next_return > 0.001:  # 0.1% threshold
                self.set_holdings(self._eurusd, 0.5)
            elif next_return < -0.001:
                self.set_holdings(self._eurusd, -0.5)
            else:
                # Close position if uncertain
                self.liquidate(self._eurusd)

        except Exception as e:
            self.log(f"Prediction error: {e}")

    def on_data(self, data):
        """Update price history with new data."""
        if self._eurusd in data:
            bar = data[self._eurusd]
            if bar.close > 0:
                self._price_history.append(bar.close)
                # Keep only recent history
                if len(self._price_history) > self._lookback_days + 100:
                    self._price_history = self._price_history[-self._lookback_days - 50:]

    def on_end_of_algorithm(self):
        final_value = self.portfolio.total_portfolio_value
        returns = (final_value - 100000) / 100000
        self.log(f"SVM Wavelet Forecasting: Final=${final_value:,.0f}, Return={returns:.2%}")
