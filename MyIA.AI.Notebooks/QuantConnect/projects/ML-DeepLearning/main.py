# region imports
from AlgorithmImports import *
# endregion

import torch
import torch.nn as nn
import numpy as np


class SimpleLSTM(nn.Module):
    """LSTM network for time-series return prediction.

    Architecture:
    - Input: sequence of normalized returns (seq_length, 1)
    - Hidden: 1 LSTM layer with 32 units
    - Output: predicted next return (1,)
    """

    def __init__(self, input_size=1, hidden_size=32, num_layers=1):
        super(SimpleLSTM, self).__init__()
        self.lstm = nn.LSTM(
            input_size=input_size,
            hidden_size=hidden_size,
            num_layers=num_layers,
            batch_first=True,
        )
        self.fc = nn.Linear(hidden_size, 1)

    def forward(self, x):
        # x shape: (batch, seq_length, input_size)
        lstm_out, _ = self.lstm(x)
        last_output = lstm_out[:, -1, :]
        return self.fc(last_output)


class MLDeepLearningAlgorithm(QCAlgorithm):
    """
    Deep Learning Strategy with LSTM models.

    Strategy:
    - Use LSTM (Long Short-Term Memory) networks for time series prediction
    - Sequence modeling: predict next returns from past price sequences
    - Features: normalized returns as input sequences
    - Architecture: LSTM layer + Dense output
    - Walk-forward training with periodic retraining
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.SetEndDate(2024, 12, 31)
        self.SetCash(100000)
        self.SetBrokerageModel(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # Assets
        self.tickers = ["SPY", "QQQ", "IWM"]
        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.DAILY).Symbol

        # Deep learning parameters
        self.sequence_length = 20  # Lookback window
        self.epochs = 20
        self.learning_rate = 0.01
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
        self.norm_params = {}  # Store mean/std per ticker

    def PrepareSequences(self, prices, sequence_length=20):
        """Prepare sequences for LSTM training."""
        returns = prices.pct_change().fillna(0)

        # Normalize
        mean = returns.mean()
        std = returns.std()
        if std < 1e-8:
            std = 1.0
        normalized = (returns - mean) / std

        # Create sequences
        X, y = [], []
        for i in range(sequence_length, len(normalized)):
            X.append(normalized.iloc[i - sequence_length:i].values)
            y.append(normalized.iloc[i])

        return np.array(X), np.array(y), mean, std

    def TrainLSTM(self, X_train, y_train, epochs=20):
        """Train an actual LSTM model on the given sequences."""
        device = torch.device('cpu')

        model = SimpleLSTM(
            input_size=1,
            hidden_size=32,
            num_layers=1,
        ).to(device)

        # Convert to tensors: (batch, seq, features)
        X_tensor = torch.FloatTensor(X_train).unsqueeze(-1).to(device)
        y_tensor = torch.FloatTensor(y_train).unsqueeze(-1).to(device)

        criterion = nn.MSELoss()
        optimizer = torch.optim.Adam(model.parameters(), lr=self.learning_rate)

        model.train()
        for epoch in range(epochs):
            optimizer.zero_grad()
            output = model(X_tensor)
            loss = criterion(output, y_tensor)
            loss.backward()
            optimizer.step()

        model.eval()
        return model

    def TrainModel(self):
        """Train LSTM models for each asset."""
        self.Debug("Training LSTM models...")

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], 252, Resolution.DAILY)

                if history.empty or len(history) < 60:
                    continue

                closes = history['close']

                # Prepare sequences
                X, y, mean, std = self.PrepareSequences(closes, self.sequence_length)

                if len(X) < 30:
                    continue

                # Train actual LSTM
                model = self.TrainLSTM(X, y, epochs=self.epochs)
                self.models[ticker] = model
                self.norm_params[ticker] = {'mean': mean, 'std': std}

            except Exception as e:
                self.Debug(f"Error training {ticker}: {e}")
                continue

        self.Debug(f"LSTM models trained. {len(self.models)} models ready.")

    def Predict(self, ticker, history):
        """Make prediction using trained LSTM model."""
        if ticker not in self.models:
            return 0

        model = self.models[ticker]
        params = self.norm_params[ticker]

        closes = history['close']
        returns = closes.pct_change().fillna(0)

        # Normalize
        normalized = (returns - params['mean']) / params['std']

        # Get last sequence
        if len(normalized) < self.sequence_length:
            return 0

        sequence = normalized.iloc[-self.sequence_length:].values
        X = torch.FloatTensor(sequence).unsqueeze(0).unsqueeze(-1)  # (1, seq, 1)

        # Predict
        with torch.no_grad():
            prediction = model(X).item()

        # Denormalize
        pred_return = prediction * params['std'] + params['mean']

        return pred_return

    def Rebalance(self):
        """Rebalance based on LSTM predictions."""
        if not self.models:
            return

        predictions = {}

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], 60, Resolution.DAILY)

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
