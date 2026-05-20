# region imports
from AlgorithmImports import *
# endregion

class MLRegressionAlgorithm(QCAlgorithm):
    """
    ML Regression Strategy for Price Prediction.

    Strategy:
    - Use Ridge Regression to predict next-day returns
    - Features: RSI, EMA ratios, volume, volatility
    - Long when predicted return > threshold
    - Position sizing based on prediction confidence
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.SetCash(100000)

        # Universe: Top 20 liquid stocks
        self.tickers = [
            "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA",
            "META", "TSLA", "JPM", "V", "WMT",
            "DIS", "NFLX", "PYPL", "ADBE", "CRM",
            "INTC", "AMD", "GS", "MS", "BA"
        ]

        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.Daily).Symbol

        # Model parameters
        self.lookback = 60  # Training window
        self.features = 15  # Number of features
        self.prediction_threshold = 0.005  # 0.5% expected return
        self.max_positions = 10
        self.position_size = 0.1  # 10% per position

        # Rebalance schedule
        self.Schedule.On(self.DateRules.EveryDay("SPY"),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.Rebalance)

        # Train model schedule (weekly)
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.TrainModel)

        self.model = None
        self.scaler = None

    def TrainModel(self):
        """Train Ridge Regression model."""
        self.Debug("Training model...")

        # Get historical data
        history = self.History(list(self.symbols.values()), self.lookback, Resolution.Daily)

        if history.empty or len(history) < self.lookback:
            return

        # Prepare features and targets
        X, y = self.PrepareFeatures(history)

        if X is None or len(X) < 10:
            return

        # Train Ridge Regression
        from sklearn.linear_model import Ridge
        from sklearn.preprocessing import StandardScaler

        self.scaler = StandardScaler()
        X_scaled = self.scaler.fit_transform(X)

        self.model = Ridge(alpha=1.0)
        self.model.fit(X_scaled, y)

        self.Debug(f"Model trained. R²: {self.model.score(X_scaled, y):.3f}")

    def PrepareFeatures(self, history):
        """Prepare features for ML model."""
        closes = history['close'].unstack(level=0)
        volumes = history['volume'].unstack(level=0)

        symbol_to_ticker = {str(v): k for k, v in self.symbols.items()}

        features_list = []
        targets_list = []

        for ticker in self.tickers:
            if str(self.symbols[ticker]) not in closes.columns:
                continue

            close = closes[str(self.symbols[ticker])].dropna()
            volume = volumes[str(self.symbols[ticker])].dropna()

            if len(close) < 20:
                continue

            # Technical indicators
            rsi = self.CalculateRSI(close)
            ema20 = close.ewm(span=20).mean()
            ema50 = close.ewm(span=50).mean()
            ema_ratio = ema20 / ema50

            # Returns
            returns = close.pct_change()
            vol5 = returns.rolling(5).std()
            vol20 = returns.rolling(20).std()

            # Volume features
            volume_ma = volume.rolling(20).mean()
            volume_ratio = volume / volume_ma

            # Combine features
            df = pd.DataFrame({
                'RSI': rsi,
                'EMA_Ratio': ema_ratio,
                'Returns_1': returns.shift(1),
                'Returns_5': returns.shift(5),
                'Vol_5': vol5,
                'Vol_20': vol20,
                'Volume_Ratio': volume_ratio,
                'Price_Momentum_5': (close / close.shift(5) - 1),
                'Price_Momentum_10': (close / close.shift(10) - 1),
                'Distance_to_MA20': (close - ema20) / close,
                'Distance_to_MA50': (close - ema50) / close,
            })

            # Target: next day return
            df['Target'] = returns.shift(-1)

            df = df.dropna()

            if len(df) > 10:
                features_list.append(df.drop('Target', axis=1))
                targets_list.append(df['Target'])

        if not features_list:
            return None, None

        X = pd.concat(features_list, ignore_index=True)
        y = pd.concat(targets_list, ignore_index=True)

        return X.fillna(0), y.fillna(0)

    def CalculateRSI(self, prices, period=14):
        """Calculate RSI."""
        delta = prices.diff()
        gain = (delta.where(delta > 0, 0)).rolling(window=period).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(window=period).mean()
        rs = gain / loss
        return 100 - (100 / (1 + rs))

    def Rebalance(self):
        """Rebalance portfolio based on predictions."""
        if self.model is None or self.scaler is None:
            return

        # Get recent data for predictions
        history = self.History(list(self.symbols.values()), 60, Resolution.Daily)

        if history.empty:
            return

        predictions = {}
        for ticker in self.tickers:
            try:
                features = self.GetPredictionFeatures(history, ticker)
                if features is not None:
                    X = self.scaler.transform([features])
                    pred = self.model.predict(X)[0]
                    predictions[ticker] = pred
            except:
                continue

        # Sort by predicted return
        sorted_preds = sorted(predictions.items(), key=lambda x: x[1], reverse=True)

        # Liquidate existing positions
        self.Liquidate()

        # Enter long positions for top predictions
        count = 0
        for ticker, pred in sorted_preds:
            if pred > self.prediction_threshold and count < self.max_positions:
                self.SetHoldings(self.symbols[ticker], self.position_size)
                count += 1

        self.Debug(f"Positions: {count}, Best prediction: {sorted_preds[0][1]:.3f}" if sorted_preds else "No positions")

    def GetPredictionFeatures(self, history, ticker):
        """Extract features for single stock prediction."""
        closes = history['close'].unstack(level=0)
        volumes = history['volume'].unstack(level=0)

        sym_str = str(self.symbols[ticker])
        if sym_str not in closes.columns:
            return None

        close = closes[sym_str].dropna()
        volume = volumes[sym_str].dropna()

        if len(close) < 20:
            return None

        rsi = self.CalculateRSI(close)
        ema20 = close.ewm(span=20).mean()
        ema50 = close.ewm(span=50).mean()
        returns = close.pct_change()

        features = [
            rsi.iloc[-1],
            (ema20.iloc[-1] / ema50.iloc[-1]),
            returns.iloc[-1],
            returns.iloc[-5] if len(returns) >= 5 else 0,
            returns.rolling(5).std().iloc[-1],
            returns.rolling(20).std().iloc[-1],
            (volume.iloc[-1] / volume.rolling(20).mean().iloc[-1]),
            (close.iloc[-1] / close.iloc[-5] - 1) if len(close) >= 5 else 0,
            (close.iloc[-1] / close.iloc[-10] - 1) if len(close) >= 10 else 0,
            ((close.iloc[-1] - ema20.iloc[-1]) / close.iloc[-1]),
            ((close.iloc[-1] - ema50.iloc[-1]) / close.iloc[-1]),
        ]

        return features
