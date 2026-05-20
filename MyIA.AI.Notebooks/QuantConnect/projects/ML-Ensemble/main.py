# region imports
from AlgorithmImports import *
# endregion

class MLEnsembleAlgorithm(QCAlgorithm):
    """
    ML Ensemble Strategy combining multiple weak signals.

    Strategy:
    - Train multiple diverse models (Ridge, RandomForest, LightGBM)
    - Combine predictions using weighted averaging
    - Features: Technical indicators + fundamental ratios
    - Position sizing based on ensemble confidence
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.SetCash(100000)

        # Universe: Top 30 liquid stocks
        self.tickers = [
            "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA", "META", "TSLA",
            "JPM", "V", "WMT", "DIS", "NFLX", "PYPL", "ADBE", "CRM",
            "INTC", "AMD", "GS", "MS", "BA", "CSCO", "ORCL", "AVGO",
            "TXN", "QCOM", "IBM", "AMAT", "NOW", "SHOP", "SQ"
        ]

        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.DAILY).Symbol

        # Ensemble parameters
        self.lookback = 90
        self.rebalance_freq = 5
        self.min_confidence = 0.6
        self.max_positions = 12
        self.position_size = 0.08

        # Rebalance schedule
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.Rebalance)

        # Train models bi-weekly
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.TrainModels)

        self.models = {}
        self.scaler = None
        self.weights = {}

    def TrainModels(self):
        """Train ensemble of models."""
        self.Debug("Training ensemble models...")

        history = self.History(list(self.symbols.values()), self.lookback, Resolution.Daily)

        if history.empty or len(history) < self.lookback:
            return

        X, y = self.PrepareFeatures(history)

        if X is None or len(X) < 50:
            return

        from sklearn.preprocessing import StandardScaler
        from sklearn.linear_model import Ridge
        from sklearn.ensemble import RandomForestClassifier, GradientBoostingClassifier

        self.scaler = StandardScaler()
        X_scaled = self.scaler.fit_transform(X)

        # Model 1: Ridge Regression
        ridge = Ridge(alpha=1.0)
        ridge.fit(X_scaled, y)

        # Model 2: RandomForest
        rf = RandomForestClassifier(n_estimators=50, max_depth=5, random_state=42)
        rf.fit(X_scaled, (y > 0).astype(int))

        # Model 3: Gradient Boosting
        gb = GradientBoostingClassifier(n_estimators=50, max_depth=3, random_state=42)
        gb.fit(X_scaled, (y > 0).astype(int))

        self.models = {
            'ridge': ridge,
            'random_forest': rf,
            'gradient_boosting': gb
        }

        # Equal weights initially
        self.weights = {name: 1.0/len(self.models) for name in self.models}

        self.Debug("Ensemble models trained.")

    def PrepareFeatures(self, history):
        """Prepare features for ensemble."""
        closes = history['close'].unstack(level=0)
        volumes = history['volume'].unstack(level=0)

        symbol_to_ticker = {str(v): k for k, v in self.symbols.items()}
        closes.columns = [symbol_to_ticker.get(str(c), str(c)) for c in closes.columns]
        volumes.columns = [symbol_to_ticker.get(str(c), str(c)) for c in volumes.columns]

        features_list = []
        targets_list = []

        for ticker in self.tickers:
            if ticker not in closes.columns:
                continue

            close = closes[ticker].dropna()
            volume = volumes[ticker].dropna()

            if len(close) < 30:
                continue

            # Technical features
            rsi = self.CalculateRSI(close)
            ema20 = close.ewm(span=20).mean()
            ema50 = close.ewm(span=50).mean()

            returns = close.pct_change()
            vol5 = returns.rolling(5).std()
            vol20 = returns.rolling(20).std()

            volume_ma = volume.rolling(20).mean()

            df = pd.DataFrame({
                'RSI': rsi,
                'EMA_Ratio': ema20 / ema50,
                'Returns_1': returns.shift(1),
                'Returns_5': returns.shift(5),
                'Returns_20': returns.shift(20),
                'Vol_5': vol5,
                'Vol_20': vol20,
                'Volume_Ratio': volume / volume_ma,
                'Momentum_5': close / close.shift(5) - 1,
                'Momentum_20': close / close.shift(20) - 1,
                'Dist_MA20': (close - ema20) / close,
                'Dist_MA50': (close - ema50) / close,
            })

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
        delta = prices.diff()
        gain = (delta.where(delta > 0, 0)).rolling(window=period).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(window=period).mean()
        rs = gain / loss
        return 100 - (100 / (1 + rs))

    def Rebalance(self):
        """Rebalance using ensemble predictions."""
        if not self.models or self.scaler is None:
            return

        history = self.History(list(self.symbols.values()), 60, Resolution.Daily)

        if history.empty:
            return

        predictions = {}
        confidences = {}

        for ticker in self.tickers:
            try:
                features = self.GetFeatures(history, ticker)
                if features is None:
                    continue

                X = self.scaler.transform([features])

                # Get predictions from all models
                preds = []
                for name, model in self.models.items():
                    if name == 'ridge':
                        pred = model.predict(X)[0]
                        preds.append(pred)
                    else:
                        prob = model.predict_proba(X)[0][1]
                        preds.append(prob)

                # Weighted ensemble prediction
                ensemble_pred = sum(p * self.weights[name] for name, p in zip(self.models.keys(), preds))

                # Confidence = agreement between models
                confidence = 1 - np.std(preds)

                predictions[ticker] = ensemble_pred
                confidences[ticker] = confidence

            except Exception:
                continue

        # Filter by confidence
        filtered_preds = {t: p for t, p in predictions.items()
                         if confidences.get(t, 0) > self.min_confidence}

        if not filtered_preds:
            return

        # Sort by prediction
        sorted_preds = sorted(filtered_preds.items(), key=lambda x: x[1], reverse=True)

        # Liquidate
        self.Liquidate()

        # Enter long positions
        count = 0
        for ticker, pred in sorted_preds:
            if pred > 0.005 and count < self.max_positions:
                self.SetHoldings(self.symbols[ticker], self.position_size)
                count += 1

        self.Debug(f"Positions: {count}, Best pred: {sorted_preds[0][1]:.3f}" if sorted_preds else "No positions")

    def GetFeatures(self, history, ticker):
        """Extract features for single stock."""
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
            returns.iloc[-20] if len(returns) >= 20 else 0,
            returns.rolling(5).std().iloc[-1],
            returns.rolling(20).std().iloc[-1],
            (volume.iloc[-1] / volume.rolling(20).mean().iloc[-1]),
            (close.iloc[-1] / close.iloc[-5] - 1) if len(close) >= 5 else 0,
            (close.iloc[-1] / close.iloc[-20] - 1) if len(close) >= 20 else 0,
            ((close.iloc[-1] - ema20.iloc[-1]) / close.iloc[-1]),
            ((close.iloc[-1] - ema50.iloc[-1]) / close.iloc[-1]),
        ]

        return features
