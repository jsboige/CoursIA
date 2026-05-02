# region imports
from AlgorithmImports import *
# endregion

class MLRandomForestAlgorithm(QCAlgorithm):
    """
    Random Forest Classification Strategy - v3.

    v3 (from v2 Sharpe 0.187, only 75 trades due to SMA200 filter + high threshold):
    - Removed SMA200 regime filter (caused excessive cash drag)
    - Lowered threshold to 0.54 (from 0.58) to increase trade frequency
    - Bi-weekly rebalance (compromise between weekly and monthly)
    - Kept: 2015 start, depth 5, min_samples 10, lookback 120, 12 features

    Performance history:
    - v1 (2020+, weekly): Sharpe 0.45, CAGR 12%, MaxDD 20.4%
    - v2 (2015+, monthly+SMA200): Sharpe 0.19, CAGR 5.6%, MaxDD 19.2% (too conservative)
    - v3 (2015+, biweekly, no filter): Sharpe 0.68, CAGR 20.1%, MaxDD 36.4%
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.SetCash(100000)

        # Universe: Liquid large-cap stocks
        self.tickers = [
            "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA",
            "META", "TSLA", "JPM", "V", "WMT"
        ]

        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.DAILY).Symbol

        # Random Forest parameters
        self.lookback = 120
        self.n_estimators = 100
        self.max_depth = 5
        self.min_samples_split = 10

        # Bi-weekly rebalance (1st and 3rd Monday)
        self.week_counter = 0
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.on_monday)

        # Monthly training
        self.Schedule.On(self.DateRules.MonthStart("SPY"),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.train_model)

        self.model = None
        self.scaler = None
        self.feature_names = None

        self.SetWarmUp(60, Resolution.Daily)

    def on_monday(self):
        """Bi-weekly rebalance."""
        self.week_counter += 1
        if self.week_counter % 2 == 0:
            self.rebalance()

    def calculate_features(self, history, ticker):
        """Calculate technical features for Random Forest."""
        closes = history['close']
        volumes = history['volume']
        highs = history['high']
        lows = history['low']

        returns = closes.pct_change()

        sma_5 = closes.rolling(5).mean()
        sma_20 = closes.rolling(20).mean()
        sma_50 = closes.rolling(50).mean()

        # RSI
        delta = closes.diff()
        gain = (delta.where(delta > 0, 0)).rolling(14).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(14).mean()
        rs = gain / loss
        rsi = 100 - (100 / (1 + rs))

        # MACD
        ema_12 = closes.ewm(span=12).mean()
        ema_26 = closes.ewm(span=26).mean()
        macd = ema_12 - ema_26
        macd_signal = macd.ewm(span=9).mean()

        # Bollinger Bands
        bb_middle = closes.rolling(20).mean()
        bb_std = closes.rolling(20).std()
        bb_position = (closes - bb_middle) / (2 * bb_std)

        # Momentum
        momentum_5 = closes / closes.shift(5) - 1
        momentum_10 = closes / closes.shift(10) - 1
        momentum_20 = closes / closes.shift(20) - 1

        # Volatility
        volatility_20 = returns.rolling(20).std()

        # Volume
        volume_sma = volumes.rolling(20).mean()
        volume_ratio = volumes / volume_sma

        # Price ratios
        price_to_sma20 = closes / sma_20
        price_to_sma50 = closes / sma_50

        features = pd.DataFrame({
            'rsi': rsi,
            'bb_position': bb_position,
            'macd_hist': macd - macd_signal,
            'mom_5': momentum_5,
            'mom_10': momentum_10,
            'mom_20': momentum_20,
            'vol_20': volatility_20,
            'volume_ratio': volume_ratio,
            'price_sma20': price_to_sma20,
            'price_sma50': price_to_sma50,
            'sma_ratio_5_20': sma_5 / sma_20,
            'sma_ratio_20_50': sma_20 / sma_50,
        })

        return features.fillna(0)

    def train_model(self):
        """Train Random Forest classifier."""
        if self.IsWarmingUp:
            return

        from sklearn.ensemble import RandomForestClassifier
        from sklearn.preprocessing import MinMaxScaler

        all_features = []
        all_targets = []

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], self.lookback, Resolution.Daily)
                if history.empty or len(history) < 60:
                    continue

                features = self.calculate_features(history, ticker)
                closes = history['close']

                future_return = closes.pct_change().shift(-1)
                target = (future_return > 0).astype(int)

                features['target'] = target
                features = features.dropna()

                if len(features) > 20:
                    all_features.append(features.drop('target', axis=1))
                    all_targets.append(features['target'])

            except Exception as e:
                self.Debug(f"Error {ticker}: {e}")
                continue

        if not all_features:
            return

        X = pd.concat(all_features, ignore_index=True)
        y = pd.concat(all_targets, ignore_index=True)
        self.feature_names = X.columns.tolist()

        self.scaler = MinMaxScaler()
        X_scaled = self.scaler.fit_transform(X)

        self.model = RandomForestClassifier(
            n_estimators=self.n_estimators,
            max_depth=self.max_depth,
            min_samples_split=self.min_samples_split,
            random_state=42,
            n_jobs=-1
        )
        self.model.fit(X_scaled, y)

    def predict(self, ticker, history):
        """Predict probability of positive return."""
        if self.model is None:
            return 0.5

        features = self.calculate_features(history, ticker)
        if len(features) == 0:
            return 0.5

        latest_features = features.iloc[-1:].values
        if self.scaler is not None:
            latest_features = self.scaler.transform(latest_features)

        proba = self.model.predict_proba(latest_features)[0]
        return proba[1]

    def rebalance(self):
        """Rebalance based on RF predictions."""
        if self.IsWarmingUp or self.model is None:
            return

        predictions = {}
        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], self.lookback, Resolution.Daily)
                if history.empty:
                    continue
                prob = self.predict(ticker, history)
                predictions[ticker] = prob
            except Exception as e:
                continue

        if not predictions:
            return

        sorted_preds = sorted(predictions.items(), key=lambda x: x[1], reverse=True)

        max_positions = 5
        threshold = 0.54
        selected = [(t, p) for t, p in sorted_preds if p > threshold][:max_positions]

        target_symbols = {self.symbols[t] for t, _ in selected}

        # Liquidate non-target positions
        for holding in self.Portfolio.Values:
            if holding.Invested and holding.Symbol not in target_symbols:
                self.Liquidate(holding.Symbol)

        # Set target positions
        if selected:
            weight = 0.90 / len(selected)
            for ticker, prob in selected:
                self.SetHoldings(self.symbols[ticker], weight)
