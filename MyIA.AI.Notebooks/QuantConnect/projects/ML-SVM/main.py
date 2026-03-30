# region imports
from AlgorithmImports import *
# endregion

class MLSVMAlgorithm(QCAlgorithm):
    """
    SVM Classification Strategy - v3.

    v3 (from v2 Sharpe -0.02, too much cash from regime filter):
    - Removed SMA200 regime filter (was causing excessive cash drag)
    - Bi-weekly rebalance (better match with prediction horizon)
    - Lower threshold (0.55) to increase time in market
    - Kept: equity-only ETFs, linear kernel, 120d lookback, 8 features

    Performance history:
    - v1 (2020+, mixed ETFs, RBF, weekly): Sharpe -0.58, 28% win rate
    - v2 (2015+, equity only, linear, regime filter): Sharpe -0.02
    - v3 (2015+, no filter, biweekly): Sharpe 0.147

    Structural ceiling: SVM for daily/weekly ETF direction prediction
    has limited signal-to-noise ratio. Alpha remains negative.
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.SetCash(100000)

        # Equity-only ETFs
        self.tickers = ["SPY", "QQQ", "IWM", "DIA", "XLK", "XLF", "XLV", "XLY"]

        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.DAILY).Symbol

        # SVM parameters
        self.lookback = 120
        self.C = 0.5
        self.kernel = 'linear'

        # Monthly training
        self.Schedule.On(self.DateRules.MonthStart("SPY"),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.train_model)

        # Bi-weekly rebalance
        self.week_counter = 0
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.on_monday)

        self.model = None
        self.scaler = None

        self.SetWarmUp(60, Resolution.Daily)

    def on_monday(self):
        self.week_counter += 1
        if self.week_counter % 2 == 0:
            self.rebalance()

    def calculate_features(self, history, ticker):
        closes = history['close']
        returns = closes.pct_change()

        sma_20 = closes.rolling(20).mean()
        sma_50 = closes.rolling(50).mean()

        delta = closes.diff()
        gain = (delta.where(delta > 0, 0)).rolling(14).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(14).mean()
        rs = gain / loss
        rsi = (100 - (100 / (1 + rs))) / 100

        ema_12 = closes.ewm(span=12).mean()
        ema_26 = closes.ewm(span=26).mean()
        macd = ema_12 - ema_26
        macd_signal = macd.ewm(span=9).mean()

        bb_middle = closes.rolling(20).mean()
        bb_std = closes.rolling(20).std()
        bb_position = (closes - bb_middle) / (2 * bb_std)
        bb_position = bb_position.clip(-2, 2) / 2

        momentum_10 = closes / closes.shift(10) - 1
        momentum_20 = closes / closes.shift(20) - 1
        volatility_20 = returns.rolling(20).std()
        price_to_sma20 = closes / sma_20 - 1
        price_to_sma50 = closes / sma_50 - 1

        features = pd.DataFrame({
            'rsi': rsi,
            'bb_position': bb_position,
            'macd_hist': (macd - macd_signal) / closes,
            'mom_10': momentum_10,
            'mom_20': momentum_20,
            'volatility': volatility_20,
            'price_sma20': price_to_sma20,
            'price_sma50': price_to_sma50,
        })

        return features.fillna(0)

    def train_model(self):
        if self.IsWarmingUp:
            return

        from sklearn.svm import SVC
        from sklearn.preprocessing import StandardScaler

        all_features = []
        all_targets = []

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], self.lookback, Resolution.Daily)
                if history.empty or len(history) < 60:
                    continue

                features = self.calculate_features(history, ticker)
                closes = history['close']

                # Target: positive 10-day forward return
                future_return = closes.pct_change(10).shift(-10)
                target = (future_return > 0).astype(int)

                features['target'] = target
                features = features.dropna()

                if len(features) > 20:
                    all_features.append(features.drop('target', axis=1))
                    all_targets.append(features['target'])

            except Exception as e:
                continue

        if not all_features:
            return

        X = pd.concat(all_features, ignore_index=True)
        y = pd.concat(all_targets, ignore_index=True)

        self.scaler = StandardScaler()
        X_scaled = self.scaler.fit_transform(X)

        self.model = SVC(
            C=self.C,
            kernel=self.kernel,
            probability=True,
            random_state=42
        )
        self.model.fit(X_scaled, y)

    def predict(self, ticker, history):
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

        max_positions = 4
        threshold = 0.55
        selected = [(t, p) for t, p in sorted_preds if p > threshold][:max_positions]

        target_symbols = {self.symbols[t] for t, _ in selected}

        for holding in self.Portfolio.Values:
            if holding.Invested and holding.Symbol not in target_symbols:
                self.Liquidate(holding.Symbol)

        if selected:
            weight = 0.90 / len(selected)
            for ticker, prob in selected:
                self.SetHoldings(self.symbols[ticker], weight)
