# region imports
from AlgorithmImports import *
# endregion


class ESGFMLXGBoost(QCAlgorithm):
    """
    ESGF Kit - ML XGBoost Sector Rotation.

    Sector ETF rotation using Gradient Boosting regression with walk-forward
    training. Predicts 20-day forward returns and allocates to sectors with
    the highest predicted returns.

    Architecture:
        - Universe: 9 sector ETFs
        - Features: 20 technical indicators per sector
        - Model: GradientBoostingRegressor (100 trees, depth 4, lr=0.05)
        - Training: 3-year rolling window, bi-weekly retrain
        - Rebalancing: Bi-weekly
        - Risk: SMA200 bear filter, confidence-weighted sizing, max 5 sectors

    Performance (2015-2024 backtest):
        - Target Sharpe: >= 0.78
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.SetEndDate(2024, 12, 31)
        self.SetCash(100000)

        self.tickers = ["XLK", "XLF", "XLV", "XLE", "XLY", "XLP", "XLI", "XLU", "XLRE"]

        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.DAILY).Symbol

        self.spy = self.AddEquity("SPY", Resolution.DAILY).Symbol

        # Model parameters
        self.lookback = 252 * 3       # 3-year training window
        self.n_estimators = 100
        self.max_depth = 4
        self.learning_rate = 0.05
        self.min_samples_leaf = 15
        self.subsample = 0.8
        self.max_positions = 5
        self.allocation_pct = 0.90

        # State
        self.model = None
        self.scaler = None
        self.week_counter = 0

        # SMA200 for regime detection
        self.spy_sma200 = self.SMA(self.spy, 200, Resolution.DAILY)

        # Bi-weekly schedule
        self.Schedule.On(
            self.DateRules.Every(DayOfWeek.MONDAY),
            self.TimeRules.AfterMarketOpen(self.spy, 30),
            self.on_monday,
        )

        self.SetWarmUp(200, Resolution.DAILY)

    def calculate_features(self, history):
        """Calculate 20 technical features for a single asset."""
        closes = history["close"]
        volumes = history["volume"]
        highs = history["high"]
        lows = history["low"]

        returns = closes.pct_change()

        # SMA
        sma_5 = closes.rolling(5).mean()
        sma_10 = closes.rolling(10).mean()
        sma_20 = closes.rolling(20).mean()
        sma_50 = closes.rolling(50).mean()

        # RSI
        delta = closes.diff()
        gain = delta.where(delta > 0, 0).rolling(14).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(14).mean()
        rs = gain / loss
        rsi = 100 - (100 / (1 + rs))

        # Bollinger Bands
        bb_mid = closes.rolling(20).mean()
        bb_std = closes.rolling(20).std()
        bb_pos = (closes - bb_mid) / (2 * bb_std)

        # MACD
        ema12 = closes.ewm(span=12).mean()
        ema26 = closes.ewm(span=26).mean()
        macd = ema12 - ema26
        macd_signal = macd.ewm(span=9).mean()

        # Stochastic
        low_14 = lows.rolling(14).min()
        high_14 = highs.rolling(14).max()
        denom = (high_14 - low_14).replace(0, np.nan)
        stoch_k = 100 * (closes - low_14) / denom

        # ATR
        tr = pd.concat([
            highs - lows,
            (highs - closes.shift()).abs(),
            (lows - closes.shift()).abs(),
        ], axis=1).max(axis=1)
        atr = tr.rolling(14).mean()

        # Momentum
        mom_5 = closes.pct_change(5)
        mom_10 = closes.pct_change(10)
        mom_20 = closes.pct_change(20)
        mom_50 = closes.pct_change(50)

        # Volatility
        vol_5 = returns.rolling(5).std()
        vol_20 = returns.rolling(20).std()

        # Volume
        vol_sma = volumes.rolling(20).mean()
        volume_ratio = volumes / vol_sma

        # Price ratios
        price_sma20 = closes / sma_20
        price_sma50 = closes / sma_50

        # Range position
        low_50 = lows.rolling(50).min()
        high_50 = highs.rolling(50).max()
        range_pos = (closes - low_50) / (high_50 - low_50)

        features = pd.DataFrame({
            "rsi": rsi,
            "bb_position": bb_pos,
            "macd_hist": macd - macd_signal,
            "stoch_k": stoch_k,
            "atr_ratio": atr / closes,
            "mom_5": mom_5,
            "mom_10": mom_10,
            "mom_20": mom_20,
            "mom_50": mom_50,
            "vol_5": vol_5,
            "vol_20": vol_20,
            "volume_ratio": volume_ratio,
            "price_sma20": price_sma20,
            "price_sma50": price_sma50,
            "sma_5_20": sma_5 / sma_20,
            "sma_10_50": sma_10 / sma_50,
            "range_position": range_pos,
            "return_1d": returns,
            "return_5d": closes.pct_change(5),
            "return_20d": closes.pct_change(20),
        })

        return features.fillna(0).replace([np.inf, -np.inf], 0)

    def train_model(self):
        """Train GradientBoosting on pooled sector data."""
        from sklearn.ensemble import GradientBoostingRegressor
        from sklearn.preprocessing import StandardScaler

        all_X, all_y = [], []

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], self.lookback, Resolution.DAILY)
                if history.empty or len(history) < 100:
                    continue

                features = self.calculate_features(history)
                closes = history["close"]

                # Target: 20-day forward return (regression)
                target = closes.pct_change(20).shift(-20)

                features["target"] = target
                features = features.dropna()

                if len(features) > 50:
                    all_X.append(features.drop("target", axis=1))
                    all_y.append(features["target"])
            except Exception:
                continue

        if not all_X:
            return

        X = pd.concat(all_X, ignore_index=True)
        y = pd.concat(all_y, ignore_index=True)

        self.scaler = StandardScaler()
        X_scaled = self.scaler.fit_transform(X)

        self.model = GradientBoostingRegressor(
            n_estimators=self.n_estimators,
            max_depth=self.max_depth,
            learning_rate=self.learning_rate,
            min_samples_leaf=self.min_samples_leaf,
            subsample=self.subsample,
            random_state=42,
        )
        self.model.fit(X_scaled, y)

    def predict_return(self, ticker):
        """Predict 20-day forward return for a sector."""
        if self.model is None:
            return 0.0

        try:
            history = self.History(self.symbols[ticker], 60, Resolution.DAILY)
            if history.empty or len(history) < 50:
                return 0.0

            features = self.calculate_features(history)
            latest = features.iloc[-1:].values
            latest = self.scaler.transform(latest)

            return float(self.model.predict(latest)[0])
        except Exception:
            return 0.0

    def on_monday(self):
        """Bi-weekly: train week 1, trade week 2."""
        if self.IsWarmingUp:
            return

        self.week_counter += 1
        if self.week_counter % 2 == 1:
            self.train_model()
        else:
            self.rebalance()

    def rebalance(self):
        """Select sectors with highest predicted returns."""
        if self.model is None:
            return

        is_bear = not self.spy_sma200.IsReady or self.Securities[self.spy].Price < self.spy_sma200.Current.Value

        predictions = {}
        for ticker in self.tickers:
            predictions[ticker] = self.predict_return(ticker)

        sorted_preds = sorted(predictions.items(), key=lambda x: x[1], reverse=True)

        # Only select sectors with positive predicted return
        max_pos = 2 if is_bear else self.max_positions
        threshold = 0.0 if not is_bear else 0.005

        selected = [(t, p) for t, p in sorted_preds if p > threshold][:max_pos]

        target_symbols = {self.symbols[t] for t, _ in selected}

        for holding in self.Portfolio.Values:
            if holding.Invested and holding.Symbol not in target_symbols:
                self.Liquidate(holding.Symbol)

        if selected:
            weight = self.allocation_pct / len(selected)
            for ticker, _ in selected:
                self.SetHoldings(self.symbols[ticker], weight)

        bear_str = " [BEAR]" if is_bear else ""
        self.Debug(f"Rebalance{bear_str}: {len(selected)} pos | Pred: {sorted_preds[:3]}")
