# region imports
from AlgorithmImports import *
# endregion

class MLEnhancedPairsAlgorithm(QCAlgorithm):
    """
    ML-Enhanced Pairs Trading Strategy.

    Strategy:
    - Select cointegrated pairs (Engle-Granger test)
    - Use ML classifier to predict entry/exit timing
    - Features: Z-score, half-life, volatility regime
    - Long/short based on prediction and pair dynamics
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.SetCash(100000)

        # Universe: Sector ETFs for pairs
        self.etf_pairs = [
            ("XLE", "XLP"),  # Energy vs Consumer Staples
            ("XLV", "XLU"),  # Healthcare vs Utilities
            ("XLF", "XLK"),  # Financial vs Tech
            ("XLY", "XLP"),  # Discretionary vs Staples
            ("XLK", "XLE"),  # Tech vs Energy
        ]

        self.symbols = {}
        for ticker1, ticker2 in self.etf_pairs:
            self.symbols[ticker1] = self.AddEquity(ticker1, Resolution.Daily).Symbol
            self.symbols[ticker2] = self.AddEquity(ticker2, Resolution.Daily).Symbol

        # Model parameters
        self.lookback = 90
        self.z_entry = 2.0
        self.z_exit = 0.5
        self.min_half_life = 5
        self.max_half_life = 60
        self.max_pairs = 3

        # Rebalance schedule
        self.Schedule.On(self.DateRules.EveryDay("SPY"),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.Rebalance)

        # Train model weekly
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.TrainModel)

        self.model = None
        self.scaler = None
        self.active_pairs = []

    def TrainModel(self):
        """Train ML model for entry/exit prediction."""
        self.Debug("Training ML model for pairs...")

        # Get historical data for all pairs
        history = self.History(list(self.symbols.values()), self.lookback, Resolution.Daily)

        if history.empty or len(history) < self.lookback:
            return

        # Prepare features and labels
        X, y = self.PrepareMLFeatures(history)

        if X is None or len(X) < 20:
            return

        # Train classifier
        from sklearn.ensemble import RandomForestClassifier
        from sklearn.preprocessing import StandardScaler

        self.scaler = StandardScaler()
        X_scaled = self.scaler.fit_transform(X)

        self.model = RandomForestClassifier(n_estimators=50, max_depth=5, random_state=42)
        self.model.fit(X_scaled, y)

        train_acc = self.model.score(X_scaled, y)
        self.Debug(f"Model trained. Accuracy: {train_acc:.3f}")

    def PrepareMLFeatures(self, history):
        """Prepare ML features from pair spreads."""
        closes = history['close'].unstack(level=0)
        symbol_to_ticker = {str(v): k for k, v in self.symbols.items()}
        closes.columns = [symbol_to_ticker.get(str(c), str(c)) for c in closes.columns]

        features_list = []
        labels_list = []

        for ticker1, ticker2 in self.etf_pairs:
            if ticker1 not in closes.columns or ticker2 not in closes.columns:
                continue

            # Calculate spread
            spread = self.CalculateSpread(closes[ticker1], closes[ticker2])
            if spread is None:
                continue

            # Features
            zscore = self.CalculateZScore(spread)
            half_life = self.CalculateHalfLife(spread)

            if half_life < self.min_half_life or half_life > self.max_half_life:
                continue

            # Volatility regime
            vol = spread.pct_change().rolling(20).std()
            vol_regime = (vol > vol.rolling(60).mean()).astype(int)

            # Momentum
            momentum = spread.pct_change(5)

            # Combine features
            df = pd.DataFrame({
                'ZScore': zscore,
                'HalfLife': half_life,
                'VolRegime': vol_regime,
                'Momentum': momentum,
            })

            # Label: 1 if good entry (|z| > 2), 0 otherwise
            df['Label'] = (np.abs(zscore) > self.z_entry).astype(int)

            df = df.dropna()

            if len(df) > 10:
                features_list.append(df.drop('Label', axis=1))
                labels_list.append(df['Label'])

        if not features_list:
            return None, None

        X = pd.concat(features_list, ignore_index=True)
        y = pd.concat(labels_list, ignore_index=True)

        return X.fillna(0), y.fillna(0)

    def CalculateSpread(self, price1, price2):
        """Calculate cointegrated spread using OLS hedge ratio."""
        import statsmodels.api as sm

        df = pd.DataFrame({'y': price1, 'x': price2}).dropna()

        if len(df) < 30:
            return None

        # OLS regression for hedge ratio
        x = sm.add_constant(df['x'])
        result = sm.OLS(df['y'], x).fit()
        hedge_ratio = result.params['x']

        # Calculate spread
        spread = df['y'] - hedge_ratio * df['x']

        # Test for cointegration (ADF test)
        from statsmodels.tsa.stattools import adfuller
        adf_result = adfuller(spread.dropna())

        if adf_result[1] > 0.05:  # Not cointegrated
            return None

        return spread

    def CalculateZScore(self, spread):
        """Calculate rolling Z-score of spread."""
        return (spread - spread.rolling(20).mean()) / spread.rolling(20).std()

    def CalculateHalfLife(self, spread):
        """Calculate half-life of mean reversion."""
        df = pd.DataFrame({'spread': spread}).dropna()

        if len(df) < 10:
            return 999

        df['spread_lag'] = df['spread'].shift(1)
        df = df.dropna()

        # AR(1) regression
        from sklearn.linear_model import LinearRegression
        model = LinearRegression()
        model.fit(df[['spread_lag']], df['spread'])

        lambda_coef = model.coef_[0]

        if lambda_coef >= 1:
            return 999

        half_life = -np.log(2) / np.log(lambda_coef)
        return max(0, half_life)

    def Rebalance(self):
        """Rebalance based on ML predictions and pair dynamics."""
        if self.model is None or self.scaler is None:
            return

        # Get recent data
        history = self.History(list(self.symbols.values()), self.lookback, Resolution.Daily)

        if history.empty:
            return

        closes = history['close'].unstack(level=0)
        symbol_to_ticker = {str(v): k for k, v in self.symbols.items()}
        closes.columns = [symbol_to_ticker.get(str(c), str(c)) for c in closes.columns]

        # Evaluate each pair
        pair_scores = []

        for ticker1, ticker2 in self.etf_pairs:
            if ticker1 not in closes.columns or ticker2 not in closes.columns:
                continue

            spread = self.CalculateSpread(closes[ticker1], closes[ticker2])
            if spread is None:
                continue

            half_life = self.CalculateHalfLife(spread)
            if half_life < self.min_half_life or half_life > self.max_half_life:
                continue

            zscore = self.CalculateZScore(spread)
            current_z = zscore.iloc[-1]

            # ML prediction
            vol_regime = (spread.pct_change().rolling(20).std().iloc[-1] >
                         spread.pct_change().rolling(60).std().mean())
            momentum = spread.pct_change(5).iloc[-1]

            features = [[current_z, half_life, int(vol_regime), momentum]]
            features_scaled = self.scaler.transform(features)

            prediction = self.model.predict_proba(features_scaled)[0][1]

            # Score combines ML prediction and Z-score magnitude
            score = prediction * np.abs(current_z)
            pair_scores.append((ticker1, ticker2, current_z, score, half_life))

        # Sort by score
        pair_scores.sort(key=lambda x: x[3], reverse=True)

        # Select top pairs
        selected_pairs = pair_scores[:self.max_pairs]

        # Liquidate existing positions
        self.Liquidate()

        # Enter positions
        for ticker1, ticker2, z, score, hl in selected_pairs:
            if z > self.z_entry:
                # Short the spread (short ticker1, long ticker2)
                self.SetHoldings(self.symbols[ticker1], -0.45)
                self.SetHoldings(self.symbols[ticker2], 0.45)
            elif z < -self.z_entry:
                # Long the spread (long ticker1, short ticker2)
                self.SetHoldings(self.symbols[ticker1], 0.45)
                self.SetHoldings(self.symbols[ticker2], -0.45)

        self.Debug(f"Active pairs: {len(selected_pairs)}")
