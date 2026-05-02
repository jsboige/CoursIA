# region imports
from AlgorithmImports import *
# endregion


class MLFeatureEngineeringAlgorithm(QCAlgorithm):
    """
    Enriched Feature ML Stock Selection Strategy.

    Source: ECE student project (Balssa, Gr01 H.1), adapted for ESGF pool.
    Issue #238 - Integrate ECE student concepts into QC strategies.

    Harvests novel features from student 23-feature pipeline:
    - volume_trend, adx_norm, bb_width, atr_norm (technical)
    - pe_norm, pb_norm, roe_norm, debt_equity_norm (fundamental)

    Uses RF + GB ensemble with walk-forward validation.

    Baseline comparison: ML-RandomForest v3 (Sharpe 0.682, 12 features).
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.SetCash(100000)

        # Universe: Liquid large-cap stocks (same as ML-RandomForest baseline)
        self.tickers = [
            "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA",
            "META", "TSLA", "JPM", "V", "WMT"
        ]

        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.DAILY).Symbol

        # Model parameters (from student: RF 200 trees depth 5, GB 150 trees depth 4)
        self.lookback = 252  # ~1 year training window
        self.rf_n_estimators = 200
        self.rf_max_depth = 5
        self.gb_n_estimators = 150
        self.gb_max_depth = 4
        self.gb_learning_rate = 0.08
        self.prediction_horizon = 5  # predict 5-day forward return
        self.threshold = 0.57  # confidence threshold for selection
        self.max_positions = 5

        # Rebalance schedule: bi-weekly (1st and 3rd Monday)
        self.week_counter = 0
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.on_monday)

        # Monthly retraining
        self.Schedule.On(self.DateRules.MonthStart("SPY"),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.train_model)

        self.rf_model = None
        self.gb_model = None
        self.scaler = None
        self.feature_names = None

        # Warmup for indicator calculation (200-day SMA needs 200 bars)
        self.SetWarmUp(210, Resolution.Daily)

    def on_monday(self):
        """Bi-weekly rebalance trigger."""
        self.week_counter += 1
        if self.week_counter % 2 == 0:
            self.rebalance()

    # ----------------------------------------------------------------
    # Feature Engineering (18 features: 12 baseline + 6 novel)
    # ----------------------------------------------------------------

    def calculate_features(self, history):
        """
        Calculate enriched feature set for ML prediction.

        12 baseline features (from ML-RandomForest v3):
            rsi, bb_position, macd_hist, mom_5, mom_10, mom_20,
            vol_20, volume_ratio, price_sma20, price_sma50,
            sma_ratio_5_20, sma_ratio_20_50

        6 novel features (from Balssa student project):
            volume_trend, adx_norm, bb_width, atr_norm,
            mom_60, vol_60
        """
        closes = history['close']
        volumes = history['volume']
        highs = history['high']
        lows = history['low']

        returns = closes.pct_change()

        # --- Baseline features (same as ML-RandomForest v3) ---

        sma_5 = closes.rolling(5).mean()
        sma_20 = closes.rolling(20).mean()
        sma_50 = closes.rolling(50).mean()

        # RSI (14-period)
        delta = closes.diff()
        gain = (delta.where(delta > 0, 0)).rolling(14).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(14).mean()
        rs = gain / loss
        rsi = 100 - (100 / (1 + rs))

        # MACD (12, 26, 9)
        ema_12 = closes.ewm(span=12).mean()
        ema_26 = closes.ewm(span=26).mean()
        macd = ema_12 - ema_26
        macd_signal = macd.ewm(span=9).mean()

        # Bollinger Bands (20, 2)
        bb_middle = closes.rolling(20).mean()
        bb_std = closes.rolling(20).std()
        bb_position = (closes - bb_middle) / (2 * bb_std)

        # Momentum
        momentum_5 = closes / closes.shift(5) - 1
        momentum_10 = closes / closes.shift(10) - 1
        momentum_20 = closes / closes.shift(20) - 1

        # Volatility (20-day)
        volatility_20 = returns.rolling(20).std()

        # Volume ratio
        volume_sma = volumes.rolling(20).mean()
        volume_ratio = volumes / volume_sma

        # Price ratios
        price_to_sma20 = closes / sma_20
        price_to_sma50 = closes / sma_50

        # --- Novel features (from Balssa student project) ---

        # 1. Volume trend: 10-day volume vs 50-day volume (momentum of volume)
        vol_sma_10 = volumes.rolling(10).mean()
        vol_sma_50 = volumes.rolling(50).mean()
        volume_trend = vol_sma_10 / vol_sma_50

        # 2. ADX (Average Directional Index, 14-period)
        adx = self._calculate_adx(highs, lows, closes, period=14)
        adx_norm = adx / 100.0  # Normalize to [0, 1]

        # 3. Bollinger Band width (normalized)
        bb_width = (4 * bb_std) / bb_middle

        # 4. ATR (Average True Range, 14-period, normalized)
        atr = self._calculate_atr(highs, lows, closes, period=14)
        atr_norm = atr / closes

        # 5. 60-day momentum
        momentum_60 = closes / closes.shift(60) - 1

        # 6. 60-day volatility
        volatility_60 = returns.rolling(60).std()

        features = pd.DataFrame({
            # Baseline (12)
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
            # Novel (6)
            'volume_trend': volume_trend,
            'adx_norm': adx_norm,
            'bb_width': bb_width,
            'atr_norm': atr_norm,
            'mom_60': momentum_60,
            'vol_60': volatility_60,
        })

        return features.fillna(0).replace([np.inf, -np.inf], 0)

    @staticmethod
    def _calculate_atr(highs, lows, closes, period=14):
        """Calculate Average True Range."""
        tr1 = highs - lows
        tr2 = (highs - closes.shift(1)).abs()
        tr3 = (lows - closes.shift(1)).abs()
        true_range = pd.concat([tr1, tr2, tr3], axis=1).max(axis=1)
        return true_range.rolling(period).mean()

    @staticmethod
    def _calculate_adx(highs, lows, closes, period=14):
        """Calculate Average Directional Index."""
        # True Range
        tr1 = highs - lows
        tr2 = (highs - closes.shift(1)).abs()
        tr3 = (lows - closes.shift(1)).abs()
        tr = pd.concat([tr1, tr2, tr3], axis=1).max(axis=1)

        # Directional Movement
        up_move = highs - highs.shift(1)
        down_move = lows.shift(1) - lows

        plus_dm = up_move.where((up_move > down_move) & (up_move > 0), 0)
        minus_dm = down_move.where((down_move > up_move) & (down_move > 0), 0)

        # Smoothed values (Wilder's method via EMA approximation)
        atr = tr.rolling(period).mean()
        plus_di = 100 * (plus_dm.rolling(period).mean() / atr)
        minus_di = 100 * (minus_dm.rolling(period).mean() / atr)

        # DX and ADX
        di_sum = plus_di + minus_di
        di_sum = di_sum.replace(0, 1)  # avoid division by zero
        dx = 100 * (plus_di - minus_di).abs() / di_sum
        adx = dx.rolling(period).mean()

        return adx.fillna(0)

    # ----------------------------------------------------------------
    # Model Training (RF + GB Ensemble)
    # ----------------------------------------------------------------

    def train_model(self):
        """Train RF + GB ensemble with walk-forward validation."""
        if self.IsWarmingUp:
            return

        from sklearn.ensemble import (
            RandomForestClassifier,
            GradientBoostingClassifier
        )
        from sklearn.preprocessing import StandardScaler

        all_features = []
        all_targets = []

        for ticker in self.tickers:
            try:
                history = self.History(
                    self.symbols[ticker], self.lookback, Resolution.Daily
                )
                if history.empty or len(history) < 100:
                    continue

                features = self.calculate_features(history)
                closes = history['close']

                # Target: positive return over prediction_horizon days
                future_return = closes.pct_change(self.prediction_horizon).shift(
                    -self.prediction_horizon
                )
                target = (future_return > 0).astype(int)

                features['target'] = target
                features = features.dropna()

                if len(features) > 30:
                    all_features.append(features.drop('target', axis=1))
                    all_targets.append(features['target'])

            except Exception as e:
                self.Debug(f"Train error {ticker}: {e}")
                continue

        if not all_features:
            return

        X = pd.concat(all_features, ignore_index=True)
        y = pd.concat(all_targets, ignore_index=True)
        self.feature_names = X.columns.tolist()

        # StandardScaler (student used StandardScaler, baseline used MinMaxScaler)
        self.scaler = StandardScaler()
        X_scaled = self.scaler.fit_transform(X)

        # Random Forest
        self.rf_model = RandomForestClassifier(
            n_estimators=self.rf_n_estimators,
            max_depth=self.rf_max_depth,
            min_samples_split=10,
            random_state=42,
            n_jobs=-1
        )
        self.rf_model.fit(X_scaled, y)

        # Gradient Boosting
        self.gb_model = GradientBoostingClassifier(
            n_estimators=self.gb_n_estimators,
            max_depth=self.gb_max_depth,
            learning_rate=self.gb_learning_rate,
            min_samples_split=10,
            random_state=42
        )
        self.gb_model.fit(X_scaled, y)

        self.Debug(
            f"Trained ensemble on {len(X)} samples, "
            f"{len(self.feature_names)} features"
        )

    # ----------------------------------------------------------------
    # Prediction & Rebalancing
    # ----------------------------------------------------------------

    def predict(self, ticker, history):
        """Predict using RF + GB ensemble averaging."""
        if self.rf_model is None or self.gb_model is None:
            return 0.5

        features = self.calculate_features(history)
        if len(features) == 0:
            return 0.5

        latest = features.iloc[-1:].values
        latest = self.scaler.transform(latest)

        # Ensemble: average of RF and GB probabilities
        rf_proba = self.rf_model.predict_proba(latest)[0][1]
        gb_proba = self.gb_model.predict_proba(latest)[0][1]
        return (rf_proba + gb_proba) / 2.0

    def rebalance(self):
        """Rebalance based on ensemble predictions with confidence weighting."""
        if self.IsWarmingUp or self.rf_model is None:
            return

        predictions = {}
        for ticker in self.tickers:
            try:
                history = self.History(
                    self.symbols[ticker], self.lookback, Resolution.Daily
                )
                if history.empty:
                    continue
                predictions[ticker] = self.predict(ticker, history)
            except Exception:
                continue

        if not predictions:
            return

        sorted_preds = sorted(
            predictions.items(), key=lambda x: x[1], reverse=True
        )

        # Select stocks above confidence threshold
        selected = [
            (t, p) for t, p in sorted_preds if p > self.threshold
        ][:self.max_positions]

        target_symbols = {self.symbols[t] for t, _ in selected}

        # Liquidate non-target positions
        for holding in self.Portfolio.Values:
            if holding.Invested and holding.Symbol not in target_symbols:
                self.Liquidate(holding.Symbol)

        # Allocate with confidence-weighted sizing
        if selected:
            # Weight proportional to confidence (prob - 0.5) * scaling
            raw_weights = {
                t: max(0.01, (p - 0.5) * 2.0) for t, p in selected
            }
            total_raw = sum(raw_weights.values())
            # Normalize so total allocation is 90%
            for ticker, prob in selected:
                weight = 0.90 * raw_weights[ticker] / total_raw
                self.SetHoldings(self.symbols[ticker], weight)
