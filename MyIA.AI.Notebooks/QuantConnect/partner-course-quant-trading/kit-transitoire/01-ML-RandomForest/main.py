# region imports
from AlgorithmImports import *
# endregion


class MlRandomForestAlgorithm(QCAlgorithm):
    """
    ML RandomForest Sector Rotation.

    Sector ETF rotation using Random Forest classification with walk-forward
    training. Each month the model predicts which sectors will outperform,
    allocating to the top predictions.

    Architecture:
        - Universe: 9 sector ETFs (XLK through XLRE)
        - Features: 14 technical indicators per sector
        - Model: RandomForestClassifier (200 trees, depth 6)
        - Training: 4-year rolling window, monthly retrain
        - Labels: 20-day forward return > 0; the last 20 bars of each window,
          whose forward return is unknown, are dropped (#22429). Parameters
          label_mode=legacy (old labels, those bars counted as "down") and
          rf_seed (forest seed, 42 by default) replay the measurement.
        - Rebalancing: Monthly
        - Risk: SMA200 bear filter, max 4 sectors, 5% cash buffer

    Performance (2015-2024 backtest):
        - Target Sharpe: >= 0.75
        - Benchmark: SPY Buy & Hold
        - v2: threshold 0.65, max_positions 3, allocation 95% -> Sharpe 0.286 (worse)
        - v3: threshold 0.55 (original), max_positions 4, allocation 95% -> Sharpe 0.556
          (old labels, seed 42; replayed 2026-10-25: Sharpe 0.604, same MaxDD 17.2%)
        - v4 (#22429): labels fixed, seed 42 -> Sharpe 0.387, CAGR 9.92%, MaxDD 46.6%
          (reference backtest). Seeds 0/1/7/42/99: Sharpe 0.334 to 0.453. Under the
          old labels, the seed alone moved Sharpe from 0.223 to 0.634 and MaxDD
          from 17.2% to 50.7%.
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.SetEndDate(2024, 12, 31)
        self.SetCash(100000)

        # Universe: sector ETFs
        self.tickers = [
            "XLK",  # Technology
            "XLF",  # Financials
            "XLV",  # Health Care
            "XLE",  # Energy
            "XLY",  # Consumer Discretionary
            "XLP",  # Consumer Staples
            "XLI",  # Industrials
            "XLU",  # Utilities
            "XLRE", # Real Estate
        ]

        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.DAILY).Symbol

        # Benchmark for regime detection
        self.spy = self.AddEquity("SPY", Resolution.DAILY).Symbol

        # Model parameters
        self.lookback = 252 * 4      # 4-year training window
        self.n_estimators = 200
        self.max_depth = 6
        self.min_samples_leaf = 15
        self.max_positions = 4
        self.probability_threshold = 0.55
        self.allocation_pct = 0.95

        # Labels: "forward" drops the last 20 bars of each training window,
        # whose 20-day forward return is unknown (#22429). "legacy" keeps the
        # pre-fix behaviour, where those bars were labelled 0 ("down").
        self.label_mode = self.GetParameter("label_mode") or "forward"
        self.rf_seed = int(self.GetParameter("rf_seed") or 42)

        # Label diagnostics, summed over every retrain
        self.n_label_rows = 0
        self.n_unknown_fwd = 0
        self.n_positive = 0

        # State
        self.model = None
        self.scaler = None
        self.feature_names = None

        # SMA200 for regime detection
        self.spy_sma200 = self.SMA(self.spy, 200, Resolution.DAILY)

        # Monthly rebalance
        self.Schedule.On(
            self.DateRules.MonthStart(self.spy),
            self.TimeRules.AfterMarketOpen(self.spy, 30),
            self.monthly_action,
        )

        self.SetWarmUp(200, Resolution.DAILY)

    def calculate_features(self, history):
        """Calculate 14 technical features for a single asset."""
        closes = history["close"]
        volumes = history["volume"]
        highs = history["high"]
        lows = history["low"]

        returns = closes.pct_change()

        # SMA ratios
        sma_5 = closes.rolling(5).mean()
        sma_20 = closes.rolling(20).mean()
        sma_50 = closes.rolling(50).mean()

        # RSI
        delta = closes.diff()
        gain = delta.where(delta > 0, 0).rolling(14).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(14).mean()
        rs = gain / loss
        rsi = 100 - (100 / (1 + rs))

        # Bollinger Band position
        bb_mid = closes.rolling(20).mean()
        bb_std = closes.rolling(20).std()
        bb_pos = (closes - bb_mid) / (2 * bb_std)

        # MACD histogram
        ema12 = closes.ewm(span=12).mean()
        ema26 = closes.ewm(span=26).mean()
        macd = ema12 - ema26
        macd_signal = macd.ewm(span=9).mean()
        macd_hist = macd - macd_signal

        # Momentum
        mom_5 = closes.pct_change(5)
        mom_10 = closes.pct_change(10)
        mom_20 = closes.pct_change(20)
        mom_50 = closes.pct_change(50)

        # Volatility
        vol_20 = returns.rolling(20).std()

        # Volume ratio
        vol_sma = volumes.rolling(20).mean()
        volume_ratio = volumes / vol_sma

        # Price position in 50-day range
        low_50 = lows.rolling(50).min()
        high_50 = highs.rolling(50).max()
        range_pos = (closes - low_50) / (high_50 - low_50)

        features = pd.DataFrame({
            "rsi": rsi,
            "bb_position": bb_pos,
            "macd_hist": macd_hist,
            "mom_5": mom_5,
            "mom_10": mom_10,
            "mom_20": mom_20,
            "mom_50": mom_50,
            "vol_20": vol_20,
            "volume_ratio": volume_ratio,
            "price_sma20": closes / sma_20,
            "price_sma50": closes / sma_50,
            "sma_ratio_5_20": sma_5 / sma_20,
            "sma_ratio_20_50": sma_20 / sma_50,
            "range_position": range_pos,
        })

        return features.fillna(0).replace([np.inf, -np.inf], 0)

    def train_model(self):
        """Train RF on pooled sector data with rolling window."""
        from sklearn.ensemble import RandomForestClassifier
        from sklearn.preprocessing import StandardScaler

        all_X, all_y = [], []

        for ticker in self.tickers:
            try:
                history = self.History(self.symbols[ticker], self.lookback, Resolution.DAILY)
                if history.empty or len(history) < 100:
                    continue

                features = self.calculate_features(history)
                closes = history["close"]

                # Target: positive 20-day forward return. The last 20 bars have
                # no forward return: NaN > 0 is False, so they must be masked
                # explicitly, otherwise they are all labelled 0.
                future_ret = closes.pct_change(20).shift(-20)
                target = (future_ret > 0).astype(int)
                if self.label_mode != "legacy":
                    target = target.where(future_ret.notna())

                features["target"] = target
                features = features.dropna()

                self.n_unknown_fwd += int(future_ret.isna().sum())
                self.n_label_rows += len(features)
                self.n_positive += int(features["target"].sum())

                if len(features) > 50:
                    all_X.append(features.drop("target", axis=1))
                    all_y.append(features["target"])
            except Exception:
                continue

        if not all_X:
            return

        X = pd.concat(all_X, ignore_index=True)
        y = pd.concat(all_y, ignore_index=True)

        self.feature_names = X.columns.tolist()

        self.scaler = StandardScaler()
        X_scaled = self.scaler.fit_transform(X)

        self.model = RandomForestClassifier(
            n_estimators=self.n_estimators,
            max_depth=self.max_depth,
            min_samples_leaf=self.min_samples_leaf,
            random_state=self.rf_seed,
            n_jobs=-1,
        )
        self.model.fit(X_scaled, y)

    def predict_proba(self, ticker):
        """Get probability of positive return for a sector."""
        if self.model is None:
            return 0.5

        try:
            history = self.History(self.symbols[ticker], 60, Resolution.DAILY)
            if history.empty or len(history) < 50:
                return 0.5

            features = self.calculate_features(history)
            latest = features.iloc[-1:].values
            latest = self.scaler.transform(latest)

            proba = self.model.predict_proba(latest)[0]
            return proba[1] if len(proba) > 1 else 0.5
        except Exception:
            return 0.5

    def monthly_action(self):
        """Train and rebalance on month start."""
        if self.IsWarmingUp:
            return

        self.train_model()
        self.rebalance()

    def rebalance(self):
        """Select top sectors and allocate."""
        if self.model is None:
            return

        # Regime detection
        is_bear = not self.spy_sma200.IsReady or self.Securities[self.spy].Price < self.spy_sma200.Current.Value

        predictions = {}
        for ticker in self.tickers:
            predictions[ticker] = self.predict_proba(ticker)

        # Sort by probability
        sorted_preds = sorted(predictions.items(), key=lambda x: x[1], reverse=True)

        # Select top sectors above threshold
        threshold = self.probability_threshold
        max_pos = 2 if is_bear else self.max_positions

        selected = [(t, p) for t, p in sorted_preds if p > threshold][:max_pos]

        target_symbols = {self.symbols[t] for t, _ in selected}

        # Liquidate positions not in target
        for holding in self.Portfolio.Values:
            if holding.Invested and holding.Symbol not in target_symbols:
                self.Liquidate(holding.Symbol)

        # Allocate to selected sectors
        if selected:
            weight = self.allocation_pct / len(selected)
            for ticker, _ in selected:
                self.SetHoldings(self.symbols[ticker], weight)

        # Log
        bear_str = " [BEAR MODE]" if is_bear else ""
        top3 = ", ".join(f"{t}:{p:.2f}" for t, p in sorted_preds[:3])
        self.Debug(f"Rebalance{bear_str}: {len(selected)} positions | Top3: {top3}")

    def OnEndOfAlgorithm(self):
        """Publish the label diagnostics as runtime statistics."""
        if self.n_label_rows:
            self.SetRuntimeStatistic("Label rows", str(self.n_label_rows))
            self.SetRuntimeStatistic("Unknown fwd", str(self.n_unknown_fwd))
            self.SetRuntimeStatistic("Up share", f"{self.n_positive / self.n_label_rows:.4f}")
        self.Log(f"labels mode={self.label_mode} seed={self.rf_seed} rows={self.n_label_rows} "
                 f"unknown_fwd={self.n_unknown_fwd} up={self.n_positive}")
