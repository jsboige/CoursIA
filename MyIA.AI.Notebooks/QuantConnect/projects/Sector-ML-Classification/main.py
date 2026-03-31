# region imports
from AlgorithmImports import *
from datetime import datetime
import numpy as np
from sklearn.ensemble import RandomForestClassifier
from sklearn.preprocessing import StandardScaler
# endregion


class SectorMLClassificationAlgorithm(QCAlgorithm):
    """
    Sector Rotation with ML Classification - v5.

    v5 changes (from v4 Sharpe 0.308, Beta 0.639, Alpha +0.003, MaxDD 32.7%):
    - Always select top-N sectors by buy probability (no cash drag in bull)
    - In bull market: always hold top 4 sectors ranked by RF buy probability
    - In bear market: hold top 2 defensive sectors OR go cash if best prob < 0.35
    - Equal weight (simpler, more robust than confidence-weighted for 8 sectors)
    - Keep monthly retraining and 11 features from v4

    v4 analysis:
    - Alpha +0.003 is good (first positive alpha!)
    - Beta 0.639 confirms signal-driven (not beta-loading)
    - But Sharpe 0.308 < v2b 0.352: cash drag in bull markets
    - When all RF proba < 0.50 threshold, strategy holds stale positions
    - Fix: always rebalance to top-N, threshold only filters bear cash decision

    Performance history:
    - v2b (2018-2026): Sharpe 0.352, Beta 0.964, Alpha -0.007, MaxDD 41.7%
    - v3   (2015-2026): Sharpe 0.288, Beta 0.832, Alpha -0.012, MaxDD 36.0%
    - v3.1 (2015-2026): Sharpe 0.253, Beta 0.833, Alpha -0.018, MaxDD 39.1%
    - v4   (2015-2026): Sharpe 0.308, Beta 0.639, Alpha +0.003, MaxDD 32.7%
    - v5   (2015-2026): Sharpe 0.473, Beta 0.799, Alpha +0.009, MaxDD 34.4%
    """

    SECTOR_ETFS = {
        "XLK": "Technology",
        "XLF": "Financials",
        "XLV": "Healthcare",
        "XLE": "Energy",
        "XLY": "Consumer Discretionary",
        "XLP": "Consumer Staples",
        "XLI": "Industrials",
        "XLU": "Utilities"
    }

    DEFENSIVE_SECTORS = ["XLU", "XLP", "XLV"]

    TRAIN_LOOKBACK_DAYS = 252 * 4  # 4-year rolling window
    FORWARD_DAYS = 10              # 10-day forward return (biweekly cycle)
    BUY_THRESHOLD = 0.012          # 1.2% over 10 days = buy signal
    AVOID_THRESHOLD = -0.008       # -0.8% over 10 days = avoid signal
    TOP_N_SECTORS = 4              # positions in bull regime
    BEAR_N_SECTORS = 2             # positions in bear regime
    BEAR_MIN_PROB = 0.35           # in bear: go cash if best defensive prob < this
    RF_N_ESTIMATORS = 100
    RF_MAX_DEPTH = 5
    RF_MIN_SAMPLES_LEAF = 10
    SMA_SHORT = 20
    SMA_LONG = 50
    SMA200_PERIOD = 200

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)

        self.etf_tickers = list(self.SECTOR_ETFS.keys())
        self.symbols = []
        self.symbol_map = {}  # ticker -> symbol

        for ticker in self.etf_tickers:
            symbol = self.add_equity(ticker, Resolution.DAILY, Market.USA).Symbol
            self.symbols.append(symbol)
            self.symbol_map[ticker] = symbol

        self._spy = self.add_equity("SPY", Resolution.DAILY, Market.USA).Symbol
        self.set_benchmark(self._spy)

        self.model = None
        self.scaler = None

        # Indicators per sector
        self.indicators = {}
        for symbol in self.symbols:
            self.indicators[symbol.ID] = {
                'rsi': self.RSI(symbol, 14, MovingAverageType.Wilders, Resolution.DAILY),
                'sma_short': self.SMA(symbol, self.SMA_SHORT, Resolution.DAILY),
                'sma_long': self.SMA(symbol, self.SMA_LONG, Resolution.DAILY),
            }

        # SPY SMA200 for bear market regime
        self._spy_sma200 = self.SMA(self._spy, self.SMA200_PERIOD, Resolution.DAILY)

        # Biweekly rebalance: month-start + approx mid-month
        self.schedule.on(self.date_rules.month_start("SPY"),
                         self.time_rules.after_market_open("SPY", 30),
                         self.rebalance)
        self.schedule.on(self.date_rules.month_start("SPY", 14),
                         self.time_rules.after_market_open("SPY", 30),
                         self.rebalance)

        # Monthly retraining
        self.schedule.on(self.date_rules.month_start("SPY"),
                         self.time_rules.after_market_open("SPY", 60),
                         self.train_model)

        self.set_warm_up(self.SMA200_PERIOD + 20, Resolution.DAILY)

    def is_bear_market(self):
        """Return True if SPY is below its 200-day SMA."""
        if not self._spy_sma200.is_ready:
            return False
        spy_price = self.securities[self._spy].price
        return spy_price < self._spy_sma200.current.value

    def get_features_live(self, symbol):
        """Calculate 11 features for live prediction."""
        indicators = self.indicators[symbol.ID]
        if not all(ind.is_ready for ind in indicators.values()):
            return None

        current_price = self.securities[symbol].price
        spy_price = self.securities[self._spy].price
        history = self.history(symbol, 260, Resolution.DAILY)
        spy_history = self.history(self._spy, 260, Resolution.DAILY)

        if history is None or len(history) < self.SMA_LONG:
            return None
        if 'close' not in history.columns:
            return None

        closes = history['close']
        if len(closes) < 50:
            return None

        returns_5d = (current_price / closes.iloc[-5] - 1) if len(closes) >= 5 else 0.0
        returns_10d = (current_price / closes.iloc[-10] - 1) if len(closes) >= 10 else 0.0
        returns_20d = (current_price / closes.iloc[-20] - 1) if len(closes) >= 20 else 0.0
        returns_50d = (current_price / closes.iloc[-50] - 1) if len(closes) >= 50 else 0.0

        daily_returns = closes.pct_change().dropna()
        vol = daily_returns.rolling(20).std().iloc[-1]
        volatility = float(vol) if not np.isnan(float(vol)) else 0.01

        rsi = indicators['rsi'].current.value
        rsi_normalized = (rsi - 50) / 50

        sma_short = indicators['sma_short'].current.value
        sma_long = indicators['sma_long'].current.value
        ma_ratio = sma_short / sma_long if sma_long > 0 else 1.0

        if 'high' in history.columns and 'low' in history.columns:
            high_20d = float(history['high'].rolling(20).max().iloc[-1])
            low_20d = float(history['low'].rolling(20).min().iloc[-1])
            position_in_range = (
                (current_price - low_20d) / (high_20d - low_20d)
                if high_20d > low_20d else 0.5
            )
        else:
            position_in_range = 0.5

        high_52w = closes.rolling(252).max().iloc[-1] if len(closes) >= 252 else closes.max()
        ratio_52w_high = current_price / high_52w if high_52w > 0 else 1.0

        spy_ret_5d = 0.0
        spy_ret_10d = 0.0
        if (spy_history is not None and len(spy_history) >= 10
                and 'close' in spy_history.columns):
            spy_closes = spy_history['close']
            spy_ret_5d = (spy_price / spy_closes.iloc[-5] - 1) if len(spy_closes) >= 5 else 0.0
            spy_ret_10d = (spy_price / spy_closes.iloc[-10] - 1) if len(spy_closes) >= 10 else 0.0

        relative_5d = returns_5d - spy_ret_5d
        relative_10d = returns_10d - spy_ret_10d

        features = [
            returns_5d, returns_10d, returns_20d, returns_50d,
            volatility, rsi_normalized, ma_ratio, position_in_range,
            ratio_52w_high, relative_5d, relative_10d
        ]

        if any(np.isnan(f) for f in features):
            return None

        return features

    def get_features_historical(self, sector_prices, spy_prices, date):
        """Calculate 11 features from historical price series up to date."""
        data = sector_prices[:date]
        spy_data = spy_prices[:date]

        if len(data) < self.SMA_LONG or len(spy_data) < 10:
            return None

        current_price = data.iloc[-1]
        spy_price = spy_data.iloc[-1]

        if pd.isna(current_price) or current_price == 0:
            return None

        returns_5d = (current_price / data.iloc[-5] - 1) if len(data) >= 5 else 0.0
        returns_10d = (current_price / data.iloc[-10] - 1) if len(data) >= 10 else 0.0
        returns_20d = (current_price / data.iloc[-20] - 1) if len(data) >= 20 else 0.0
        returns_50d = (current_price / data.iloc[-50] - 1) if len(data) >= 50 else 0.0

        daily_returns = data.pct_change().dropna()
        vol_val = daily_returns.rolling(20).std().iloc[-1]
        volatility = (
            float(vol_val) if len(daily_returns) >= 20 and not pd.isna(vol_val) else 0.01
        )

        delta = data.diff()
        gain = delta.clip(lower=0)
        loss = -delta.clip(lower=0)
        avg_gain = gain.rolling(14).mean().iloc[-1]
        avg_loss = loss.rolling(14).mean().iloc[-1]
        rs = avg_gain / avg_loss if avg_loss > 0 else 0.0
        rsi = 100 - (100 / (1 + rs))
        rsi_normalized = (rsi - 50) / 50

        sma_short = data.rolling(self.SMA_SHORT).mean().iloc[-1]
        sma_long = data.rolling(self.SMA_LONG).mean().iloc[-1]
        ma_ratio = sma_short / sma_long if sma_long > 0 else 1.0

        high_20d = data.rolling(20).max().iloc[-1]
        low_20d = data.rolling(20).min().iloc[-1]
        position_in_range = (
            (current_price - low_20d) / (high_20d - low_20d)
            if high_20d > low_20d else 0.5
        )

        high_52w = data.rolling(252).max().iloc[-1] if len(data) >= 252 else data.max()
        ratio_52w_high = current_price / high_52w if high_52w > 0 else 1.0

        spy_ret_5d = (spy_price / spy_data.iloc[-5] - 1) if len(spy_data) >= 5 else 0.0
        spy_ret_10d = (spy_price / spy_data.iloc[-10] - 1) if len(spy_data) >= 10 else 0.0
        relative_5d = returns_5d - spy_ret_5d
        relative_10d = returns_10d - spy_ret_10d

        features = [
            returns_5d, returns_10d, returns_20d, returns_50d,
            volatility, rsi_normalized, ma_ratio, position_in_range,
            ratio_52w_high, relative_5d, relative_10d
        ]

        if any(np.isnan(f) for f in features):
            return None

        return features

    def train_model(self):
        """Train on rolling 4-year window with 10-day forward returns."""
        if self.is_warming_up:
            return

        train_end = self.time - timedelta(days=15)
        train_start = train_end - timedelta(days=self.TRAIN_LOOKBACK_DAYS)

        try:
            all_symbols = self.symbols + [self._spy]
            history = self.history(all_symbols, train_start, train_end, Resolution.DAILY)

            if history is None or len(history) == 0:
                return

            if 'close' not in history.columns:
                self.error("Training: no close column")
                return

            price_data = history['close'].unstack(level=0)

            if len(price_data) < 100:
                return

            spy_sid = self._spy.ID
            if spy_sid not in price_data.columns:
                return
            spy_prices = price_data[spy_sid]

            X_list, y_list = [], []

            # Sample every 5 days to reduce autocorrelation
            dates_to_use = price_data.index[self.SMA_LONG:-self.FORWARD_DAYS:5]

            for date in dates_to_use:
                for symbol in self.symbols:
                    sid = symbol.ID
                    if sid not in price_data.columns:
                        continue

                    future_idx = price_data.index.get_loc(date)
                    if isinstance(future_idx, slice):
                        future_idx = future_idx.start
                    if future_idx + self.FORWARD_DAYS >= len(price_data):
                        continue

                    future_price = price_data[sid].iloc[future_idx + self.FORWARD_DAYS]
                    current_price_val = price_data[sid].iloc[future_idx]

                    if (pd.isna(future_price) or pd.isna(current_price_val)
                            or current_price_val == 0):
                        continue

                    future_return = future_price / current_price_val - 1

                    if future_return > self.BUY_THRESHOLD:
                        label = 2
                    elif future_return < self.AVOID_THRESHOLD:
                        label = 0
                    else:
                        label = 1

                    features = self.get_features_historical(
                        price_data[sid], spy_prices, date
                    )
                    if features is not None:
                        X_list.append(features)
                        y_list.append(label)

            if len(X_list) < 50:
                self.debug(f"Not enough training samples: {len(X_list)}")
                return

            X = np.array(X_list)
            y = np.array(y_list)

            self.scaler = StandardScaler()
            X_scaled = self.scaler.fit_transform(X)

            self.model = RandomForestClassifier(
                n_estimators=self.RF_N_ESTIMATORS,
                max_depth=self.RF_MAX_DEPTH,
                min_samples_leaf=self.RF_MIN_SAMPLES_LEAF,
                random_state=42,
                n_jobs=-1
            )
            self.model.fit(X_scaled, y)
            unique, counts = np.unique(y, return_counts=True)
            class_dist = dict(zip(unique.tolist(), counts.tolist()))
            self.debug(f"Model trained: {len(X)} samples, classes={class_dist}")

        except Exception as e:
            self.error(f"Training error: {e}")

    def rebalance(self):
        """Biweekly rebalance with SMA200 bear regime filter."""
        if self.is_warming_up:
            return

        if self.model is None:
            self.train_model()
            if self.model is None:
                return

        bear_market = self.is_bear_market()

        if bear_market:
            # In bear: score only defensive sectors
            candidates = [
                self.symbol_map[t] for t in self.DEFENSIVE_SECTORS
                if t in self.symbol_map
            ]
            max_positions = self.BEAR_N_SECTORS
        else:
            candidates = self.symbols
            max_positions = self.TOP_N_SECTORS

        # ML scoring - probability of BUY class (class 2)
        sector_scores = {}
        for symbol in candidates:
            features = self.get_features_live(symbol)
            if features is None:
                continue
            try:
                x_arr = np.array(features).reshape(1, -1)
                x_scaled = self.scaler.transform(x_arr)
                proba = self.model.predict_proba(x_scaled)[0]
                class_list = list(self.model.classes_)
                buy_idx = class_list.index(2) if 2 in class_list else -1
                buy_prob = float(proba[buy_idx]) if buy_idx >= 0 else 0.0
                sector_scores[symbol] = buy_prob
            except Exception:
                continue

        if not sector_scores:
            # No features available: keep current positions
            return

        # Rank by buy probability
        ranked = sorted(sector_scores.items(), key=lambda x: x[1], reverse=True)
        top_candidates = ranked[:max_positions]

        if bear_market:
            # In bear: only hold if best defensive sector has meaningful signal
            best_prob = top_candidates[0][1] if top_candidates else 0.0
            if best_prob < self.BEAR_MIN_PROB:
                self.liquidate()
                self.debug(f"BEAR | best_prob={best_prob:.3f} < {self.BEAR_MIN_PROB} | Full cash")
                return
            selected = [s for s, _ in top_candidates]
        else:
            # In bull: always hold top N sectors (RF ranks which to prefer)
            selected = [s for s, _ in top_candidates]

        if not selected:
            return

        # Equal weight allocation
        weight = 1.0 / len(selected)

        # Selective liquidation: only exit positions no longer selected
        target_set = set(selected)
        for symbol in self.symbols:
            if self.portfolio[symbol].invested and symbol not in target_set:
                self.liquidate(symbol)

        for symbol in selected:
            self.set_holdings(symbol, weight)

        regime_str = "BEAR" if bear_market else "BULL"
        tickers = [
            t for t in self.etf_tickers
            if self.symbol_map.get(t) in target_set
        ]
        probs = [f"{sector_scores.get(s, 0):.2f}" for s in selected]
        self.debug(f"{regime_str} | {tickers} | probs={probs}")
