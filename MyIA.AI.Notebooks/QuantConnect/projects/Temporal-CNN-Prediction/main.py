#region imports
from AlgorithmImports import *
import numpy as np
from collections import deque
from sklearn.neural_network import MLPClassifier
from sklearn.preprocessing import StandardScaler
from sklearn.pipeline import Pipeline
# endregion


class TemporalCNNPrediction(QCAlgorithm):
    """
    Temporal CNN for Price Direction Prediction - v2 (Real MLPClassifier).

    This strategy replaces the fake hardcoded-kernel CNN with a real trained
    MLPClassifier that mimics temporal convolutional pattern recognition.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 14

    Key improvements vs v1 (fake CNN, SPY only, Sharpe 0.169):
    - Real sklearn MLPClassifier(128, 64, 32) trained on historical data
    - 3-class prediction: UP (>0.5%), DOWN (<-0.5%), NEUTRAL
    - 8 diversified ETFs: SPY, QQQ, IWM, XLK, XLF, XLV, DIA, EFA
    - Temporal features at multiple scales (5, 10, 20 days) mimicking CNN kernels
    - Monthly retraining on 252-day rolling window
    - Biweekly rebalancing (every 10 days) to reduce transaction costs
    - Only trade UP predictions with probability > 0.40
    - min_positions=2 to avoid cash drag

    Feature engineering (CNN-inspired temporal patterns, 18 features):
    - Multi-scale returns and volatility (5d, 10d, 20d windows)
    - Trend consistency: higher-high count, up-day fraction, sign-change rate
    - Cumulative returns (momentum) at 3 scales
    - Vol ratio (short/long): regime indicator
    - Autocorrelation lag-1: mean-reversion vs momentum detection
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 1, 1)
        self.set_cash(100_000)

        # Universe: 8 diversified ETFs
        self._tickers = ["SPY", "QQQ", "IWM", "XLK", "XLF", "XLV", "DIA", "EFA"]
        self._symbols = []
        for ticker in self._tickers:
            sym = self.add_equity(ticker, Resolution.DAILY).symbol
            self._symbols.append(sym)

        # Parameters
        self._lookback = 20          # Feature window (mimics CNN receptive field)
        self._train_window = 252     # Training data: 1 year
        self._up_threshold = 0.005   # +0.5% over horizon = UP class
        self._down_threshold = -0.005  # -0.5% over horizon = DOWN class
        self._pred_threshold = 0.40  # Minimum UP probability to take a position
        self._min_positions = 2      # Always hold at least 2 to avoid cash drag
        self._horizon = 10           # Predict 10-day forward return
        self._rebalance_freq = 10    # Biweekly rebalancing (trading days)

        # State per symbol: store raw close prices
        buf_size = self._train_window + self._horizon + self._lookback + 20
        self._price_history = {sym: deque(maxlen=buf_size) for sym in self._symbols}

        # ML models per symbol (one MLP per ETF)
        self._models = {sym: None for sym in self._symbols}
        self._models_trained = {sym: False for sym in self._symbols}
        self._last_train_month = -1
        self._days_since_rebalance = 0

        # Warmup: load initial price history per symbol (individual calls avoid TradeBars issue)
        warmup_days = buf_size + 100
        for sym in self._symbols:
            bars = self.history[TradeBar](sym, timedelta(days=warmup_days), Resolution.DAILY)
            for bar in bars:
                self._price_history[sym].append(bar.close)

        self.log(f"TemporalCNN v2 initialized. Universe: {self._tickers}")
        self.log(f"Features: 18 multi-scale temporal (5/10/20d). MLPClassifier(128,64,32)")
        self.log(f"Period: 2015-2026, horizon={self._horizon}d, retrain=monthly, rebal={self._rebalance_freq}d")

        # Schedule
        self.schedule.on(
            self.date_rules.every_day(self._symbols[0]),
            self.time_rules.after_market_open(self._symbols[0], 30),
            self._daily_update
        )

    def on_data(self, data):
        """Collect price data each bar."""
        for sym in self._symbols:
            if data.bars.contains_key(sym):
                self._price_history[sym].append(data.bars[sym].close)

    def _compute_features(self, prices):
        """
        Compute 18 temporal features that mimic CNN pattern detection at 3 scales.

        CNN analogy:
        - 5-day kernel: captures recent micro-patterns (lag returns, micro-vol)
        - 10-day kernel: swing / medium-term patterns
        - 20-day kernel: trend regime (long-term direction)

        Returns numpy array of 18 features, or None if insufficient data.
        """
        if len(prices) < self._lookback + 1:
            return None

        p = np.array(prices[-(self._lookback + 1):])
        rets = np.diff(p) / p[:-1]  # daily returns, length = lookback = 20

        # Safety check
        if len(rets) < 20:
            return None

        r = rets  # 20 daily returns

        features = []

        # -- Scale 1: short (5d) --
        r5 = r[-5:]
        features.append(float(np.mean(r5)))           # mean return 5d
        features.append(float(np.std(r5) + 1e-8))     # volatility 5d
        features.append(float(r[-1]))                  # lag-1 return
        features.append(float(r[-2]))                  # lag-2 return
        features.append(float(r[-3]))                  # lag-3 return
        # Trend direction consistency (5d): fraction of higher returns
        hh_count = sum(1 for i in range(1, len(r5)) if r5[i] > r5[i-1])
        features.append(float(hh_count) / max(len(r5) - 1, 1))

        # -- Scale 2: medium (10d) --
        r10 = r[-10:]
        features.append(float(np.mean(r10)))           # mean return 10d
        features.append(float(np.std(r10) + 1e-8))    # volatility 10d
        features.append(float(np.sum(r10 > 0)) / len(r10))  # up-day fraction 10d
        # Noise: sign changes per period
        sign_changes = sum(1 for i in range(1, len(r10))
                           if np.sign(r10[i]) != np.sign(r10[i-1]))
        features.append(float(sign_changes) / max(len(r10) - 1, 1))

        # -- Scale 3: long (20d) --
        r20 = r[-20:]
        features.append(float(np.mean(r20)))           # mean return 20d
        features.append(float(np.std(r20) + 1e-8))    # volatility 20d
        features.append(float(np.sum(r20 > 0)) / len(r20))  # up-day fraction 20d

        # Cumulative momentum at 3 scales
        cum5 = float(np.prod(1 + r[-5:]) - 1)
        cum10 = float(np.prod(1 + r[-10:]) - 1)
        cum20 = float(np.prod(1 + r[-20:]) - 1)
        features.append(cum5)
        features.append(cum10)
        features.append(cum20)

        # Vol regime: short/long vol ratio (expansion = trending, compression = ranging)
        vol_ratio = (np.std(r5) + 1e-8) / (np.std(r20) + 1e-8)
        features.append(float(vol_ratio))

        # Autocorrelation lag-1 (mean reversion < 0, momentum > 0)
        if len(r20) > 2:
            autocorr = float(np.corrcoef(r20[:-1], r20[1:])[0, 1])
            features.append(0.0 if np.isnan(autocorr) else autocorr)
        else:
            features.append(0.0)

        return np.array(features, dtype=float)

    def _build_training_data(self, sym):
        """
        Build (X, y) training dataset from price history.

        Target: 3-class label based on forward horizon return.
        - 2 = UP (> +0.5% over 10 days)
        - 0 = DOWN (< -0.5% over 10 days)
        - 1 = NEUTRAL
        """
        prices = list(self._price_history[sym])
        min_needed = self._train_window + self._horizon + self._lookback + 2
        if len(prices) < min_needed:
            return None, None

        # Use most recent slice
        prices = prices[-min_needed:]

        X, y = [], []
        for i in range(self._lookback + 1, len(prices) - self._horizon):
            window = prices[i - self._lookback - 1: i + 1]
            features = self._compute_features(window)
            if features is None:
                continue

            # Forward return: price at i+horizon vs price at i
            fwd_return = prices[i + self._horizon - 1] / prices[i] - 1

            if fwd_return > self._up_threshold:
                label = 2
            elif fwd_return < self._down_threshold:
                label = 0
            else:
                label = 1

            X.append(features)
            y.append(label)

        if len(X) < 30:
            return None, None

        return np.array(X, dtype=float), np.array(y, dtype=int)

    def _train_models(self):
        """Train one MLPClassifier per symbol on rolling 252-day window."""
        self.log(f"Training models ({self.time.date()})...")
        trained_count = 0

        for sym in self._symbols:
            X, y = self._build_training_data(sym)
            if X is None:
                continue

            # Need at least 2 classes
            unique_classes = np.unique(y)
            if len(unique_classes) < 2:
                continue

            try:
                model = Pipeline([
                    ('scaler', StandardScaler()),
                    ('clf', MLPClassifier(
                        hidden_layer_sizes=(128, 64, 32),
                        activation='relu',
                        solver='adam',
                        max_iter=300,
                        random_state=42,
                        early_stopping=True,
                        validation_fraction=0.1,
                        n_iter_no_change=15,
                        tol=1e-4
                    ))
                ])
                model.fit(X, y)
                self._models[sym] = model
                self._models_trained[sym] = True
                trained_count += 1
            except Exception as e:
                self.log(f"Training error {sym.value}: {e}")

        self.log(f"Trained {trained_count}/{len(self._symbols)} models")

    def _get_up_probability(self, sym):
        """
        Get probability that symbol will go UP over next horizon days.
        Returns (prob_up, is_trained).
        """
        if not self._models_trained.get(sym, False):
            return 0.0, False

        prices = list(self._price_history[sym])
        if len(prices) < self._lookback + 2:
            return 0.0, False

        window = prices[-(self._lookback + 2):]
        features = self._compute_features(window)
        if features is None:
            return 0.0, False

        try:
            proba = self._models[sym].predict_proba(features.reshape(1, -1))[0]
            classes = self._models[sym].named_steps['clf'].classes_
            up_idx = np.where(classes == 2)[0]
            prob_up = float(proba[up_idx[0]]) if len(up_idx) > 0 else 0.0
            return prob_up, True
        except Exception as e:
            self.log(f"Prediction error {sym.value}: {e}")
            return 0.0, False

    def _daily_update(self):
        """Daily handler: retrain monthly, rebalance biweekly."""
        current_month = self.time.month

        # Monthly retraining: first day of new month
        if current_month != self._last_train_month:
            price_ready = all(
                len(self._price_history[s]) >= self._train_window + self._horizon + self._lookback + 2
                for s in self._symbols
            )
            if price_ready:
                self._train_models()
                self._last_train_month = current_month

        # Biweekly rebalancing
        self._days_since_rebalance += 1
        if self._days_since_rebalance >= self._rebalance_freq:
            self._rebalance()
            self._days_since_rebalance = 0

    def _rebalance(self):
        """
        Allocate equal weight to ETFs predicted UP with prob > threshold.
        Always hold at least min_positions to avoid cash drag.
        """
        any_trained = any(self._models_trained.values())
        if not any_trained:
            return

        # Score all symbols
        scores = {}
        for sym in self._symbols:
            prob_up, is_trained = self._get_up_probability(sym)
            if is_trained:
                scores[sym] = prob_up

        if not scores:
            return

        # Primary filter: prob_up > threshold
        candidates = [(sym, prob) for sym, prob in scores.items()
                      if prob > self._pred_threshold]
        candidates.sort(key=lambda x: x[1], reverse=True)

        # Fallback: ensure minimum positions
        if len(candidates) < self._min_positions:
            all_sorted = sorted(scores.items(), key=lambda x: x[1], reverse=True)
            candidates = all_sorted[:self._min_positions]

        selected = [sym for sym, _ in candidates]
        weight = 1.0 / len(selected)

        # Log
        score_str = ", ".join(
            f"{sym.value}={scores.get(sym, 0):.3f}" for sym in selected[:4]
        )
        self.log(f"Rebal {self.time.date()}: {len(selected)} ETFs @ {weight:.1%} each | {score_str}")

        # Execute
        for sym in self._symbols:
            if sym in selected:
                self.set_holdings(sym, weight)
            else:
                self.liquidate(sym)

        # Plots
        best_prob = candidates[0][1] if candidates else 0.0
        self.plot('CNN', 'BestUpProb', best_prob)
        self.plot('CNN', 'NumPositions', float(len(selected)))

    def on_end_of_algorithm(self):
        final_value = self.portfolio.total_portfolio_value
        total_return = (final_value - 100_000) / 100_000
        trained = sum(1 for v in self._models_trained.values() if v)
        self.log(f"TemporalCNN v2: Final=${final_value:,.0f} | Return={total_return:.2%} | Models={trained}/{len(self._symbols)}")
