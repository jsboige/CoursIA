#region imports
from AlgorithmImports import *
import numpy as np
from sklearn.ensemble import GradientBoostingRegressor
from sklearn.linear_model import Ridge
from sklearn.preprocessing import StandardScaler
from sklearn.pipeline import Pipeline
# endregion


class ChronosFoundationForecasting(QCAlgorithm):
    """
    Ensemble Time-Series Forecasting Strategy - v2 with Regime Filter.

    Replaces the fake Chronos model (hardcoded attention weights) with a
    real sklearn ensemble: GradientBoostingRegressor + Ridge regression.

    v2 improvements vs v1:
    - Regime filter: SMA200 on SPY. When SPY < SMA200 (bear regime),
      reduce risk exposure (max 2 positions from defensive assets).
    - Minimum prediction threshold: 0.002 (0.2% over 10 days) to filter
      noise predictions and reduce false positives.
    - Defensive set: GLD + IEF allowed in bear regime.
    - This reduces MaxDD while preserving the ML signal integrity.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 18

    Features per asset (21 total):
    - Lag returns: 1, 2, 3, 5, 10, 20 days
    - Rolling volatility: 5, 10, 20 days
    - Rolling mean returns: 5, 10, 20 days
    - Price vs SMA: 20, 50 days
    - Cross-asset: SPY return as market feature (1, 5, 20 days)

    Target: 10-day forward return (regression)
    Portfolio: Long top 4 assets with positive predicted return
    Regime: Bull -> 4 positions / Bear -> max 2 defensive positions
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 1, 1)
        self.set_cash(100_000)

        # Diversified ETF universe
        self._tickers = ["SPY", "QQQ", "IWM", "EFA", "TLT", "GLD", "IEF", "VNQ"]
        self._defensive_tickers = {"GLD", "IEF", "TLT"}  # allowed in bear regime
        self._symbols = {}
        for ticker in self._tickers:
            sym = self.add_equity(ticker, Resolution.DAILY).symbol
            self._symbols[ticker] = sym

        # Strategy parameters
        self._forecast_horizon = 10       # predict 10-day forward return
        self._training_window = 252       # 1 year of training data
        self._min_training_samples = 120  # min samples to train
        self._top_n = 4                   # hold top N assets in bull regime
        self._bear_top_n = 2              # max positions in bear regime
        self._total_alloc = 0.90          # 90% total allocation
        self._history_days = 300          # history to fetch
        self._min_pred_threshold = 0.002  # min 0.2% predicted 10-day return
        self._sma200_window = 200         # SMA for regime detection

        # Ensemble models (one per symbol)
        self._models = {}
        self._is_trained = {}
        self._last_train_month = -1

        for ticker in self._tickers:
            self._is_trained[ticker] = False

        # Warm-up period
        self.set_warm_up(self._history_days, Resolution.DAILY)

        # Schedule biweekly rebalance (Monday)
        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.after_market_open(self._symbols["SPY"], 30),
            self._rebalance
        )

        # Schedule monthly model training
        self.schedule.on(
            self.date_rules.month_start(self._symbols["SPY"]),
            self.time_rules.after_market_open(self._symbols["SPY"], 10),
            self._train_models
        )

        self.log("Ensemble Forecasting v2 initialized: 8-ETF, GBM+Ridge, SMA200 regime")

    def _is_bull_regime(self, spy_closes):
        """
        Regime detection: bull if SPY price > 200-day SMA.
        Returns True for bull, False for bear.
        """
        if len(spy_closes) < self._sma200_window:
            return True  # assume bull if insufficient data
        sma200 = np.mean(spy_closes[-self._sma200_window:])
        return spy_closes[-1] > sma200

    def _get_price_data(self):
        """Fetch price history for all symbols. Returns dict ticker->np.array."""
        prices = {}
        for ticker, sym in self._symbols.items():
            bars = self.history[TradeBar](sym, self._history_days, Resolution.DAILY)
            closes = np.array([bar.close for bar in bars])
            if len(closes) >= self._min_training_samples + self._forecast_horizon:
                prices[ticker] = closes
        return prices

    def _build_features(self, closes, spy_closes):
        """
        Build feature matrix and targets for training.

        Features (per row): 21 total
        - Lag returns: 1, 2, 3, 5, 10, 20
        - Rolling vol: 5, 10, 20
        - Rolling mean return: 5, 10, 20
        - Price/SMA20, price/SMA50
        - SPY lag returns: 1, 5, 20

        Target: 10-day forward log return
        """
        log_r = np.diff(np.log(closes))
        spy_log_r = np.diff(np.log(spy_closes))

        n = len(log_r)
        min_lookback = 51  # max lookback for SMA50 + 1
        start = min_lookback
        end = n - self._forecast_horizon

        if end <= start:
            return None, None

        rows = []
        targets = []

        for i in range(start, end):
            feat = self._make_feature_vector(log_r, spy_log_r, closes, i)
            rows.append(feat)

            # Target: sum of next forecast_horizon returns
            target = np.sum(log_r[i + 1:i + 1 + self._forecast_horizon])
            targets.append(target)

        if len(rows) < self._min_training_samples:
            return None, None

        return np.array(rows), np.array(targets)

    def _make_feature_vector(self, log_r, spy_log_r, closes, i):
        """Build a single feature vector at index i."""
        feat = []

        # Lag returns: 1, 2, 3, 5, 10, 20
        for lag in [1, 2, 3, 5, 10, 20]:
            if i - lag >= 0:
                feat.append(log_r[i - lag])
            else:
                feat.append(0.0)

        # Rolling vol: 5, 10, 20
        for w in [5, 10, 20]:
            window = log_r[max(0, i - w):i]
            feat.append(np.std(window) if len(window) > 1 else 0.0)

        # Rolling mean return: 5, 10, 20
        for w in [5, 10, 20]:
            window = log_r[max(0, i - w):i]
            feat.append(np.mean(window) if len(window) > 0 else 0.0)

        # Price/SMA: 20, 50 (use closes[i] as current price)
        for sma_w in [20, 50]:
            sma = np.mean(closes[max(0, i - sma_w + 1):i + 1])
            feat.append(closes[i] / sma - 1.0 if sma > 0 else 0.0)

        # SPY cross-asset: lag 1, 5, 20
        spy_i = min(i, len(spy_log_r) - 1)
        for lag in [1, 5, 20]:
            if spy_i - lag >= 0:
                feat.append(spy_log_r[spy_i - lag])
            else:
                feat.append(0.0)

        return feat

    def _build_current_features(self, closes, spy_closes):
        """Build feature vector for the most recent observation."""
        log_r = np.diff(np.log(closes))
        spy_log_r = np.diff(np.log(spy_closes))

        i = len(log_r) - 1  # most recent index
        if i < 50:
            return None

        feat = self._make_feature_vector(log_r, spy_log_r, closes, i)
        return np.array(feat).reshape(1, -1)

    def _train_models(self):
        """Train ensemble models monthly on 252-day window."""
        if self.is_warming_up:
            return

        current_month = self.time.month
        if current_month == self._last_train_month:
            return
        self._last_train_month = current_month

        prices = self._get_price_data()
        if "SPY" not in prices:
            self.log("Training skipped: SPY data not available")
            return

        spy_closes = prices["SPY"]
        trained_count = 0

        for ticker in self._tickers:
            if ticker not in prices:
                continue

            closes = prices[ticker]
            # Use only the last training_window bars
            if len(closes) > self._training_window:
                closes_train = closes[-self._training_window:]
                spy_train = spy_closes[-self._training_window:]
            else:
                closes_train = closes
                spy_train = spy_closes[:len(closes)]

            X, y = self._build_features(closes_train, spy_train)
            if X is None or len(X) < self._min_training_samples:
                continue

            try:
                # GradientBoosting pipeline
                gbm_pipe = Pipeline([
                    ("scaler", StandardScaler()),
                    ("gbm", GradientBoostingRegressor(
                        n_estimators=50,
                        max_depth=3,
                        learning_rate=0.05,
                        min_samples_leaf=5,
                        random_state=42
                    ))
                ])
                gbm_pipe.fit(X, y)

                # Ridge pipeline
                ridge_pipe = Pipeline([
                    ("scaler", StandardScaler()),
                    ("ridge", Ridge(alpha=10.0))
                ])
                ridge_pipe.fit(X, y)

                self._models[ticker] = (gbm_pipe, ridge_pipe)
                self._is_trained[ticker] = True
                trained_count += 1

            except Exception as e:
                self.log(f"Training error for {ticker}: {e}")
                self._is_trained[ticker] = False

        self.log(f"Models trained: {trained_count}/{len(self._tickers)} assets, "
                 f"date={self.time.date()}")

    def _predict(self, ticker, closes, spy_closes):
        """Generate ensemble prediction for one asset."""
        if ticker not in self._models or not self._is_trained[ticker]:
            return None

        feat = self._build_current_features(closes, spy_closes)
        if feat is None:
            return None

        try:
            gbm_pipe, ridge_pipe = self._models[ticker]
            gbm_pred = gbm_pipe.predict(feat)[0]
            ridge_pred = ridge_pipe.predict(feat)[0]

            # Weighted ensemble: 60% GBM + 40% Ridge
            return 0.60 * gbm_pred + 0.40 * ridge_pred

        except Exception as e:
            self.log(f"Prediction error for {ticker}: {e}")
            return None

    def _rebalance(self):
        """Biweekly rebalance with regime-aware portfolio construction."""
        if self.is_warming_up:
            return

        # Check if any model is trained
        any_trained = any(self._is_trained.values())
        if not any_trained:
            return

        prices = self._get_price_data()
        if "SPY" not in prices:
            return

        spy_closes = prices["SPY"]

        # Regime detection
        bull_regime = self._is_bull_regime(spy_closes)
        max_positions = self._top_n if bull_regime else self._bear_top_n

        # Generate predictions
        predictions = {}
        for ticker in self._tickers:
            if ticker not in prices:
                continue
            # In bear regime: only consider defensive assets
            if not bull_regime and ticker not in self._defensive_tickers:
                continue
            pred = self._predict(ticker, prices[ticker], spy_closes)
            if pred is not None:
                predictions[ticker] = pred

        # Rank by predicted return, apply minimum threshold
        ranked = sorted(predictions.items(), key=lambda x: x[1], reverse=True)
        top_picks = [
            (t, p) for t, p in ranked[:max_positions]
            if p > self._min_pred_threshold
        ]

        # Portfolio construction: equal weight among top picks
        current_holdings = set(
            t for t in self._tickers
            if self.portfolio[self._symbols[t]].invested
        )
        target_holdings = set(t for t, _ in top_picks)

        # Exit positions not in target
        for ticker in current_holdings - target_holdings:
            self.liquidate(self._symbols[ticker])

        # Enter/rebalance target positions
        if len(top_picks) > 0:
            weight = self._total_alloc / len(top_picks)
            for ticker, pred in top_picks:
                self.set_holdings(self._symbols[ticker], weight)

        # Log monthly
        if self.time.day <= 7:
            regime_str = "BULL" if bull_regime else "BEAR"
            pred_str = ", ".join([f"{t}:{p:.4f}" for t, p in ranked[:5]])
            self.log(
                f"Regime={regime_str} | Predictions: {pred_str} "
                f"| Holding: {[t for t, _ in top_picks]}"
            )

    def on_end_of_algorithm(self):
        final_value = self.portfolio.total_portfolio_value
        ret = (final_value - 100_000) / 100_000
        trained = sum(1 for v in self._is_trained.values() if v)
        self.log(
            f"Ensemble Forecasting v2: Final=${final_value:,.0f}, "
            f"Return={ret:.2%}, Models trained={trained}/{len(self._tickers)}"
        )
