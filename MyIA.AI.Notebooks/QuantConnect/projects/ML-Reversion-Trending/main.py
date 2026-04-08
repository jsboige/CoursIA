#region imports
from AlgorithmImports import *
import numpy as np
import pandas as pd
from sklearn.ensemble import GradientBoostingClassifier
from sklearn.preprocessing import StandardScaler
#endregion
# Hands-On AI Trading - Ex03: Reversion vs Trending Classification
# Classifies market regime as mean-reverting or trending, then applies the
# appropriate strategy: mean-reversion (RSI + Bollinger) or trend-following (MA crossover).
# Source: HandsOnAITradingBook, Section 06, Example 03


class MLReversionTrendingClassifier(QCAlgorithm):

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # Tradeable universe
        self.symbols = {
            "SPY": self.add_equity("SPY", Resolution.DAILY).symbol,
            "TLT": self.add_equity("TLT", Resolution.DAILY).symbol,
            "GLD": self.add_equity("GLD", Resolution.DAILY).symbol,
            "IWM": self.add_equity("IWM", Resolution.DAILY).symbol,
            "EFA": self.add_equity("EFA", Resolution.DAILY).symbol,
        }
        self.set_benchmark(self.symbols["SPY"])

        # Regime classification parameters
        self.lookback = 126
        self.hurst_window = 100

        # ML model for regime classification
        self.model = GradientBoostingClassifier(
            n_estimators=100, max_depth=4, random_state=42
        )
        self.scaler = StandardScaler()
        self.trained = False
        self.min_training = 252

        # Strategy parameters
        self.rsi_period = int(self.get_parameter("rsi_period") or 14)
        self.bb_period = int(self.get_parameter("bb_period") or 20)
        self.bb_std = float(self.get_parameter("bb_std") or 2.0)
        self.ema_fast = int(self.get_parameter("ema_fast") or 12)
        self.ema_slow = int(self.get_parameter("ema_slow") or 26)

        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance
        )

        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 60),
            self.train_model
        )

        self.set_warm_up(252)

    def _compute_hurst(self, prices):
        """Simplified Hurst exponent via R/S analysis.

        H < 0.5: mean-reverting
        H = 0.5: random walk
        H > 0.5: trending
        """
        n = len(prices)
        if n < 20:
            return 0.5

        log_prices = np.log(np.array(prices, dtype=float))
        returns = np.diff(log_prices)
        max_k = min(n - 1, 50)

        rs_values = []
        ns = []

        k = 4
        while k < max_k:
            num_chunks = n // k
            if num_chunks < 1:
                break

            rs_chunk = []
            for i in range(num_chunks):
                chunk = returns[i * k:(i + 1) * k]
                if len(chunk) < 2:
                    continue
                mean_chunk = float(np.mean(chunk))
                cumdev = np.cumsum(chunk - mean_chunk)
                r = float(np.max(cumdev)) - float(np.min(cumdev))
                s = float(np.std(chunk, ddof=1))
                if s > 0:
                    rs_chunk.append(r / s)

            if rs_chunk:
                rs_values.append(np.mean(rs_chunk))
                ns.append(k)

            k = int(k * 1.5) + 1

        if len(ns) < 3:
            return 0.5

        log_ns = np.log(ns)
        log_rs = np.log(rs_values)

        try:
            slope = float(np.polyfit(log_ns, log_rs, 1)[0])
            return float(np.clip(slope, 0.0, 1.0))
        except Exception:
            return 0.5

    def _compute_regime_features(self, closes):
        """Extract features that characterize the market regime."""
        n = len(closes)
        if n < 63:
            return None

        closes_arr = np.array(closes, dtype=float)
        returns = np.diff(closes_arr) / closes_arr[:-1]

        hurst = self._compute_hurst(closes_arr[-self.hurst_window:])

        if len(returns) > 2:
            autocorr = float(np.corrcoef(returns[:-1], returns[1:])[0, 1])
        else:
            autocorr = 0.0

        if len(returns) > 10:
            var_1 = float(np.var(returns[-20:]))
            ret_5 = returns[-20:].reshape(-1, 5).sum(axis=1)
            var_5 = float(np.var(ret_5)) if len(ret_5) > 1 else var_1 * 5
            vr = var_5 / (5 * var_1) if var_1 > 0 else 1.0
        else:
            vr = 1.0

        mom_5 = float(closes_arr[-1]) / float(closes_arr[-6]) - 1 if n >= 6 else 0
        mom_21 = float(closes_arr[-1]) / float(closes_arr[-22]) - 1 if n >= 22 else 0

        vol_5 = float(np.std(returns[-5:])) if len(returns) >= 5 else 0.01
        vol_21 = float(np.std(returns[-21:])) if len(returns) >= 21 else 0.01
        vol_ratio = vol_5 / vol_21 if vol_21 > 0 else 1.0

        sma_21 = float(np.mean(closes_arr[-21:]))
        dist_from_sma = (float(closes_arr[-1]) - sma_21) / sma_21 if sma_21 > 0 else 0

        return [
            float(hurst),
            float(autocorr),
            float(vr),
            float(mom_5),
            float(mom_21),
            float(vol_ratio),
            float(dist_from_sma),
            float(vol_21 * np.sqrt(252)),
        ]

    def _get_label(self, closes, idx, forward=21):
        """Label regime based on future returns pattern.

        0 = mean-reverting (price returns to mean)
        1 = trending (price continues in one direction)
        """
        if idx + forward >= len(closes):
            return None

        future = closes[idx:idx + forward]
        if len(future) < forward:
            return None

        future_arr = np.array(future, dtype=float)
        returns = np.diff(future_arr) / future_arr[:-1]
        positive = int(np.sum(returns > 0))
        negative = int(np.sum(returns < 0))

        total_return = float(future_arr[-1]) / float(future_arr[0]) - 1

        max_up = float(np.max(future_arr)) / float(future_arr[0]) - 1
        max_down = float(future_arr[0]) / float(np.min(future_arr)) - 1

        if total_return > 0.03 and positive > len(returns) * 0.6:
            return 1
        elif total_return < -0.03 and negative > len(returns) * 0.6:
            return 1

        cum_returns = np.cumsum(returns)
        zero_crossings = int(np.sum(np.diff(np.sign(cum_returns)) != 0))

        if zero_crossings > forward * 0.3 or (max_up < 0.02 and max_down < 0.02):
            return 0

        return 0

    def train_model(self):
        if self.is_warming_up:
            return

        spy_hist = self.history([self.symbols["SPY"]], 800, Resolution.DAILY)
        if spy_hist.empty:
            return

        try:
            closes = spy_hist.loc[self.symbols["SPY"]]["close"].values
        except Exception:
            return

        if len(closes) < self.min_training + 21:
            return

        X, y = [], []
        for i in range(63, len(closes) - 21):
            features = self._compute_regime_features(closes[:i])
            label = self._get_label(closes, i, forward=21)

            if features is None or label is None:
                continue

            X.append(features)
            y.append(label)

        if len(X) < 100:
            return

        X = np.array(X)
        y = np.array(y)

        self.scaler.fit(X)
        X_scaled = self.scaler.transform(X)
        self.model.fit(X_scaled, y)
        self.trained = True

    def _mean_reversion_signals(self, symbol):
        """Generate mean-reversion signals using RSI and Bollinger Bands."""
        hist = self.history(symbol, 30, Resolution.DAILY)
        if hist.empty:
            return 0.0

        try:
            closes = hist.loc[symbol]["close"].values
        except Exception:
            return 0.0

        if len(closes) < self.bb_period:
            return 0.0

        deltas = np.diff(closes[-(self.rsi_period + 1):])
        gains = np.where(deltas > 0, deltas, 0)
        losses = np.where(deltas < 0, -deltas, 0)
        avg_gain = float(np.mean(gains))
        avg_loss = float(np.mean(losses))
        if avg_loss == 0:
            rsi = 100
        else:
            rs = avg_gain / avg_loss
            rsi = 100 - 100 / (1 + rs)

        sma = float(np.mean(closes[-self.bb_period:]))
        std = float(np.std(closes[-self.bb_period:]))
        bb_pos = (float(closes[-1]) - sma) / (self.bb_std * std) if std > 0 else 0

        signal = 0.0
        if rsi < 30 and bb_pos < -1.0:
            signal = 0.8
        elif rsi < 40 and bb_pos < -0.5:
            signal = 0.5
        elif rsi > 70 and bb_pos > 1.0:
            signal = -0.8
        elif rsi > 60 and bb_pos > 0.5:
            signal = -0.5

        return signal

    def _trend_following_signals(self, symbol):
        """Generate trend-following signals using EMA crossover."""
        hist = self.history(symbol, 50, Resolution.DAILY)
        if hist.empty:
            return 0.0

        try:
            closes = hist.loc[symbol]["close"].values
        except Exception:
            return 0.0

        if len(closes) < self.ema_slow:
            return 0.0

        def ema(data, period):
            multiplier = 2.0 / (period + 1)
            result = float(data[0])
            for price in data[1:]:
                result = (float(price) - result) * multiplier + result
            return result

        ema_fast = ema(closes, self.ema_fast)
        ema_slow = ema(closes, self.ema_slow)

        mom_5 = float(closes[-1]) / float(closes[-6]) - 1 if len(closes) >= 6 else 0

        trend = (ema_fast - ema_slow) / ema_slow if ema_slow > 0 else 0

        signal = 0.0
        if trend > 0.005 and mom_5 > 0:
            signal = min(0.8, trend * 20)
        elif trend < -0.005 and mom_5 < 0:
            signal = max(-0.8, trend * 20)

        return signal

    def rebalance(self):
        if self.is_warming_up:
            return

        spy_hist = self.history([self.symbols["SPY"]], self.lookback, Resolution.DAILY)
        if spy_hist.empty:
            return

        try:
            closes = spy_hist.loc[self.symbols["SPY"]]["close"].values
        except Exception:
            return

        if len(closes) < 63:
            return

        regime = 0
        confidence = 0.5

        if self.trained:
            features = self._compute_regime_features(closes)
            if features is not None:
                X = self.scaler.transform([features])
                pred = int(self.model.predict(X)[0])
                proba = self.model.predict_proba(X)[0]
                classes = list(self.model.classes_)
                confidence = float(proba[classes.index(pred)]) if pred in classes else 0.5
                regime = pred

        hurst = self._compute_hurst(closes[-self.hurst_window:])
        if not self.trained:
            regime = 1 if hurst > 0.55 else 0

        spy = self.symbols["SPY"]
        tlt = self.symbols["TLT"]
        gld = self.symbols["GLD"]

        if regime == 1:
            trend_sig = self._trend_following_signals(spy)

            if trend_sig > 0.3:
                spy_w = min(0.7, 0.5 + trend_sig * 0.2) * confidence
                tlt_w = 0.2
                gld_w = 1.0 - spy_w - tlt_w
            elif trend_sig < -0.3:
                spy_w = max(0.1, 0.3 + trend_sig * 0.2) * confidence
                tlt_w = 0.4
                gld_w = 1.0 - spy_w - tlt_w
            else:
                spy_w = 0.4
                tlt_w = 0.3
                gld_w = 0.3

        else:
            mr_sig = self._mean_reversion_signals(spy)

            if mr_sig > 0.3:
                spy_w = min(0.7, 0.5 + mr_sig * 0.3) * confidence
                tlt_w = 0.15
                gld_w = 1.0 - spy_w - tlt_w
            elif mr_sig < -0.3:
                spy_w = max(0.05, 0.3 + mr_sig * 0.2) * confidence
                tlt_w = 0.45
                gld_w = 1.0 - spy_w - tlt_w
            else:
                spy_w = 0.4
                tlt_w = 0.3
                gld_w = 0.3

        self.set_holdings(spy, spy_w)
        self.set_holdings(tlt, tlt_w)
        self.set_holdings(gld, gld_w)

    def on_data(self, data):
        pass
