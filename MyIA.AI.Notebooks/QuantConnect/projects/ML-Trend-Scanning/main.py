#region imports
from AlgorithmImports import *
import numpy as np
import pandas as pd
from sklearn.ensemble import RandomForestClassifier
from sklearn.preprocessing import StandardScaler
#endregion
# Hands-On AI Trading - Ex01: ML Trend Scanning
# Uses t-statistic of linear regression slope across multiple windows to classify trend regime.
# Inspired by MLFinlab trend-scanning algorithm, adapted for QuantConnect.
# Source: HandsOnAITradingBook, Section 06, Example 01


class MLTrendScanning(QCAlgorithm):

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.tlt = self.add_equity("TLT", Resolution.DAILY).symbol
        self.gld = self.add_equity("GLD", Resolution.DAILY).symbol
        self.set_benchmark(self.spy)

        # Trend scanning parameters
        self.scan_windows = [5, 10, 21, 42, 63]
        self.lookback = 252
        self.t_stat_threshold = float(self.get_parameter("t_stat_threshold") or 2.0)

        # ML overlay
        self.model = RandomForestClassifier(
            n_estimators=100, max_depth=5, random_state=42
        )
        self.scaler = StandardScaler()
        self.trained = False
        self.min_training = 252

        # Position sizing
        self.max_leverage = float(self.get_parameter("max_leverage") or 1.0)

        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance
        )

        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 60),
            self.train_ml
        )

        self.set_warm_up(252)

    def _trend_scanning(self, closes):
        """Compute t-statistics for linear regression slope across multiple windows.

        For each window length, fit a linear regression of price vs time
        and return the t-statistic of the slope coefficient.
        """
        n = len(closes)
        results = {}

        for w in self.scan_windows:
            if n < w:
                continue

            y = closes[-w:]
            x = np.arange(w, dtype=float)

            x_mean = np.mean(x)
            y_mean = np.mean(y)

            ss_xx = np.sum((x - x_mean) ** 2)
            if ss_xx == 0:
                continue

            slope = np.sum((x - x_mean) * (y - y_mean)) / ss_xx
            residuals = y - (y_mean + slope * (x - x_mean))
            se = np.sqrt(np.sum(residuals ** 2) / max(1, w - 2)) / np.sqrt(ss_xx)

            if se > 0:
                t_stat = slope / se
            else:
                t_stat = 0.0

            results[w] = float(t_stat)

        return results

    def _get_trend_signal(self, closes):
        """Aggregate trend scanning results into a signal.

        Returns:
            float: Signal between -1 (strong downtrend) and +1 (strong uptrend)
        """
        t_stats = self._trend_scanning(closes)
        if not t_stats:
            return 0.0

        values = list(t_stats.values())

        bullish_count = sum(1 for t in values if t > self.t_stat_threshold)
        bearish_count = sum(1 for t in values if t < -self.t_stat_threshold)
        total = len(values)

        if total == 0:
            return 0.0

        avg_t = np.mean(values)

        # Weighted signal: combine proportion of bullish windows with average t-stat
        signal = 0.6 * (bullish_count - bearish_count) / total + 0.4 * np.clip(avg_t / 5.0, -1, 1)

        return float(np.clip(signal, -1, 1))

    def _get_features(self, closes):
        """Extract features for ML from price series."""
        if len(closes) < 63:
            return None

        returns = np.diff(closes) / closes[:-1]

        # Momentum features
        mom_5 = closes[-1] / closes[-6] - 1 if len(closes) >= 6 else 0
        mom_10 = closes[-1] / closes[-11] - 1 if len(closes) >= 11 else 0
        mom_21 = closes[-1] / closes[-22] - 1 if len(closes) >= 22 else 0
        mom_63 = closes[-1] / closes[-64] - 1 if len(closes) >= 64 else 0

        # Volatility features
        vol_5 = np.std(returns[-5:]) * np.sqrt(252) if len(returns) >= 5 else 0
        vol_21 = np.std(returns[-21:]) * np.sqrt(252) if len(returns) >= 21 else 0
        vol_63 = np.std(returns[-63:]) * np.sqrt(252) if len(returns) >= 63 else 0

        # Moving average distances
        sma_21 = np.mean(closes[-21:])
        sma_63 = np.mean(closes[-63:])
        price = closes[-1]

        dist_sma21 = price / sma_21 - 1 if sma_21 > 0 else 0
        dist_sma63 = price / sma_63 - 1 if sma_63 > 0 else 0

        # Trend scanning features
        t_stats = self._trend_scanning(closes)
        t_stat_values = [t_stats.get(w, 0.0) for w in self.scan_windows]

        features = [
            mom_5, mom_10, mom_21, mom_63,
            vol_5, vol_21, vol_63,
            dist_sma21, dist_sma63,
        ] + t_stat_values

        return features

    def train_ml(self):
        if self.is_warming_up:
            return

        spy_hist = self.history([self.spy], 800, Resolution.DAILY)
        if spy_hist.empty:
            return

        try:
            closes = spy_hist.loc[self.spy]["close"].values
        except Exception:
            return

        if len(closes) < self.min_training + 21:
            return

        X, y = [], []
        for i in range(63, len(closes) - 21):
            features = self._get_features(closes[:i])
            if features is None:
                continue

            future_ret = closes[i + 21] / closes[i] - 1
            label = 1 if future_ret > 0.02 else (0 if future_ret > -0.02 else -1)

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

    def _ml_prediction(self, closes):
        """Get ML prediction for direction."""
        if not self.trained:
            return 0, 0.5

        features = self._get_features(closes)
        if features is None:
            return 0, 0.5

        X = self.scaler.transform([features])
        pred = int(self.model.predict(X)[0])

        proba = self.model.predict_proba(X)[0]
        classes = list(self.model.classes_)

        if pred == 1:
            conf = float(proba[classes.index(1)]) if 1 in classes else 0.5
        elif pred == -1:
            conf = float(proba[classes.index(-1)]) if -1 in classes else 0.5
        else:
            conf = float(proba[classes.index(0)]) if 0 in classes else 0.5

        return pred, conf

    def rebalance(self):
        if self.is_warming_up:
            return

        spy_hist = self.history([self.spy], self.lookback, Resolution.DAILY)
        if spy_hist.empty:
            return

        try:
            closes = spy_hist.loc[self.spy]["close"].values
        except Exception:
            return

        if len(closes) < 63:
            return

        # Trend scanning signal
        trend_signal = self._get_trend_signal(closes)

        # ML prediction
        ml_pred, ml_conf = self._ml_prediction(closes)

        # Combined signal
        combined = 0.5 * trend_signal + 0.5 * (ml_pred * ml_conf)

        # Allocation based on combined signal
        max_lev = self.max_leverage

        if combined > 0.5:
            # Strong uptrend: overweight equity
            equity_w = min(max_lev * 0.8, max_lev * combined)
            bond_w = max_lev - equity_w - 0.1
            gold_w = 0.1
            self.set_holdings(self.spy, equity_w)
            self.set_holdings(self.tlt, max(0, bond_w))
            self.set_holdings(self.gld, gold_w)

        elif combined > 0.0:
            # Moderate uptrend
            equity_w = max_lev * 0.5
            bond_w = max_lev * 0.3
            gold_w = max_lev * 0.1
            self.set_holdings(self.spy, equity_w)
            self.set_holdings(self.tlt, bond_w)
            self.set_holdings(self.gld, gold_w)

        elif combined > -0.5:
            # Moderate downtrend: defensive
            equity_w = max_lev * 0.3
            bond_w = max_lev * 0.4
            gold_w = max_lev * 0.2
            self.set_holdings(self.spy, equity_w)
            self.set_holdings(self.tlt, bond_w)
            self.set_holdings(self.gld, gold_w)

        else:
            # Strong downtrend: very defensive
            equity_w = max_lev * 0.1
            bond_w = max_lev * 0.5
            gold_w = max_lev * 0.3
            self.set_holdings(self.spy, equity_w)
            self.set_holdings(self.tlt, bond_w)
            self.set_holdings(self.gld, gold_w)

    def on_data(self, data):
        pass
