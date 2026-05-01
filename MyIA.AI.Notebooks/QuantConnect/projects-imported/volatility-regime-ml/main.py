#region imports
from AlgorithmImports import *
import numpy as np
from sklearn.ensemble import RandomForestClassifier
from sklearn.preprocessing import StandardScaler
from collections import deque
#endregion
# Volatility Regime ML
# Source: QC Strategy Library - Volatility Harvest ML
# Concept: VIX regime detection with RandomForest ML overlay for tactical allocation.
# Universe: SPY, TLT, GLD, BIL + VIX via CBOE custom data.
# ML features: VIX stats (z-score, percentile, SMA ratios) + SPY momentum/vol.
# 5 regime-based allocation states with ML bullish probability overlay (>0.6).
# Daily signal check, monthly model retraining.
# Imported from QC Cloud Project ID: 29687293


class VolatilityHarvestML(QCAlgorithm):

    def initialize(self):
        self.set_start_date(2008, 1, 1)
        self.set_cash(100000)

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.tlt = self.add_equity("TLT", Resolution.DAILY).symbol
        self.gld = self.add_equity("GLD", Resolution.DAILY).symbol
        self.bil = self.add_equity("BIL", Resolution.DAILY).symbol

        self.vix = self.add_data(CBOE, "VIX", Resolution.DAILY).symbol

        # ML components
        self.model = RandomForestClassifier(
            n_estimators=100, max_depth=5, random_state=42
        )
        self.scaler = StandardScaler()
        self.trained = False
        self.training_data = []
        self.min_training = 504  # 2 years

        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.check_signal
        )

        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 60),
            self.train_model
        )

        self.set_warm_up(252)

    def get_features(self, vix_closes, spy_closes):
        if len(vix_closes) < 50 or len(spy_closes) < 200:
            return None

        current_vix = vix_closes[-1]
        vix_sma20 = np.mean(vix_closes[-20:])
        vix_sma50 = np.mean(vix_closes[-50:])
        vix_std = np.std(vix_closes[-20:])
        vix_zscore = (current_vix - vix_sma20) / vix_std if vix_std > 0 else 0
        vix_percentile = np.sum(vix_closes < current_vix) / len(vix_closes)

        spy_current = spy_closes[-1]
        spy_sma50 = np.mean(spy_closes[-50:])
        spy_sma200 = np.mean(spy_closes[-200:])
        spy_5d_ret = spy_closes[-1] / spy_closes[-5] - 1
        spy_10d_ret = spy_closes[-1] / spy_closes[-10] - 1
        spy_20d_ret = spy_closes[-1] / spy_closes[-20] - 1
        spy_vol = np.std(np.diff(spy_closes[-21:]) / spy_closes[-21:-1])

        return [
            current_vix,
            vix_zscore,
            vix_percentile,
            current_vix / vix_sma20,
            current_vix / vix_sma50,
            spy_5d_ret,
            spy_10d_ret,
            spy_20d_ret,
            spy_current / spy_sma50,
            spy_current / spy_sma200,
            spy_vol * np.sqrt(252),
        ]

    def get_label(self, spy_closes, forward_days=21):
        if len(spy_closes) < forward_days + 1:
            return None
        future_ret = spy_closes[-1] / spy_closes[-forward_days - 1] - 1
        return 1 if future_ret > 0.02 else 0

    def train_model(self):
        if self.is_warming_up:
            return

        vix_hist = self.history([self.vix], 800, Resolution.DAILY)
        spy_hist = self.history([self.spy], 800, Resolution.DAILY)

        if vix_hist.empty or spy_hist.empty:
            return

        try:
            vix_closes = vix_hist.loc[self.vix]['close'].values
            spy_closes = spy_hist.loc[self.spy]['close'].values
        except Exception:
            return

        if len(vix_closes) < self.min_training or len(spy_closes) < self.min_training:
            return

        X, y = [], []
        for i in range(200, len(spy_closes) - 21):
            features = self.get_features(vix_closes[:i], spy_closes[:i])
            label = 1 if spy_closes[i + 21] / spy_closes[i] > 0.02 else 0
            if features:
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

    def check_signal(self):
        if self.is_warming_up:
            return

        vix_hist = self.history([self.vix], 100, Resolution.DAILY)
        spy_hist = self.history([self.spy], 200, Resolution.DAILY)

        if vix_hist.empty or spy_hist.empty:
            return

        try:
            vix_closes = vix_hist.loc[self.vix]['close'].values
            spy_closes = spy_hist.loc[self.spy]['close'].values
        except Exception:
            return

        if len(vix_closes) < 50 or len(spy_closes) < 200:
            return

        current_vix = vix_closes[-1]
        vix_sma = np.mean(vix_closes[-20:])
        vix_percentile = np.percentile(vix_closes, 80)

        spy_current = spy_closes[-1]
        spy_sma50 = np.mean(spy_closes[-50:])
        spy_sma200 = np.mean(spy_closes[-200:])
        spy_5d_ret = spy_closes[-1] / spy_closes[-5] - 1

        # ML boost
        ml_bullish = False
        if self.trained:
            features = self.get_features(vix_closes, spy_closes)
            if features:
                X = self.scaler.transform([features])
                prob_array = self.model.predict_proba(X)[0]
                if len(prob_array) == 2:
                    prob = prob_array[1]
                else:
                    prob = 0.5 if self.model.predict(X)[0] == 0 else 0.7
                ml_bullish = prob > 0.6

        # Regime logic with ML overlay
        # VIX spike + oversold = BUY
        if current_vix > vix_percentile and spy_5d_ret < -0.03:
            weight = 1.0 if ml_bullish else 0.85
            self.set_holdings(self.spy, weight)
            self.set_holdings(self.tlt, 0)
            self.set_holdings(self.gld, 1.0 - weight)
            self.set_holdings(self.bil, 0)
            return

        # VIX very low + extended = reduce risk
        if current_vix < 13 and spy_current > spy_sma50 * 1.05:
            self.set_holdings(self.spy, 0.40)
            self.set_holdings(self.tlt, 0.30)
            self.set_holdings(self.gld, 0.20)
            self.set_holdings(self.bil, 0.10)
            return

        # VIX elevated but falling = recovery
        if current_vix > 20 and current_vix < vix_sma:
            weight = 0.85 if ml_bullish else 0.70
            self.set_holdings(self.spy, weight)
            self.set_holdings(self.tlt, 0.10)
            self.set_holdings(self.gld, 1.0 - weight - 0.10)
            return

        # VIX rising = get defensive
        if current_vix > vix_sma * 1.2:
            self.set_holdings(self.spy, 0.30)
            self.set_holdings(self.tlt, 0.40)
            self.set_holdings(self.gld, 0.20)
            self.set_holdings(self.bil, 0.10)
            return

        # Default: trend following with ML tilt
        if spy_current > spy_sma200:
            base = 0.70 if ml_bullish else 0.60
            self.set_holdings(self.spy, base)
            self.set_holdings(self.tlt, 0.25)
            self.set_holdings(self.gld, 1.0 - base - 0.25)
        else:
            self.set_holdings(self.spy, 0.30)
            self.set_holdings(self.tlt, 0.40)
            self.set_holdings(self.gld, 0.20)
            self.set_holdings(self.bil, 0.10)

    def on_data(self, data):
        pass


class CBOE(PythonData):
    def get_source(self, config, date, is_live):
        return SubscriptionDataSource(
            "https://cdn.cboe.com/api/global/us_indices/daily_prices/VIX_History.csv",
            SubscriptionTransportMedium.REMOTE_FILE
        )

    def reader(self, config, line, date, is_live):
        if not (line.strip() and line[0].isdigit()):
            return None

        data = line.split(',')
        try:
            index = CBOE()
            index.symbol = config.symbol
            index.time = datetime.strptime(data[0], "%m/%d/%Y")
            index.value = float(data[4])
            index["close"] = float(data[4])
            index["open"] = float(data[1])
            index["high"] = float(data[2])
            index["low"] = float(data[3])
            return index
        except Exception:
            return None
