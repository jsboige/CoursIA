#region imports
from AlgorithmImports import *
import numpy as np
from sklearn.ensemble import RandomForestClassifier
from sklearn.preprocessing import StandardScaler
from collections import deque
#endregion
# https://www.quantconnect.com/strategies/50
# Dynamic VIX-SPY Regime Strategy by Ahmet Kasti
# OOS 1Y Sharpe 1.72, 5Y CAGR 29.76%
# Uses RandomForestClassifier + StandardScaler for ML overlay on VIX regime switching
# Source: QC Strategy Library #50, cloned 2026-04-04, QC Project ID: 29687293

class VolatilityHarvestML(QCAlgorithm):

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.SetCash(100000)

        self.spy = self.AddEquity("SPY", Resolution.Daily).Symbol
        self.tlt = self.AddEquity("TLT", Resolution.Daily).Symbol
        self.gld = self.AddEquity("GLD", Resolution.Daily).Symbol
        self.bil = self.AddEquity("BIL", Resolution.Daily).Symbol

        self.vix = self.AddData(CBOE, "VIX", Resolution.Daily).Symbol

        # ML components
        self.model = RandomForestClassifier(n_estimators=100, max_depth=5, random_state=42)
        self.scaler = StandardScaler()
        self.trained = False
        self.training_data = []
        self.min_training = 504  # 2 years

        self.Schedule.On(
            self.DateRules.EveryDay("SPY"),
            self.TimeRules.AfterMarketOpen("SPY", 30),
            self.CheckSignal
        )

        self.Schedule.On(
            self.DateRules.MonthStart("SPY"),
            self.TimeRules.AfterMarketOpen("SPY", 60),
            self.TrainModel
        )

        self.SetWarmUp(252)

    def GetFeatures(self, vix_closes, spy_closes):
        """Extract features for ML"""
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

        features = [
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

        return features

    def GetLabel(self, spy_closes, forward_days=21):
        """Label: 1 if SPY up >2% in next month, 0 otherwise"""
        if len(spy_closes) < forward_days + 1:
            return None

        future_ret = spy_closes[-1] / spy_closes[-forward_days-1] - 1
        return 1 if future_ret > 0.02 else 0

    def TrainModel(self):
        if self.IsWarmingUp:
            return

        vix_hist = self.History([self.vix], 800, Resolution.Daily)
        spy_hist = self.History([self.spy], 800, Resolution.Daily)

        if vix_hist.empty or spy_hist.empty:
            return

        try:
            vix_closes = vix_hist.loc[self.vix]['close'].values
            spy_closes = spy_hist.loc[self.spy]['close'].values
        except:
            return

        if len(vix_closes) < self.min_training or len(spy_closes) < self.min_training:
            return

        # build training set
        X, y = [], []

        for i in range(200, len(spy_closes) - 21):
            features = self.GetFeatures(vix_closes[:i], spy_closes[:i])
            label = 1 if spy_closes[i+21] / spy_closes[i] > 1.02 else 0

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

    def CheckSignal(self):
        if self.IsWarmingUp:
            return

        vix_hist = self.History([self.vix], 100, Resolution.Daily)
        spy_hist = self.History([self.spy], 200, Resolution.Daily)

        if vix_hist.empty or spy_hist.empty:
            return

        try:
            vix_closes = vix_hist.loc[self.vix]['close'].values
            spy_closes = spy_hist.loc[self.spy]['close'].values
        except:
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

        # === ML BOOST ===
        ml_bullish = False
        if self.trained:
            features = self.GetFeatures(vix_closes, spy_closes)
            if features:
                X = self.scaler.transform([features])

                prob_array = self.model.predict_proba(X)[0]

                # Handle case where model only learned one class
                if len(prob_array) == 2:
                    prob = prob_array[1]  # Probability of class 1 (bullish)
                else:
                    # Only one class learned, use prediction directly
                    prob = 0.5 if self.model.predict(X)[0] == 0 else 0.7

                ml_bullish = prob > 0.6

        # === ORIGINAL LOGIC WITH ML OVERLAY ===

        # VIX spike + oversold = BUY (boosted by ML)
        if current_vix > vix_percentile and spy_5d_ret < -0.03:
            weight = 1.0 if ml_bullish else 0.85
            self.SetHoldings(self.spy, weight)
            self.SetHoldings(self.tlt, 0)
            self.SetHoldings(self.gld, 1.0 - weight)
            self.SetHoldings(self.bil, 0)
            return

        # VIX very low + extended = reduce risk
        if current_vix < 13 and spy_current > spy_sma50 * 1.05:
            self.SetHoldings(self.spy, 0.40)
            self.SetHoldings(self.tlt, 0.30)
            self.SetHoldings(self.gld, 0.20)
            self.SetHoldings(self.bil, 0.10)
            return

        # VIX elevated but falling = recovery
        if current_vix > 20 and current_vix < vix_sma:
            weight = 0.85 if ml_bullish else 0.70
            self.SetHoldings(self.spy, weight)
            self.SetHoldings(self.tlt, 0.10)
            self.SetHoldings(self.gld, 1.0 - weight - 0.10)
            return

        # VIX rising = get defensive
        if current_vix > vix_sma * 1.2:
            self.SetHoldings(self.spy, 0.30)
            self.SetHoldings(self.tlt, 0.40)
            self.SetHoldings(self.gld, 0.20)
            self.SetHoldings(self.bil, 0.10)
            return

        # Default: trend following with ML tilt
        if spy_current > spy_sma200:
            base = 0.60
            if ml_bullish:
                base = 0.70
            self.SetHoldings(self.spy, base)
            self.SetHoldings(self.tlt, 0.25)
            self.SetHoldings(self.gld, 1.0 - base - 0.25)
        else:
            self.SetHoldings(self.spy, 0.30)
            self.SetHoldings(self.tlt, 0.40)
            self.SetHoldings(self.gld, 0.20)
            self.SetHoldings(self.bil, 0.10)

    def OnData(self, data):
        pass


class CBOE(PythonData):
    def GetSource(self, config, date, isLive):
        return SubscriptionDataSource(
            f"https://cdn.cboe.com/api/global/us_indices/daily_prices/VIX_History.csv",
            SubscriptionTransportMedium.RemoteFile
        )

    def Reader(self, config, line, date, isLive):
        if not (line.strip() and line[0].isdigit()):
            return None

        data = line.split(',')

        try:
            index = CBOE()
            index.Symbol = config.Symbol
            index.Time = datetime.strptime(data[0], "%m/%d/%Y")
            index.Value = float(data[4])
            index["close"] = float(data[4])
            index["open"] = float(data[1])
            index["high"] = float(data[2])
            index["low"] = float(data[3])
            return index
        except:
            return None
