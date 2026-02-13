from AlgorithmImports import *
import numpy as np
try:
    import joblib
except ImportError:
    joblib = None
from sklearn.ensemble import RandomForestClassifier

class MyEnhancedCryptoMlAlgorithm(QCAlgorithm):
    MODEL_KEY       = "myCryptoMlModel.pkl"
    START_DATE      = datetime(2023, 1, 1)
    END_DATE        = datetime(2024, 1, 1)
    STARTING_CASH   = 100000
    SMA_PERIOD      = 20
    RSI_PERIOD      = 14
    EMA_PERIODS     = [10, 20, 50, 200]
    ADX_PERIOD      = 14
    ATR_PERIOD      = 14

    def Initialize(self):
        self.SetStartDate(self.START_DATE.year, self.START_DATE.month, self.START_DATE.day)
        self.SetEndDate(self.END_DATE.year, self.END_DATE.month, self.END_DATE.day)
        self.SetAccountCurrency("USDT")
        self.SetCash("USDT", self.STARTING_CASH)
        self.SetBrokerageModel(BrokerageName.Binance, AccountType.Cash)
        self.symbol = self.AddCrypto("BTCUSDT", Resolution.Daily, Market.Binance).Symbol
        self.Securities[self.symbol].SetDataNormalizationMode(DataNormalizationMode.Raw)
        self.SetBenchmark(self.symbol)
        self.model = None
        if joblib and self.ObjectStore.ContainsKey(self.MODEL_KEY):
            file_path = self.ObjectStore.GetFilePath(self.MODEL_KEY)
            self.model = joblib.load(file_path)
            self.Debug(f"Modele charge depuis l'Object Store: {self.MODEL_KEY}")
        else:
            self.Debug(f"Cle {self.MODEL_KEY} introuvable. Entrainement in-situ au demarrage.")
            self.train_model_scheduled = True
        self.sma  = self.SMA(self.symbol, self.SMA_PERIOD, Resolution.Daily)
        self.rsi = self.RSI(self.symbol, self.RSI_PERIOD, MovingAverageType.Wilders, Resolution.Daily)
        self.ema_dict = {}
        for period in self.EMA_PERIODS:
            self.ema_dict[period] = self.EMA(self.symbol, period, Resolution.Daily)
        self.adx = self.ADX(self.symbol, self.ADX_PERIOD, Resolution.Daily)
        self.atr = self.ATR(self.symbol, self.ATR_PERIOD, MovingAverageType.Simple, Resolution.Daily)
        self.prev_close = None
        warmup_bars = max(self.EMA_PERIODS) + self.ADX_PERIOD
        self.SetWarmUp(warmup_bars, Resolution.Daily)

    def _train_model_insitu(self):
        """Entrainement in-situ d'un RandomForest sur les 365 derniers jours d'historique."""
        training_days = 365
        history = self.History(self.symbol, training_days, Resolution.Daily)
        if history.empty or len(history) < 60:
            self.Debug("Pas assez d'historique pour l'entrainement. Utilisation du mode EMA fallback.")
            return False
        closes = history['close'].values
        highs = history['high'].values
        lows = history['low'].values
        # Construction des features a partir de l'historique
        X_list, y_list = [], []
        for i in range(max(self.EMA_PERIODS) + 1, len(closes) - 1):
            daily_ret = (closes[i] - closes[i-1]) / closes[i-1] if closes[i-1] > 0 else 0
            sma_20 = np.mean(closes[i-self.SMA_PERIOD:i])
            rsi_14 = self._compute_rsi(closes[i-self.RSI_PERIOD:i+1])
            ema_10 = self._ema(closes[:i+1], 10)
            ema_20 = self._ema(closes[:i+1], 20)
            ema_50 = self._ema(closes[:i+1], 50)
            ema_200 = self._ema(closes[:i+1], 200)
            # ADX simplifie
            adx_val = self._compute_adx(highs[i-self.ADX_PERIOD:i+1], lows[i-self.ADX_PERIOD:i+1], closes[i-self.ADX_PERIOD:i+1])
            # ATR simplifie
            atr_val = np.mean([highs[j] - lows[j] for j in range(max(0, i-self.ATR_PERIOD), i)])
            features = [sma_20, rsi_14, daily_ret, ema_10, ema_20, ema_50, ema_200, adx_val, atr_val]
            # Label : le prix monte le lendemain ?
            label = 1 if closes[i+1] > closes[i] else 0
            X_list.append(features)
            y_list.append(label)
        if len(X_list) < 30:
            return False
        X_train = np.array(X_list)
        y_train = np.array(y_list)
        self.model = RandomForestClassifier(n_estimators=100, max_depth=5, random_state=42)
        self.model.fit(X_train, y_train)
        accuracy = self.model.score(X_train, y_train)
        self.Debug(f"Modele RandomForest entraine in-situ : {len(X_train)} samples, accuracy={accuracy:.2%}")
        return True

    def _ema(self, data, period):
        if len(data) < period:
            return np.mean(data)
        multiplier = 2.0 / (period + 1)
        ema = np.mean(data[:period])
        for val in data[period:]:
            ema = (val - ema) * multiplier + ema
        return ema

    def _compute_rsi(self, prices):
        if len(prices) < 2:
            return 50.0
        deltas = np.diff(prices)
        gains = np.where(deltas > 0, deltas, 0)
        losses = np.where(deltas < 0, -deltas, 0)
        avg_gain = np.mean(gains) if len(gains) > 0 else 0
        avg_loss = np.mean(losses) if len(losses) > 0 else 1e-10
        rs = avg_gain / max(avg_loss, 1e-10)
        return 100 - (100 / (1 + rs))

    def _compute_adx(self, highs, lows, closes):
        if len(highs) < 3:
            return 25.0
        tr = [max(highs[i] - lows[i], abs(highs[i] - closes[i-1]), abs(lows[i] - closes[i-1]))
              for i in range(1, len(highs))]
        return np.mean(tr) if tr else 25.0

    def OnData(self, slice: Slice):
        if not slice.Bars.ContainsKey(self.symbol):
            return
        bar = slice.Bars[self.symbol]
        current_price = bar.Close
        if self.IsWarmingUp:
            return
        if not self.sma.IsReady or not self.rsi.IsReady or not self.adx.IsReady or not self.atr.IsReady:
            return
        for period in self.EMA_PERIODS:
            if not self.ema_dict[period].IsReady:
                return
        # Entrainement in-situ si necessaire
        if self.model is None and getattr(self, 'train_model_scheduled', False):
            self.train_model_scheduled = False
            if not self._train_model_insitu():
                self.Debug("Entrainement echoue. Arret.")
                self.Quit("Impossible d'entrainer le modele.")
                return
        if self.model is None:
            return
        if self.prev_close is None:
            self.prev_close = current_price
            return
        daily_return = (current_price - self.prev_close) / self.prev_close
        self.prev_close = current_price
        sma_val = self.sma.Current.Value
        rsi_val = self.rsi.Current.Value
        ema_10  = self.ema_dict[10].Current.Value
        ema_20  = self.ema_dict[20].Current.Value
        ema_50  = self.ema_dict[50].Current.Value
        ema_200 = self.ema_dict[200].Current.Value
        adx_val = self.adx.Current.Value
        atr_val = self.atr.Current.Value
        X = np.array([[sma_val, rsi_val, daily_return, ema_10, ema_20, ema_50, ema_200, adx_val, atr_val]])
        pred = self.model.predict(X)[0]
        if pred == 1:
            if not self.Portfolio[self.symbol].Invested:
                self.SetHoldings(self.symbol, 1.0)
                self.Debug(f"{self.Time} => Pred=UP => Achat BTCUSDT @ {current_price:.2f}")
        else:
            if self.Portfolio[self.symbol].Invested:
                self.Liquidate(self.symbol)
                self.Debug(f"{self.Time} => Pred=DOWN => Liquidation BTCUSDT @ {current_price:.2f}")
