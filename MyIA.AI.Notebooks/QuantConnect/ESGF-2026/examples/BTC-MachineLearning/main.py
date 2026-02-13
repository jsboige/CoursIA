from AlgorithmImports import *
import joblib
import numpy as np

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
        if self.ObjectStore.ContainsKey(self.MODEL_KEY):
            file_path = self.ObjectStore.GetFilePath(self.MODEL_KEY)
            self.model = joblib.load(file_path)
            self.Debug(f"Modele charge depuis l'Object Store: {self.MODEL_KEY}")
        else:
            self.Debug(f"Cle {self.MODEL_KEY} introuvable dans l'ObjectStore.")
            self.Quit("Aucun modele trouve. Arret de l'algorithme.")
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
