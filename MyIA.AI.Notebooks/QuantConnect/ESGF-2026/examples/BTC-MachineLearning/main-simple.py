from AlgorithmImports import *
import joblib
import numpy as np

class MyCryptoMlAlgorithm(QCAlgorithm):

    def Initialize(self):
        self.SetStartDate(2022, 1, 1)
        self.SetEndDate(2023, 1, 1)
        self.SetAccountCurrency("USDT")
        self.SetCash("USDT", 100000)
        self.SetBrokerageModel(BrokerageName.Binance, AccountType.Cash)
        self.symbol = self.AddCrypto("BTCUSDT", Resolution.Daily, Market.Binance).Symbol
        self.Securities[self.symbol].SetDataNormalizationMode(DataNormalizationMode.Raw)
        self.SetBenchmark(self.symbol)
        model_key = "myCryptoMlModel.pkl"
        if self.ObjectStore.ContainsKey(model_key):
            file_path = self.ObjectStore.GetFilePath(model_key)
            self.model = joblib.load(file_path)
            self.Debug(f"Modele charge depuis l'Object Store: {model_key}")
        else:
            self.Debug(f"Cle {model_key} introuvable dans l'Object Store.")
            self.Quit("Impossible de poursuivre, aucun modele n'a ete trouve.")
        self.rsi = self.RSI(self.symbol, 14, MovingAverageType.Wilders, Resolution.Daily)
        self.sma20 = self.SMA(self.symbol, 20, Resolution.Daily)
        self.prev_close = None

    def OnData(self, slice: Slice):
        if not slice.ContainsKey(self.symbol):
            return
        if not self.rsi.IsReady or not self.sma20.IsReady:
            return
        current_price = slice[self.symbol].Close
        if self.prev_close is None:
            self.prev_close = current_price
            return
        daily_return = (current_price - self.prev_close) / self.prev_close
        self.prev_close = current_price
        X = np.array([[self.sma20.Current.Value, self.rsi.Current.Value, daily_return]])
        prediction = self.model.predict(X)[0]
        if prediction == 1:
            if not self.Portfolio[self.symbol].Invested:
                self.SetHoldings(self.symbol, 1.0)
                self.Debug(f"{self.Time}: Prediction=UP => Achat BTCUSDT (Close={current_price:.2f})")
        else:
            if self.Portfolio[self.symbol].Invested:
                self.Liquidate(self.symbol)
                self.Debug(f"{self.Time}: Prediction=DOWN => Liquidation BTCUSDT (Close={current_price:.2f})")
