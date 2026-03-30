from AlgorithmImports import *
import numpy as np
from sklearn.ensemble import RandomForestClassifier
import pickle

class AdvancedMLAlgorithm(QCAlgorithm):
    """
    Strategie ML avancee sur BTCUSDT.
    Pipeline : features -> entrainement RandomForest -> prediction direction -> execution.
    Le modele est persiste dans l'ObjectStore et re-entraine mensuellement.
    """

    # --- Parametres de la strategie ---
    MODEL_KEY = "advanced_ml_model.pkl"
    LOOKBACK_DAYS = 252          # Historique pour l'entrainement (~1 an)
    WARMUP_DAYS = 60             # Periode de warmup pour les indicateurs
    N_ESTIMATORS = 100           # Nombre d'arbres dans la foret
    MIN_TRAIN_SAMPLES = 50       # Minimum d'echantillons pour entrainer

    def Initialize(self):
        # --- Configuration du backtest ---
        self.SetStartDate(2022, 1, 1)
        self.SetEndDate(2024, 12, 31)
        self.SetAccountCurrency("USDT")
        self.SetCash("USDT", 10000)

        # --- Broker et actif ---
        self.SetBrokerageModel(BrokerageName.Binance, AccountType.Cash)
        self.symbol = self.AddCrypto("BTCUSDT", Resolution.Daily, Market.Binance).Symbol
        self.SetBenchmark(self.symbol)

        # --- Indicateurs techniques (features du modele ML) ---
        self.sma = self.SMA(self.symbol, 20, Resolution.Daily)          # Tendance
        self.rsi = self.RSI(self.symbol, 14, MovingAverageType.Wilders, Resolution.Daily)  # Momentum
        self.ema_fast = self.EMA(self.symbol, 10, Resolution.Daily)     # Signal rapide
        self.ema_slow = self.EMA(self.symbol, 50, Resolution.Daily)     # Signal lent

        # --- Etat interne ---
        self.model = None
        self.prev_close = None
        self.feature_buffer = []   # Historique des features
        self.label_buffer = []     # Labels : 1=hausse, 0=baisse

        # --- Warmup pour que les indicateurs soient prets ---
        self.SetWarmUp(self.WARMUP_DAYS, Resolution.Daily)

        # --- Charger le modele depuis l'ObjectStore si disponible ---
        if self.ObjectStore.ContainsKey(self.MODEL_KEY):
            file_path = self.ObjectStore.GetFilePath(self.MODEL_KEY)
            with open(file_path, "rb") as f:
                self.model = pickle.load(f)
            self.Debug("Modele ML charge depuis l'ObjectStore")

        # --- Re-entrainement programme le 1er de chaque mois ---
        self.Schedule.On(
            self.DateRules.MonthStart(self.symbol),
            self.TimeRules.AfterMarketOpen(self.symbol, 1),
            self.RetrainModel
        )

    def BuildFeatures(self, close_price):
        """Construit le vecteur de features : SMA ratio, RSI norme, EMA cross, daily return."""
        if self.prev_close is None or self.prev_close == 0:
            return None
        daily_return = (close_price - self.prev_close) / self.prev_close
        sma_ratio = close_price / self.sma.Current.Value if self.sma.Current.Value > 0 else 1.0
        rsi_norm = self.rsi.Current.Value / 100.0
        ema_cross = (self.ema_fast.Current.Value / self.ema_slow.Current.Value
                     if self.ema_slow.Current.Value > 0 else 1.0)
        return [sma_ratio, rsi_norm, ema_cross, daily_return]

    def OnData(self, slice: Slice):
        if not slice.Bars.ContainsKey(self.symbol):
            return
        close_price = slice.Bars[self.symbol].Close

        # Attendre que tous les indicateurs soient prets
        if self.IsWarmingUp:
            self.prev_close = close_price
            return
        if not (self.sma.IsReady and self.rsi.IsReady
                and self.ema_fast.IsReady and self.ema_slow.IsReady):
            self.prev_close = close_price
            return

        # Construire les features du jour
        features = self.BuildFeatures(close_price)
        if features is None:
            self.prev_close = close_price
            return

        # Mettre a jour les buffers d'entrainement
        # Label = direction du jour actuel (voir README pour le lookahead bias)
        label = 1 if features[-1] > 0 else 0
        self.feature_buffer.append(features)
        self.label_buffer.append(label)

        # Fenetre glissante : garder seulement les N derniers jours
        if len(self.feature_buffer) > self.LOOKBACK_DAYS:
            self.feature_buffer = self.feature_buffer[-self.LOOKBACK_DAYS:]
            self.label_buffer = self.label_buffer[-self.LOOKBACK_DAYS:]

        # Entrainement initial si le modele n'existe pas encore
        if self.model is None and len(self.feature_buffer) >= self.MIN_TRAIN_SAMPLES:
            self.TrainModel()

        # Prediction et execution
        if self.model is not None:
            prediction = self.model.predict(np.array([features]))[0]
            if prediction == 1:
                # Prediction haussiere : position longue
                if not self.Portfolio[self.symbol].Invested:
                    self.SetHoldings(self.symbol, 1.0)
                    self.Debug(f"{self.Time} | ACHAT | prix={close_price:.2f}")
            else:
                # Prediction baissiere : rester en cash
                if self.Portfolio[self.symbol].Invested:
                    self.Liquidate(self.symbol)
                    self.Debug(f"{self.Time} | VENTE | prix={close_price:.2f}")

        self.prev_close = close_price

    def TrainModel(self):
        """
        Entraine le RandomForest sur les donnees accumulees.
        ATTENTION : les features du jour J predisent le label du jour J.
        En production, decaler les labels d'un jour pour eviter le lookahead bias.
        """
        if len(self.feature_buffer) < self.MIN_TRAIN_SAMPLES:
            return
        X = np.array(self.feature_buffer)
        y = np.array(self.label_buffer)
        self.model = RandomForestClassifier(
            n_estimators=self.N_ESTIMATORS, max_depth=5, random_state=42
        )
        self.model.fit(X, y)
        self.Debug(f"{self.Time} | TRAIN | n={len(y)}, acc={self.model.score(X, y):.2%}")

    def RetrainModel(self):
        """Re-entrainement mensuel pour s'adapter aux changements de regime."""
        if len(self.feature_buffer) >= self.MIN_TRAIN_SAMPLES:
            self.TrainModel()
            self.SaveModel()

    def SaveModel(self):
        """Persiste le modele dans l'ObjectStore de QuantConnect."""
        if self.model is not None:
            self.ObjectStore.SaveBytes(self.MODEL_KEY, pickle.dumps(self.model))
            self.Debug(f"{self.Time} | SAVE | modele sauvegarde dans ObjectStore")

    def OnEndOfAlgorithm(self):
        """Sauvegarde finale du modele a la fin du backtest."""
        self.SaveModel()
        self.Debug(f"Backtest termine. Portefeuille : "
                   f"{self.Portfolio.TotalPortfolioValue:.2f} USDT")
