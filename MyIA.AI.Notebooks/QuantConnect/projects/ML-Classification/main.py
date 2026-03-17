#region imports
from AlgorithmImports import *
#endregion

import joblib
import json
import numpy as np
from io import BytesIO

class MLClassificationAlgorithm(QCAlgorithm):
    """
    Algorithme de trading utilisant un modele de classification ML
    (RandomForest) charge depuis ObjectStore.

    Workflow:
    1. Entrainer le modele dans research_classification.ipynb
    2. Sauvegarder dans ObjectStore via qb.object_store.save_bytes()
    3. Charger dans cet algorithme et utiliser pour les predictions

    Le modele predit la direction du marche (hausse/baisse) a J+1.
    """

    # Cles ObjectStore
    MODEL_KEY = "classification_model"
    CONFIG_KEY = "classification_config"

    # Parametres de trading
    SYMBOL = "SPY"
    CONFIDENCE_LONG_THRESHOLD = 0.55  # Probabilite min pour aller long
    CONFIDENCE_SHORT_THRESHOLD = 0.45  # Probabilite max pour liquider
    POSITION_SIZE = 1.0  # Taille de position (100% du portfolio)

    def Initialize(self):
        """Initialisation de l'algorithme."""
        self.SetStartDate(2023, 1, 1)
        self.SetEndDate(2025, 1, 1)
        self.SetCash(100000)

        # Ajouter le symbole
        self.symbol = self.AddEquity(self.SYMBOL, Resolution.Daily).Symbol

        # Charger le modele depuis ObjectStore
        self.LoadModel()

        # Configurer les indicateurs pour generer les features
        self.SetupIndicators()

        # Warm-up pour les indicateurs
        self.SetWarmUp(50)

        self.Log(f"MLClassificationAlgorithm initialise pour {self.SYMBOL}")

    def LoadModel(self):
        """Charger le modele et la configuration depuis ObjectStore."""
        try:
            # Verifier que les cles existent
            if not self.ObjectStore.ContainsKey(self.MODEL_KEY):
                raise Exception(f"Modele non trouve dans ObjectStore: {self.MODEL_KEY}")

            # Charger le modele
            model_bytes = self.ObjectStore.ReadBytes(self.MODEL_KEY)
            self.model = joblib.loads(bytes(model_bytes))

            # Charger la configuration
            if self.ObjectStore.ContainsKey(self.CONFIG_KEY):
                config_bytes = self.ObjectStore.ReadBytes(self.CONFIG_KEY)
                self.config = json.loads(bytes(config_bytes).decode('utf-8'))
                self.feature_cols = self.config.get('feature_cols', [])
            else:
                # Features par defaut si pas de config
                self.feature_cols = [
                    'rsi_14', 'ema_10', 'ema_20', 'ema_50',
                    'macd_line', 'macd_signal', 'macd_histogram',
                    'returns_1d', 'returns_5d', 'returns_10d',
                    'price_ema10_ratio', 'price_ema20_ratio', 'price_ema50_ratio',
                    'volatility_10d', 'volatility_20d'
                ]
                self.config = {}

            self.Log(f"Modele charge: {type(self.model).__name__}")
            if 'accuracy_test' in self.config:
                self.Log(f"Accuracy test: {self.config['accuracy_test']:.2%}")

        except Exception as e:
            self.Log(f"ERREUR chargement modele: {e}")
            self.model = None

    def SetupIndicators(self):
        """Configurer les indicateurs techniques pour les features."""
        # RSI
        self.rsi = self.RSI(self.symbol, 14, Resolution.Daily)

        # EMA
        self.ema10 = self.EMA(self.symbol, 10, Resolution.Daily)
        self.ema20 = self.EMA(self.symbol, 20, Resolution.Daily)
        self.ema50 = self.EMA(self.symbol, 50, Resolution.Daily)

        # MACD
        self.macd = self.MACD(self.symbol, 12, 26, 9, Resolution.Daily)

        # Historique des prix pour les returns et volatilite
        self.price_history = []
        self.returns_history = []

        # Rolling window pour les calculs
        self.close_window = RollingWindow[float](60)

    def OnData(self, data: Slice):
        """Traitement des donnees de marche."""
        if self.IsWarmingUp or self.model is None:
            return

        if not data.ContainsKey(self.symbol):
            return

        # Mettre a jour l'historique des prix
        close = data[self.symbol].Close
        self.close_window.Add(close)

        # Attendre assez de donnees
        if not self.close_window.IsReady:
            return

        # Construire le vecteur de features
        features = self.BuildFeatures(data)

        if features is None:
            return

        # Faire la prediction
        try:
            X = np.array([features])
            proba = self.model.predict_proba(X)[0]
            confidence_up = proba[1]  # Probabilite de hausse

            # Logique de trading basee sur la confiance
            self.ExecuteTradingLogic(confidence_up, close)

        except Exception as e:
            self.Log(f"Erreur prediction: {e}")

    def BuildFeatures(self, data: Slice) -> list:
        """
        Construire le vecteur de features pour la prediction.
        Doit correspondre exactement aux features du notebook de recherche.
        """
        try:
            close = data[self.symbol].Close

            # Verifier que les indicateurs sont prets
            if not (self.rsi.IsReady and self.ema10.IsReady and
                    self.ema20.IsReady and self.ema50.IsReady and
                    self.macd.IsReady):
                return None

            # Features basiques depuis indicateurs
            rsi_14 = float(self.rsi.Current.Value)
            ema_10 = float(self.ema10.Current.Value)
            ema_20 = float(self.ema20.Current.Value)
            ema_50 = float(self.ema50.Current.Value)

            macd_line = float(self.macd.Current.Value)
            macd_signal = float(self.macd.Signal.Current.Value)
            macd_histogram = macd_line - macd_signal

            # Ratios prix/EMA
            price_ema10_ratio = close / ema_10
            price_ema20_ratio = close / ema_20
            price_ema50_ratio = close / ema_50

            # Returns passes (approximation depuis close_window)
            prices = list(self.close_window)
            returns_1d = (prices[0] - prices[1]) / prices[1] if len(prices) > 1 else 0
            returns_5d = (prices[0] - prices[5]) / prices[5] if len(prices) > 5 else 0
            returns_10d = (prices[0] - prices[10]) / prices[10] if len(prices) > 10 else 0

            # Volatilite (ecart-type des returns sur 10 et 20 jours)
            if len(prices) >= 20:
                returns_list = [(prices[i] - prices[i+1]) / prices[i+1]
                               for i in range(min(19, len(prices)-1))]
                volatility_10d = float(np.std(returns_list[:10])) if len(returns_list) >= 10 else 0
                volatility_20d = float(np.std(returns_list[:20])) if len(returns_list) >= 20 else 0
            else:
                volatility_10d = 0
                volatility_20d = 0

            # Construire le vecteur dans le meme ordre que feature_cols
            features = [
                rsi_14,
                ema_10,
                ema_20,
                ema_50,
                macd_line,
                macd_signal,
                macd_histogram,
                returns_1d,
                returns_5d,
                returns_10d,
                price_ema10_ratio,
                price_ema20_ratio,
                price_ema50_ratio,
                volatility_10d,
                volatility_20d
            ]

            return features

        except Exception as e:
            self.Log(f"Erreur construction features: {e}")
            return None

    def ExecuteTradingLogic(self, confidence_up: float, current_price: float):
        """
        Executer la logique de trading basee sur la confiance du modele.

        Args:
            confidence_up: Probabilite predite de hausse (0-1)
            current_price: Prix actuel
        """
        # Log la prediction
        self.Log(f"Prediction: hausse={confidence_up:.2%}, baisse={1-confidence_up:.2%}")

        # Logique de trading
        if confidence_up > self.CONFIDENCE_LONG_THRESHOLD:
            # Signal haussier fort - acheter
            if not self.Portfolio[self.symbol].Invested:
                self.SetHoldings(self.symbol, self.POSITION_SIZE)
                self.Log(f"ACHAT: confiance={confidence_up:.2%} > {self.CONFIDENCE_LONG_THRESHOLD}")

        elif confidence_up < self.CONFIDENCE_SHORT_THRESHOLD:
            # Signal baissier - liquider
            if self.Portfolio[self.symbol].Invested:
                self.Liquidate(self.symbol)
                self.Log(f"LIQUIDATION: confiance={confidence_up:.2%} < {self.CONFIDENCE_SHORT_THRESHOLD}")

        # Zone neutre: ne rien faire si deja investi, ne pas acheter si pas investi

    def OnEndOfAlgorithm(self):
        """Appele a la fin de l'algorithme."""
        if self.model is not None:
            self.Log("Algorithme termine avec succes")
        else:
            self.Log("ERREUR: Modele non charge - executer research_classification.ipynb")
