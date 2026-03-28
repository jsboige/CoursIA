from AlgorithmImports import *
import numpy as np
try:
    import joblib
except ImportError:
    joblib = None
from sklearn.ensemble import RandomForestClassifier
from sklearn.preprocessing import StandardScaler

class SectorMLClassificationAlgorithm(QCAlgorithm):
    """
    Strategie de Rotation Sectorielle avec Machine Learning.

    Concept:
    - Utilise Random Forest pour classer les secteurs en 3 classes:
      * BUY: Secteur avec fort potentiel de hausse
      * HOLD: Secteur neutre
      * AVOID: Secteur avec risque de baisse
    - Rotation mensuelle basée sur les prédictions ML
    - Features techniques inspirées de QC-Py-18 (Feature Engineering)
    - Top 3 secteurs classés "BUY" sont achetés (equal-weight)

    ETFs Sectoriels utilisés:
    - XLK: Technology
    - XLF: Financials
    - XLV: Healthcare
    - XLE: Energy
    - XLY: Consumer Discretionary
    - XLP: Consumer Staples
    - XLI: Industrials
    - XLB: Materials
    - XLU: Utilities
    - XLRE: Real Estate
    - XLC: Communication Services

    Basé sur: QC-Py-19 (ML Supervised Classification)
    """

    # 11 Sector ETFs
    SECTOR_ETFS = {
        "XLK": "Technology",
        "XLF": "Financials",
        "XLV": "Healthcare",
        "XLE": "Energy",
        "XLY": "Consumer Discretionary",
        "XLP": "Consumer Staples",
        "XLI": "Industrials",
        "XLB": "Materials",
        "XLU": "Utilities",
        "XLRE": "Real Estate",
        "XLC": "Communication Services"
    }

    # Paramètres ML
    MODEL_KEY = "sector_ml_model.pkl"
    SCALER_KEY = "sector_ml_scaler.pkl"

    # Périodes pour le training
    TRAIN_START = datetime(2015, 1, 1)
    TRAIN_END = datetime(2022, 12, 31)
    BACKTEST_START = datetime(2023, 1, 1)
    BACKTEST_END = datetime(2026, 3, 1)

    # Paramètres de trading
    STARTING_CASH = 100000
    TOP_N_SECTORS = 3  # Nombre de secteurs à acheter (top-3 classés BUY)
    REBALANCE_DAY = 1  # 1er jour de chaque mois

    # Features techniques (inspirées de QC-Py-18)
    RSI_PERIOD = 14
    SMA_SHORT = 20
    SMA_LONG = 100  # v6: 100 au lieu de 50 pour un signal de tendance plus stable
    SMA_REGIME = 200  # v6: filtre de regime macro (prix > SMA200 = bull)
    EMA_SHORT = 12
    EMA_LONG = 26
    MACD_SIGNAL = 9
    BB_PERIOD = 20
    BB_STD = 2
    ATR_PERIOD = 14

    # Paramètres Random Forest
    RF_N_ESTIMATORS = 100
    RF_MAX_DEPTH = 5
    RF_MIN_SAMPLES_SPLIT = 10

    # Seuils de classification pour labels
    # Utilisés pour créer les labels pendant le training
    BUY_THRESHOLD = 0.02   # Rendement > 2% sur le mois = BUY
    AVOID_THRESHOLD = -0.01 # Rendement < -1% sur le mois = AVOID

    def Initialize(self):
        # Configuration backtest
        self.SetStartDate(self.BACKTEST_START.year, self.BACKTEST_START.month, self.BACKTEST_START.day)
        self.SetEndDate(self.BACKTEST_END.year, self.BACKTEST_END.month, self.BACKTEST_END.day)
        self.SetCash(self.STARTING_CASH)
        self.SetBrokerageModel(BrokerageName.QuantConnectBrokerage, AccountType.MARGIN)

        # Ajouter les 11 ETFs sectoriels
        self.symbols = []
        self.etf_tickers = list(self.SECTOR_ETFS.keys())

        for ticker in self.etf_tickers:
            symbol = self.AddEquity(ticker, Resolution.Daily, Market.USA).Symbol
            self.symbols.append(symbol)

        # Benchmark = SPY
        self.benchmark = self.AddEquity("SPY", Resolution.Daily, Market.USA).Symbol
        self.SetBenchmark(self.benchmark)

        # ML Model et Scaler
        self.model = None
        self.scaler = None

        # Charger depuis Object Store si disponible
        if joblib:
            self.load_model_from_object_store()

        # Initialiser les indicateurs pour chaque ETF
        self.indicators = {}
        for symbol in self.symbols:
            self.indicators[symbol.ID] = self.initialize_indicators(symbol)

        # v6: SMA200 regime filter sur SPY (benchmark)
        self.spy_sma200 = self.SMA(self.benchmark, self.SMA_REGIME, Resolution.Daily)

        # Dictionnaire pour stocker les features
        self.features_history = {}

        # Schedule: Training mensuel (v6: mensuel pour adaptation plus rapide)
        # Training a l'ouverture pour que le modele soit pret pour le rebalance
        self.Schedule.On(self.DateRules.MonthStart(self.etf_tickers),
                         self.TimeRules.AfterMarketOpen("SPY", 10),
                         self.TrainModel)

        # Schedule: Rebalance mensuel (1er jour du mois, apres training)
        self.Schedule.On(self.DateRules.MonthStart(self.etf_tickers),
                         self.TimeRules.AfterMarketOpen("SPY", 45),
                         self.Rebalance)

        # Warm-up pour les indicateurs
        self.SetWarmUp(max(self.SMA_REGIME, self.BB_PERIOD, self.MACD_SIGNAL) + self.ATR_PERIOD, Resolution.Daily)

        self.Debug("SectorMLClassificationAlgorithm initialized")
        self.Debug(f"Sectors: {', '.join(self.etf_tickers)}")
        self.Debug(f"Training period: {self.TRAIN_START} to {self.TRAIN_END}")

    def initialize_indicators(self, symbol):
        """Initialise les indicateurs techniques pour un symbole."""
        return {
            'rsi': self.RSI(symbol, self.RSI_PERIOD, MovingAverageType.Wilders, Resolution.Daily),
            'sma_short': self.SMA(symbol, self.SMA_SHORT, Resolution.Daily),
            'sma_long': self.SMA(symbol, self.SMA_LONG, Resolution.Daily),
            'ema_short': self.EMA(symbol, self.EMA_SHORT, Resolution.Daily),
            'ema_long': self.EMA(symbol, self.EMA_LONG, Resolution.Daily),
            'atr': self.ATR(symbol, self.ATR_PERIOD, MovingAverageType.Simple, Resolution.Daily)
        }

    def calculate_features(self, symbol):
        """
        Calcule les features techniques pour un symbole.

        Features inspirées de QC-Py-18 (Feature Engineering):
        - Price-based: returns, volatility, range
        - Indicator-based: RSI, MACD, Bollinger Bands, position in range
        """
        security = self.Securities[symbol]
        indicators = self.indicators[symbol.ID]

        # Vérifier que les indicateurs sont prêts
        if not all(ind.Current.Value is not None for ind in indicators.values()):
            return None

        # Prix actuel
        current_price = security.Price
        history = self.History(symbol, self.SMA_LONG + 10, Resolution.Daily)

        if len(history) < self.SMA_LONG:
            return None

        # === PRICE FEATURES ===
        # Rendements sur différentes périodes
        returns_5d = (current_price / history['close'].iloc[-5] - 1) if len(history) >= 5 else 0
        returns_10d = (current_price / history['close'].iloc[-10] - 1) if len(history) >= 10 else 0
        returns_20d = (current_price / history['close'].iloc[-20] - 1) if len(history) >= 20 else 0

        # Volatilité (écart-type des rendements sur 20 jours)
        daily_returns = history['close'].pct_change().dropna()
        volatility = daily_returns.rolling(20).std().iloc[-1] if len(daily_returns) >= 20 else 0

        # === INDICATOR FEATURES ===
        rsi = indicators['rsi'].Current.Value
        rsi_normalized = (rsi - 50) / 50  # Normalize [-1, 1]

        sma_short = indicators['sma_short'].Current.Value
        sma_long = indicators['sma_long'].Current.Value
        ma_ratio = sma_short / sma_long if sma_long > 0 else 1

        # Position dans le range 20D
        high_20d = history['high'].rolling(20).max().iloc[-1]
        low_20d = history['low'].rolling(20).min().iloc[-1]
        position_in_range = (current_price - low_20d) / (high_20d - low_20d) if high_20d > low_20d else 0.5

        # EMA pour MACD
        ema_short = indicators['ema_short'].Current.Value
        ema_long = indicators['ema_long'].Current.Value
        macd = ema_short - ema_long
        macd_normalized = macd / current_price if current_price > 0 else 0

        # Distance from high/low
        dist_from_high = (high_20d - current_price) / current_price if current_price > 0 else 0
        dist_from_low = (current_price - low_20d) / current_price if current_price > 0 else 0

        # ATR normalisé
        atr = indicators['atr'].Current.Value
        atr_normalized = atr / current_price if current_price > 0 else 0

        features = {
            'returns_5d': returns_5d,
            'returns_10d': returns_10d,
            'returns_20d': returns_20d,
            'volatility': volatility,
            'rsi_normalized': rsi_normalized,
            'ma_ratio': ma_ratio,
            'position_in_range': position_in_range,
            'macd_normalized': macd_normalized,
            'dist_from_high': dist_from_high,
            'dist_from_low': dist_from_low,
            'atr_normalized': atr_normalized
        }

        return features

    def create_training_labels(self, lookahead_days=20):
        """
        Crée les labels pour le training (3 classes).

        Classes:
        - 2 (BUY): Rendement futur > BUY_THRESHOLD (2%)
        - 1 (HOLD): Rendement entre AVOID_THRESHOLD et BUY_THRESHOLD
        - 0 (AVOID): Rendement futur < AVOID_THRESHOLD (-1%)
        """
        labels = {}

        for symbol in self.symbols:
            # Récupérer l'historique pour calculer le rendement futur
            history = self.History([symbol], self.TRAIN_START, self.TRAIN_END, Resolution.Daily)

            if len(history) < lookahead_days + 1:
                continue

            df = history['close'].unstack(level=0)
            future_returns = df.shift(-lookahead_days) / df - 1

            # Créer les labels (2 = BUY, 1 = HOLD, 0 = AVOID)
            label_series = future_returns.apply(
                lambda x: 2 if x > self.BUY_THRESHOLD else (0 if x < self.AVOID_THRESHOLD else 1)
            )

            labels[symbol.ID] = label_series

        return labels

    def prepare_training_data(self):
        """
        Prépare les données de training (features + labels).
        """
        self.Debug("Preparing training data...")

        # Récupérer les labels
        labels = self.create_training_labels()

        # Récupérer l'historique complet
        history = self.History(self.symbols, self.TRAIN_START, self.TRAIN_END, Resolution.Daily)

        if 'close' in history.columns:
            price_data = history['close'].unstack(level=0)
        else:
            price_data = history.unstack(level=0)

        X_list = []
        y_list = []

        # Pour chaque date dans la période de training
        for date in price_data.index[50:-20]:  # Skip warmup et lookahead
            # Calculer les features pour chaque secteur à cette date
            features_list = []
            labels_list = []

            for symbol in self.symbols:
                symbol_id = symbol.ID

                # Récupérer le label pour cette date
                if symbol_id in labels and date in labels[symbol_id].index:
                    label = labels[symbol_id].loc[date]

                    # Skip si NaN
                    if pd.isna(label):
                        continue

                    # Calculer les features (simplifié pour le training)
                    # En pratique, on utiliserait l'historique jusqu'à cette date
                    features = self.calculate_features_for_training(symbol, date, price_data)

                    if features is not None:
                        features_list.append(features)
                        labels_list.append(label)

            if features_list:
                X_list.extend(features_list)
                y_list.extend(labels_list)

        if len(X_list) == 0:
            self.Debug("Warning: No training data prepared!")
            return None, None

        X = np.array(X_list)
        y = np.array(y_list)

        self.Debug(f"Training data prepared: {X.shape[0]} samples, {X.shape[1]} features")
        return X, y

    def calculate_features_for_training(self, symbol, date, price_data):
        """
        Calcule les features pour une date donnée (training).

        Version simplifiée pour le training avec données historiques.
        """
        try:
            symbol_id = symbol.ID
            if symbol_id not in price_data.columns:
                return None

            # Prix jusqu'à cette date
            prices = price_data[symbol_id][:date]

            if len(prices) < self.SMA_LONG:
                return None

            current_price = prices.iloc[-1]

            # Features calculées sur l'historique jusqu'à cette date
            returns_5d = (current_price / prices.iloc[-5] - 1) if len(prices) >= 5 else 0
            returns_10d = (current_price / prices.iloc[-10] - 1) if len(prices) >= 10 else 0
            returns_20d = (current_price / prices.iloc[-20] - 1) if len(prices) >= 20 else 0

            # Volatilité
            daily_returns = prices.pct_change().dropna()
            volatility = daily_returns.rolling(20).std().iloc[-1] if len(daily_returns) >= 20 else 0

            # RSI
            delta = prices.diff()
            gain = delta.clip(lower=0)
            loss = -delta.clip(lower=0)
            avg_gain = gain.rolling(14).mean().iloc[-1]
            avg_loss = loss.rolling(14).mean().iloc[-1]
            rs = avg_gain / avg_loss if avg_loss > 0 else 0
            rsi = 100 - (100 / (1 + rs))
            rsi_normalized = (rsi - 50) / 50

            # MA ratio
            sma_short = prices.rolling(20).mean().iloc[-1]
            sma_long = prices.rolling(50).mean().iloc[-1]
            ma_ratio = sma_short / sma_long if sma_long > 0 else 1

            # Position in range
            high_20d = prices.rolling(20).max().iloc[-1]
            low_20d = prices.rolling(20).min().iloc[-1]
            position_in_range = (current_price - low_20d) / (high_20d - low_20d) if high_20d > low_20d else 0.5

            return [
                returns_5d, returns_10d, returns_20d,
                volatility, rsi_normalized, ma_ratio, position_in_range
            ]

        except Exception as e:
            self.Debug(f"Error calculating features for {symbol.ID} at {date}: {e}")
            return None

    def TrainModel(self):
        """Entraîne le modèle Random Forest avec les données historiques."""
        self.Debug(f"Training ML model at {self.Time}")

        try:
            # Préparer les données
            X, y = self.prepare_training_data()

            if X is None or len(X) == 0:
                self.Debug("No training data available. Skipping training.")
                return

            # Normaliser les features
            self.scaler = StandardScaler()
            X_scaled = self.scaler.fit_transform(X)

            # Entraîner Random Forest
            self.model = RandomForestClassifier(
                n_estimators=self.RF_N_ESTIMATORS,
                max_depth=self.RF_MAX_DEPTH,
                min_samples_split=self.RF_MIN_SAMPLES_SPLIT,
                random_state=42,
                n_jobs=-1
            )

            self.model.fit(X_scaled, y)

            # Feature importance (pour debug)
            feature_names = [
                'returns_5d', 'returns_10d', 'returns_20d',
                'volatility', 'rsi_normalized', 'ma_ratio', 'position_in_range'
            ]

            self.Debug("Model trained successfully")
            self.Debug(f"Feature importances:")
            for name, importance in zip(feature_names, self.model.feature_importances_):
                self.Debug(f"  {name}: {importance:.4f}")

            # Sauvegarder dans Object Store
            if joblib:
                self.save_model_to_object_store()

        except Exception as e:
            self.Error(f"Error training model: {e}")

    def predict_sector_class(self, symbol):
        """
        Prédit la classe pour un secteur (BUY=2, HOLD=1, AVOID=0).
        """
        if self.model is None or self.scaler is None:
            return 1  # HOLD par défaut si pas de modèle

        try:
            # Calculer les features
            features_dict = self.calculate_features(symbol)

            if features_dict is None:
                return 1  # HOLD si features pas prêtes

            # Extraire dans le bon ordre (7 features pour training)
            features = [
                features_dict['returns_5d'],
                features_dict['returns_10d'],
                features_dict['returns_20d'],
                features_dict['volatility'],
                features_dict['rsi_normalized'],
                features_dict['ma_ratio'],
                features_dict['position_in_range']
            ]

            # Prédire
            X = np.array(features).reshape(1, -1)
            X_scaled = self.scaler.transform(X)
            prediction = self.model.predict(X_scaled)[0]

            # Probabilités pour debug
            probs = self.model.predict_proba(X_scaled)[0]

            return prediction

        except Exception as e:
            self.Debug(f"Error predicting for {symbol.ID}: {e}")
            return 1  # HOLD par défaut

    def Rebalance(self):
        """Rebalance le portfolio mensuellement basé sur les prédictions ML."""

        # v6: Filtre de regime macro - si SPY < SMA200, reduire l'exposition
        spy_price = self.Securities[self.benchmark].Price
        spy_above_sma200 = (self.spy_sma200.IsReady and
                            spy_price > self.spy_sma200.Current.Value)

        # v6: Bear regime defense - liquidate if SPY below SMA200
        if self.spy_sma200.IsReady and not spy_above_sma200:
            self.Debug(f"BEAR regime: SPY ({spy_price:.2f}) < SMA200 ({self.spy_sma200.Current.Value:.2f}). Liquidating.")
            self.Liquidate()
            return

        # Si pas de modèle, entraîner d'abord
        if self.model is None:
            self.Debug("No model available. Training...")
            self.TrainModel()
            if self.model is None:
                return

        self.Debug(f"Rebalancing at {self.Time}")

        # Prédire la classe pour chaque secteur
        sector_predictions = {}

        for symbol in self.symbols:
            prediction = self.predict_sector_class(symbol)
            sector_predictions[symbol] = prediction

        # Sélectionner les top-N secteurs classés BUY (prediction = 2)
        buy_sectors = [s for s, p in sector_predictions.items() if p == 2]

        # Si moins de TOP_N secteurs BUY, inclure les HOLD
        if len(buy_sectors) < self.TOP_N_SECTORS:
            hold_sectors = [s for s, p in sector_predictions.items() if p == 1]
            buy_sectors.extend(hold_sectors[:self.TOP_N_SECTORS - len(buy_sectors)])

        # Limiter à TOP_N_SECTORS
        selected_sectors = buy_sectors[:self.TOP_N_SECTORS]

        self.Debug(f"Selected sectors for long: {[self.Securities[s].Symbol for s in selected_sectors]}")

        # Calculer le poids pour chaque secteur (equal-weight)
        weight = 1.0 / len(selected_sectors) if len(selected_sectors) > 0 else 0

        # Liquid toutes les positions
        self.Liquidate()

        # Ouvrir les positions
        for symbol in selected_sectors:
            self.SetHoldings(symbol, weight)

        self.Debug(f"Rebalance complete: {len(selected_sectors)} positions, weight={weight:.2%}")

    def save_model_to_object_store(self):
        """Sauvegarde le modèle et le scaler dans l'Object Store."""
        try:
            import tempfile
            import os

            # Sauvegarder le modèle
            with tempfile.NamedTemporaryFile(delete=False, suffix='.pkl') as tmp:
                joblib.dump(self.model, tmp.name)
                self.ObjectStore.Save(self.MODEL_KEY, tmp.name)
                os.unlink(tmp.name)

            # Sauvegarder le scaler
            with tempfile.NamedTemporaryFile(delete=False, suffix='.pkl') as tmp:
                joblib.dump(self.scaler, tmp.name)
                self.ObjectStore.Save(self.SCALER_KEY, tmp.name)
                os.unlink(tmp.name)

            self.Debug(f"Model and scaler saved to Object Store")

        except Exception as e:
            self.Error(f"Error saving to Object Store: {e}")

    def load_model_from_object_store(self):
        """Charge le modèle et le scaler depuis l'Object Store."""
        try:
            import tempfile
            import os

            # Charger le modèle
            if self.ObjectStore.ContainsKey(self.MODEL_KEY):
                with tempfile.NamedTemporaryFile(delete=False, suffix='.pkl') as tmp:
                    self.ObjectStore.GetFilePath(self.MODEL_KEY, tmp.name)
                    self.model = joblib.load(tmp.name)
                    os.unlink(tmp.name)

                self.Debug(f"Model loaded from Object Store")

            # Charger le scaler
            if self.ObjectStore.ContainsKey(self.SCALER_KEY):
                with tempfile.NamedTemporaryFile(delete=False, suffix='.pkl') as tmp:
                    self.ObjectStore.GetFilePath(self.SCALER_KEY, tmp.name)
                    self.scaler = joblib.load(tmp.name)
                    os.unlink(tmp.name)

                self.Debug(f"Scaler loaded from Object Store")

            return True

        except Exception as e:
            self.Debug(f"Error loading from Object Store: {e}")
            return False
