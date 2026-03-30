from AlgorithmImports import *
import numpy as np
import json
try:
    import joblib
except ImportError:
    joblib = None

# PyTorch for Deep Learning
try:
    import torch
    import torch.nn as nn
    from torch.utils.data import Dataset, DataLoader
    TORCH_AVAILABLE = True
except ImportError:
    TORCH_AVAILABLE = False


class SeriesDecomposition(nn.Module):
    """Series decomposition block from DLinear (AAAI 2023)."""

    def __init__(self, kernel_size):
        super().__init__()
        self.moving_avg = nn.AvgPool1d(kernel_size=kernel_size, stride=1, padding=0)

    def forward(self, x):
        # x: (batch, seq_len, channels)
        # padding for same size output
        padding_size = (x.shape[1] - 1) // 2
        front = x[:, :1, :].repeat(1, padding_size, 1)
        end = x[:, -1:, :].repeat(1, padding_size, 1)
        x_padded = torch.cat([front, x, end], dim=1)

        # moving average
        trend = self.moving_avg(x_padded.transpose(1, 2)).transpose(1, 2)
        seasonal = x - trend

        return seasonal, trend


class DLinear(nn.Module):
    """
    DLinear: Are Transformers Effective for Time Series Forecasting? (AAAI 2023)

    Ultra-simple architecture: Decomposition + Linear layers
    - No attention mechanism
    - ~10K parameters
    - SOTA performance on time series forecasting
    """

    def __init__(self, seq_len=60, pred_len=1, enc_in=1, individual=True):
        super().__init__()
        self.seq_len = seq_len
        self.pred_len = pred_len
        self.enc_in = enc_in
        self.individual = individual

        # Decomposition block
        kernel_size = 25  # Moving average window
        self.decomposition = SeriesDecomposition(kernel_size)

        if self.individual:
            # Individual linear layer for each variable
            self.Linear_Seasonal = nn.ModuleList()
            self.Linear_Trend = nn.ModuleList()

            for i in range(self.enc_in):
                self.Linear_Seasonal.append(nn.Linear(self.seq_len, self.pred_len))
                self.Linear_Trend.append(nn.Linear(self.seq_len, self.pred_len))
        else:
            # Shared linear layer for all variables
            self.Linear_Seasonal = nn.Linear(self.seq_len, self.pred_len)
            self.Linear_Trend = nn.Linear(self.seq_len, self.pred_len)

    def forward(self, x):
        # x: (batch, seq_len, channels)
        seasonal, trend = self.decomposition(x)

        if self.individual:
            seasonal_output = []
            trend_output = []
            for i in range(self.enc_in):
                seasonal_output.append(self.Linear_Seasonal[i](seasonal[:, :, i:i+1]))
                trend_output.append(self.Linear_Trend[i](trend[:, :, i:i+1]))
            seasonal_output = torch.cat(seasonal_output, dim=2)
            trend_output = torch.cat(trend_output, dim=2)
        else:
            seasonal_output = self.Linear_Seasonal(seasonal)
            trend_output = self.Linear_Trend(trend)

        return seasonal_output + trend_output


class SimpleLSTM(nn.Module):
    """Traditional LSTM for comparison (LSTM from 2015 era)."""

    def __init__(self, input_size=1, hidden_size=64, num_layers=2, output_size=1):
        super().__init__()
        self.hidden_size = hidden_size
        self.num_layers = num_layers

        self.lstm = nn.LSTM(input_size, hidden_size, num_layers, batch_first=True)
        self.fc = nn.Linear(hidden_size, output_size)

    def forward(self, x):
        # x: (batch, seq_len, input_size)
        lstm_out, _ = self.lstm(x)
        # Take last output
        out = self.fc(lstm_out[:, -1, :])
        return out.unsqueeze(1)  # (batch, 1, 1)


class CryptoLSTMPredictionAlgorithm(QCAlgorithm):
    """
    Crypto Prediction with Deep Learning (DLinear + LSTM comparison).

    Concept:
    - Utilise DLinear (SOTA AAAI 2023) pour prédire les rendements BTCUSDT
    - LSTM traditionnel inclus pour comparaison pédagogique
    - Features techniques inspirées de QC-Py-18 (Feature Engineering)
    - Walk-forward validation pour time series
    - Position sizing basé sur la confiance de la prédiction

    Basé sur: QC-Py-22 (Deep Learning for Time Series)
    """

    # Paramètres du modèle
    SEQ_LEN = 60  # 60 jours d'historique pour prédire
    PRED_LEN = 1  # Prédire 1 jour ahead
    MODEL_TYPE = "dlinear"  # "dlinear" ou "lstm"

    # Paramètres de trading
    STARTING_CASH = 100000
    BASE_POSITION_SIZE = 0.5  # 50% de base
    MAX_POSITION_SIZE = 1.0   # 100% max
    MIN_CONFIDENCE = 0.3      # Seuil de confiance minimum

    # Paramètres de training
    TRAIN_START = datetime(2020, 1, 1)
    TRAIN_END = datetime(2023, 12, 31)
    BACKTEST_START = datetime(2024, 1, 1)
    BACKTEST_END = datetime(2026, 3, 1)

    RETRAIN_DAYS = 90  # Retrainer tous les 90 jours

    # Features techniques (QC-Py-18)
    RSI_PERIOD = 14
    SMA_SHORT = 20
    SMA_LONG = 50
    EMA_SHORT = 12
    EMA_LONG = 26
    ATR_PERIOD = 14
    BB_PERIOD = 20

    # Hyperparamètres DLinear
    DLINEAR_INDIVIDUAL = True  # Linear layer per variable

    # Hyperparamètres LSTM (pour comparaison)
    LSTM_HIDDEN = 64
    LSTM_LAYERS = 2

    # Object Store keys
    MODEL_KEY = "crypto_dl_model.pkl"
    SCALER_KEY = "crypto_dl_scaler.pkl"
    METADATA_KEY = "crypto_dl_metadata.json"

    def Initialize(self):
        # Configuration backtest
        self.SetStartDate(self.BACKTEST_START.year, self.BACKTEST_START.month, self.BACKTEST_START.day)
        self.SetEndDate(self.BACKTEST_END.year, self.BACKTEST_END.month, self.BACKTEST_END.day)
        self.SetCash(self.STARTING_CASH)

        # Brokerage model pour crypto
        self.SetBrokerageModel(BrokerageName.Binance, AccountType.Cash)
        self.SetAccountCurrency("USDT")

        # Ajouter BTCUSDT
        self.symbol = self.AddCrypto("BTCUSDT", Resolution.Daily, Market.Binance).Symbol
        self.SetBenchmark(self.symbol)

        # Vérifier PyTorch
        if not TORCH_AVAILABLE:
            self.Error("PyTorch not available. This algorithm requires torch.")
            raise Exception("PyTorch required")

        # Modèle et scaler
        self.model = None
        self.scaler = None
        self.feature_stats = None  # Pour normalisation
        self.last_train_date = None

        # Charger depuis Object Store si disponible
        if joblib:
            self.load_model_from_object_store()

        # Initialiser les indicateurs
        self.indicators = self.initialize_indicators(self.symbol)

        # Schedule: Rebalance quotidien (30 min après open)
        self.Schedule.On(self.DateRules.EveryDay(self.symbol),
                         self.TimeRules.AfterMarketOpen(self.symbol, 30),
                         self.Rebalance)

        # Schedule: Retraining périodique
        self.Schedule.On(self.DateRules.Every(DayOfWeek.Monday),
                         self.TimeRules.AfterMarketOpen(self.symbol, 60),
                         self.CheckRetrain)

        # Warm-up
        self.SetWarmUp(self.SEQ_LEN + 10, Resolution.Daily)

        self.Debug("CryptoLSTMPredictionAlgorithm initialized")
        self.Debug(f"Model type: {self.MODEL_TYPE}")
        self.Debug(f"Sequence length: {self.SEQ_LEN} days")

    def initialize_indicators(self, symbol):
        """Initialise les indicateurs techniques."""
        return {
            'rsi': self.RSI(symbol, self.RSI_PERIOD, MovingAverageType.Wilders, Resolution.Daily),
            'sma_short': self.SMA(symbol, self.SMA_SHORT, Resolution.Daily),
            'sma_long': self.SMA(symbol, self.SMA_LONG, Resolution.Daily),
            'ema_short': self.EMA(symbol, self.EMA_SHORT, Resolution.Daily),
            'ema_long': self.EMA(symbol, self.EMA_LONG, Resolution.Daily),
            'atr': self.ATR(symbol, self.ATR_PERIOD, MovingAverageType.Simple, Resolution.Daily),
            'bb': self.BB(symbol, self.BB_PERIOD, 2, MovingAverageType.Simple, Resolution.Daily)
        }

    def calculate_features(self, symbol):
        """
        Calcule les features techniques pour DLinear/LSTM.

        Features inspirées de QC-Py-18:
        - Returns (5d, 10d, 20d)
        - Volatility (20d rolling std)
        - RSI normalized
        - MA ratio (short/long)
        - Position in range (20d high/low)
        - Distance from high/low
        - ATR normalized
        - Bollinger Bands position
        """
        security = self.Securities[symbol]
        indicators = self.indicators

        # Vérifier indicateurs prêts
        if not all(ind.Current.Value is not None for ind in indicators.values()):
            return None

        current_price = security.Price
        history = self.History(symbol, self.SMA_LONG + 10, Resolution.Daily)

        if len(history) < self.SMA_LONG:
            return None

        # Price features
        returns_5d = (current_price / history['close'].iloc[-5] - 1) if len(history) >= 5 else 0
        returns_10d = (current_price / history['close'].iloc[-10] - 1) if len(history) >= 10 else 0
        returns_20d = (current_price / history['close'].iloc[-20] - 1) if len(history) >= 20 else 0

        # Volatility
        daily_returns = history['close'].pct_change().dropna()
        volatility = daily_returns.rolling(20).std().iloc[-1] if len(daily_returns) >= 20 else 0

        # RSI normalized
        rsi = indicators['rsi'].Current.Value
        rsi_normalized = (rsi - 50) / 50

        # MA ratio
        sma_short = indicators['sma_short'].Current.Value
        sma_long = indicators['sma_long'].Current.Value
        ma_ratio = sma_short / sma_long if sma_long > 0 else 1

        # Position in range
        high_20d = history['high'].rolling(20).max().iloc[-1]
        low_20d = history['low'].rolling(20).min().iloc[-1]
        position_in_range = (current_price - low_20d) / (high_20d - low_20d) if high_20d > low_20d else 0.5

        # Distance from high/low
        dist_from_high = (high_20d - current_price) / current_price if current_price > 0 else 0
        dist_from_low = (current_price - low_20d) / current_price if current_price > 0 else 0

        # ATR normalized
        atr = indicators['atr'].Current.Value
        atr_normalized = atr / current_price if current_price > 0 else 0

        # Bollinger Bands position
        bb_upper = indicators['bb'].UpperBand.Current.Value
        bb_lower = indicators['bb'].LowerBand.Current.Value
        bb_position = (current_price - bb_lower) / (bb_upper - bb_lower) if bb_upper > bb_lower else 0.5

        features = np.array([
            returns_5d, returns_10d, returns_20d,
            volatility, rsi_normalized, ma_ratio,
            position_in_range, dist_from_high, dist_from_low,
            atr_normalized, bb_position
        ])

        return features

    def normalize_features(self, features, fit=False):
        """Normalise les features avec statistiques rolling."""
        if fit:
            # Calculer les stats sur les données de training
            self.feature_stats = {
                'mean': np.mean(features, axis=0),
                'std': np.std(features, axis=0) + 1e-8  # Avoid division by zero
            }

        if self.feature_stats is None:
            return features

        return (features - self.feature_stats['mean']) / self.feature_stats['std']

    def prepare_training_data(self):
        """Prépare les données de training avec walk-forward."""
        self.Debug("Preparing training data...")

        # Récupérer l'historique
        history = self.History(self.symbol, self.TRAIN_START, self.TRAIN_END, Resolution.Daily)

        if len(history) < self.SEQ_LEN + 10:
            self.Debug("Not enough historical data")
            return None, None

        # Calculer les features pour chaque jour
        features_list = []
        targets_list = []

        # Utiliser calculate_features_for_training pour simuler
        prices = history['close'].values
        highs = history['high'].values
        lows = history['low'].values

        for i in range(self.SMA_LONG, len(prices) - self.PRED_LEN):
            # Features jusqu'à i
            features = self.calculate_features_for_training(
                prices[:i+1], highs[:i+1], lows[:i+1], i
            )

            if features is None:
                continue

            # Target: rendement futur
            future_return = (prices[i + self.PRED_LEN] / prices[i] - 1)

            # Target binaire: 1 si hausse > 1%, 0 sinon
            target = 1 if future_return > 0.01 else 0

            features_list.append(features)
            targets_list.append(target)

        if len(features_list) == 0:
            self.Debug("No training samples prepared")
            return None, None

        X = np.array(features_list)
        y = np.array(targets_list)

        self.Debug(f"Training data: {X.shape[0]} samples, {X.shape[1]} features")
        self.Debug(f"Target distribution: {np.bincount(y)}")

        return X, y

    def calculate_features_for_training(self, prices, highs, lows, idx):
        """Calcule les features pour l'entraînement (offline)."""
        if idx < self.SMA_LONG:
            return None

        current_price = prices[idx]

        # Returns
        returns_5d = (current_price / prices[idx-5] - 1) if idx >= 5 else 0
        returns_10d = (current_price / prices[idx-10] - 1) if idx >= 10 else 0
        returns_20d = (current_price / prices[idx-20] - 1) if idx >= 20 else 0

        # Volatility
        returns = np.diff(prices[max(0, idx-20):idx+1]) / prices[max(0, idx-20):idx]
        volatility = np.std(returns[-20:]) if len(returns) >= 20 else 0

        # RSI
        deltas = np.diff(prices[max(0, idx-14):idx+1])
        gains = np.where(deltas > 0, deltas, 0)
        losses = np.where(deltas < 0, -deltas, 0)
        avg_gain = np.mean(gains[-14:])
        avg_loss = np.mean(losses[-14:])
        rs = avg_gain / avg_loss if avg_loss > 0 else 0
        rsi = 100 - (100 / (1 + rs))
        rsi_normalized = (rsi - 50) / 50

        # MA ratio
        sma_short = np.mean(prices[idx-20:idx+1])
        sma_long = np.mean(prices[idx-50:idx+1])
        ma_ratio = sma_short / sma_long if sma_long > 0 else 1

        # Position in range
        high_20d = np.max(highs[idx-20:idx+1])
        low_20d = np.min(lows[idx-20:idx+1])
        position_in_range = (current_price - low_20d) / (high_20d - low_20d) if high_20d > low_20d else 0.5

        # Distance from high/low
        dist_from_high = (high_20d - current_price) / current_price if current_price > 0 else 0
        dist_from_low = (current_price - low_20d) / current_price if current_price > 0 else 0

        # ATR
        tr = np.maximum(highs[idx-14:idx+1] - lows[idx-14:idx+1],
                       np.maximum(abs(highs[idx-14:idx+1] - prices[idx-15:idx]),
                                  abs(lows[idx-14:idx+1] - prices[idx-15:idx])))
        atr = np.mean(tr[-14:])
        atr_normalized = atr / current_price if current_price > 0 else 0

        # Bollinger Bands
        bb_mean = np.mean(prices[idx-20:idx+1])
        bb_std = np.std(prices[idx-20:idx+1])
        bb_upper = bb_mean + 2 * bb_std
        bb_lower = bb_mean - 2 * bb_std
        bb_position = (current_price - bb_lower) / (bb_upper - bb_lower) if bb_upper > bb_lower else 0.5

        return np.array([
            returns_5d, returns_10d, returns_20d,
            volatility, rsi_normalized, ma_ratio,
            position_in_range, dist_from_high, dist_from_low,
            atr_normalized, bb_position
        ])

    def create_sequences(self, X, y):
        """Crée les séquences pour le modèle séquentiel."""
        X_seq, y_seq = [], []

        for i in range(len(X) - self.SEQ_LEN):
            X_seq.append(X[i:i+self.SEQ_LEN])
            y_seq.append(y[i+self.SEQ_LEN])

        return np.array(X_seq), np.array(y_seq)

    def TrainModel(self):
        """Entraîne le modèle DLinear ou LSTM."""
        self.Debug(f"Training {self.MODEL_TYPE.upper()} model at {self.Time}")

        try:
            # Préparer les données
            X, y = self.prepare_training_data()

            if X is None or len(X) == 0:
                self.Debug("No training data available")
                return

            # Créer les séquences
            X_seq, y_seq = self.create_sequences(X, y)

            if len(X_seq) == 0:
                self.Debug("No sequences created")
                return

            # Normaliser
            X_seq_norm = self.normalize_features(X_seq, fit=True)

            # Convertir en PyTorch tensors
            X_tensor = torch.FloatTensor(X_seq_norm).unsqueeze(-1)  # (batch, seq, 1)
            y_tensor = torch.FloatTensor(y_seq).unsqueeze(-1)      # (batch, 1, 1)

            # Créer le modèle
            if self.MODEL_TYPE == "dlinear":
                self.model = DLinear(
                    seq_len=self.SEQ_LEN,
                    pred_len=self.PRED_LEN,
                    enc_in=1,  # Univariate
                    individual=self.DLINEAR_INDIVIDUAL
                )
            else:  # LSTM
                self.model = SimpleLSTM(
                    input_size=1,
                    hidden_size=self.LSTM_HIDDEN,
                    num_layers=self.LSTM_LAYERS,
                    output_size=1
                )

            # Training
            criterion = nn.MSELoss()
            optimizer = torch.optim.Adam(self.model.parameters(), lr=0.001)

            self.model.train()
            epochs = 50
            batch_size = 32

            dataset = list(zip(X_tensor, y_tensor))
            dataloader = DataLoader(dataset, batch_size=batch_size, shuffle=True)

            for epoch in range(epochs):
                epoch_loss = 0
                for batch_X, batch_y in dataloader:
                    optimizer.zero_grad()

                    if self.MODEL_TYPE == "dlinear":
                        # DLinear expects (batch, seq, channels)
                        predictions = self.model(batch_X)
                    else:
                        # LSTM expects (batch, seq, input_size)
                        predictions = self.model(batch_X)

                    loss = criterion(predictions, batch_y)
                    loss.backward()
                    optimizer.step()

                    epoch_loss += loss.item()

                if epoch % 10 == 0:
                    self.Debug(f"Epoch {epoch}, Loss: {epoch_loss/len(dataloader):.6f}")

            # Evaluation rapide
            self.model.eval()
            with torch.no_grad():
                predictions = self.model(X_tensor)
                train_loss = criterion(predictions, y_tensor)
                self.Debug(f"Training complete. Final loss: {train_loss.item():.6f}")

            # Sauvegarder
            self.last_train_date = self.Time
            if joblib:
                self.save_model_to_object_store()

            self.Debug(f"{self.MODEL_TYPE.upper()} model trained successfully")

        except Exception as e:
            self.Error(f"Error training model: {e}")

    def CheckRetrain(self):
        """Vérifie si le modèle doit être réentraîné."""
        if self.model is None:
            self.TrainModel()
            return

        if self.last_train_date is None:
            return

        days_since_train = (self.Time.date() - self.last_train_date.date()).days

        if days_since_train >= self.RETRAIN_DAYS:
            self.Debug(f"Retraining model (last trained {days_since_train} days ago)")
            self.TrainModel()

    def predict(self, features_sequence):
        """Prédit avec le modèle."""
        if self.model is None or self.feature_stats is None:
            return None, 0

        try:
            # Normaliser
            features_norm = self.normalize_features(features_sequence)

            # Convertir en tensor
            X = torch.FloatTensor(features_norm).unsqueeze(0).unsqueeze(-1)  # (1, seq, 1)

            # Prédire
            self.model.eval()
            with torch.no_grad():
                prediction = self.model(X)  # (1, 1, 1)
                predicted_return = prediction.item()

            # Confiance basée sur la magnitude
            confidence = min(abs(predicted_return) / 0.02, 1.0)  # 2% = 100% confiance

            return predicted_return, confidence

        except Exception as e:
            self.Debug(f"Error predicting: {e}")
            return None, 0

    def build_sequence(self):
        """Construit la séquence de features pour la prédiction."""
        history = self.History(self.symbol, self.SEQ_LEN + 10, Resolution.Daily)

        if len(history) < self.SEQ_LEN:
            return None

        sequence = []
        prices = history['close'].values
        highs = history['high'].values
        lows = history['low'].values

        for i in range(self.SMA_LONG, len(prices)):
            features = self.calculate_features_for_training(
                prices[:i+1], highs[:i+1], lows[:i+1], i
            )
            if features is not None:
                sequence.append(features)

            if len(sequence) == self.SEQ_LEN:
                break

        if len(sequence) < self.SEQ_LEN:
            return None

        return np.array(sequence[-self.SEQ_LEN:])

    def Rebalance(self):
        """Rebalance quotidien basé sur les prédictions DL."""

        # Si pas de modèle, entraîner
        if self.model is None:
            self.Debug("No model available. Training...")
            self.TrainModel()
            if self.model is None:
                return

        # Construire la séquence
        sequence = self.build_sequence()

        if sequence is None:
            self.Debug("Not enough data for prediction")
            return

        # Prédire
        predicted_return, confidence = self.predict(sequence)

        if predicted_return is None:
            return

        self.Debug(f"Prediction: {predicted_return:.4f}, Confidence: {confidence:.2f}")

        # Décision de trading
        current_position = self.Portfolio[self.symbol].Invested

        if predicted_return > 0 and confidence >= self.MIN_CONFIDENCE:
            # Signal long
            target_size = self.BASE_POSITION_SIZE + (confidence * (self.MAX_POSITION_SIZE - self.BASE_POSITION_SIZE))
            target_size = min(target_size, self.MAX_POSITION_SIZE)

            self.SetHoldings(self.symbol, target_size)
            self.Debug(f"LONG signal: {target_size:.1%} position")

        elif predicted_return < 0 and confidence >= self.MIN_CONFIDENCE:
            # Signal court/cash
            if current_position:
                self.Liquidate(self.symbol)
                self.Debug("CASH signal: Liquidated position")

        else:
            # Confiance faible, maintenir ou réduire
            if confidence < self.MIN_CONFIDENCE * 0.5 and current_position:
                self.Liquidate(self.symbol)
                self.Debug("Low confidence: Liquidated")

    def save_model_to_object_store(self):
        """Sauvegarde le modèle dans l'Object Store."""
        try:
            import tempfile
            import os

            # Sauvegarder le modèle PyTorch
            model_state = {
                'model_type': self.MODEL_TYPE,
                'state_dict': self.model.state_dict(),
                'model_class': self.model.__class__.__name__,
                'seq_len': self.SEQ_LEN,
                'pred_len': self.PRED_LEN
            }

            with tempfile.NamedTemporaryFile(delete=False, suffix='.pkl') as tmp:
                joblib.dump(model_state, tmp.name)
                self.ObjectStore.Save(self.MODEL_KEY, tmp.name)
                os.unlink(tmp.name)

            # Sauvegarder les stats
            with tempfile.NamedTemporaryFile(delete=False, suffix='.pkl') as tmp:
                joblib.dump(self.feature_stats, tmp.name)
                self.ObjectStore.Save(self.SCALER_KEY, tmp.name)
                os.unlink(tmp.name)

            # Sauvegarder les métadonnées
            metadata = {
                'model_type': self.MODEL_TYPE,
                'last_train_date': self.last_train_date.isoformat() if self.last_train_date else None,
                'seq_len': self.SEQ_LEN,
                'feature_count': 11
            }

            with tempfile.NamedTemporaryFile(delete=False, suffix='.json') as tmp:
                tmp.write(json.dumps(metadata).encode())
                self.ObjectStore.Save(self.METADATA_KEY, tmp.name)
                os.unlink(tmp.name)

            self.Debug("Model saved to Object Store")

        except Exception as e:
            self.Error(f"Error saving model: {e}")

    def load_model_from_object_store(self):
        """Charge le modèle depuis l'Object Store."""
        try:
            import tempfile
            import os

            # Charger les métadonnées
            if self.ObjectStore.ContainsKey(self.METADATA_KEY):
                with tempfile.NamedTemporaryFile(delete=False, suffix='.json') as tmp:
                    self.ObjectStore.GetFilePath(self.METADATA_KEY, tmp.name)
                    with open(tmp.name, 'r') as f:
                        metadata = json.load(f)
                    os.unlink(tmp.name)

                self.MODEL_TYPE = metadata.get('model_type', 'dlinear')
                last_train = metadata.get('last_train_date')
                if last_train:
                    self.last_train_date = datetime.fromisoformat(last_train)

                self.Debug(f"Loaded metadata: model_type={self.MODEL_TYPE}")

            # Charger le modèle
            if self.ObjectStore.ContainsKey(self.MODEL_KEY):
                with tempfile.NamedTemporaryFile(delete=False, suffix='.pkl') as tmp:
                    self.ObjectStore.GetFilePath(self.MODEL_KEY, tmp.name)
                    model_state = joblib.load(tmp.name)
                    os.unlink(tmp.name)

                # Recréer le modèle
                if model_state['model_class'] == 'DLinear':
                    self.model = DLinear(
                        seq_len=model_state['seq_len'],
                        pred_len=model_state['pred_len'],
                        enc_in=1,
                        individual=self.DLINEAR_INDIVIDUAL
                    )
                elif model_state['model_class'] == 'SimpleLSTM':
                    self.model = SimpleLSTM(
                        input_size=1,
                        hidden_size=self.LSTM_HIDDEN,
                        num_layers=self.LSTM_LAYERS,
                        output_size=1
                    )

                self.model.load_state_dict(model_state['state_dict'])
                self.Debug("Model loaded from Object Store")

            # Charger les stats
            if self.ObjectStore.ContainsKey(self.SCALER_KEY):
                with tempfile.NamedTemporaryFile(delete=False, suffix='.pkl') as tmp:
                    self.ObjectStore.GetFilePath(self.SCALER_KEY, tmp.name)
                    self.feature_stats = joblib.load(tmp.name)
                    os.unlink(tmp.name)

                self.Debug("Feature stats loaded")

            return True

        except Exception as e:
            self.Debug(f"Error loading model: {e}")
            return False
