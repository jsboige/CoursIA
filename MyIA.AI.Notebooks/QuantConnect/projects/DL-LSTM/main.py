#region imports
from AlgorithmImports import *
#endregion

import torch
import torch.nn as nn
import numpy as np
from io import BytesIO

class LSTMModel(nn.Module):
    """
    Modele LSTM pour la prediction de prix.

    Architecture identique a celle entrainee dans research_lstm.ipynb:
    - Input: sequence de prix normalises (seq_length, 1)
    - Hidden: 2 couches LSTM bidirectionnelles de 50 unites
    - Output: prix predit normalise
    """

    def __init__(self, hidden_size=50, num_layers=2):
        super(LSTMModel, self).__init__()
        self.hidden_size = hidden_size
        self.num_layers = num_layers

        # LSTM bidirectionnel
        self.lstm = nn.LSTM(
            input_size=1,
            hidden_size=hidden_size,
            num_layers=num_layers,
            batch_first=True,
            bidirectional=True
        )

        # Couches fully connected
        self.fc1 = nn.Linear(hidden_size * 2, 32)  # *2 car bidirectionnel
        self.relu = nn.ReLU()
        self.fc2 = nn.Linear(32, 1)

    def forward(self, x):
        # x shape: (batch, seq_length, 1)
        lstm_out, _ = self.lstm(x)

        # Prendre le dernier output
        last_output = lstm_out[:, -1, :]

        # Passer par les couches FC
        x = self.fc1(last_output)
        x = self.relu(x)
        x = self.fc2(x)

        return x


class DLLSTMAlgorithm(QCAlgorithm):
    """
    Algorithme de trading utilisant un modele LSTM charge depuis ObjectStore.

    Workflow:
    1. Entrainer le modele dans research_lstm.ipynb
    2. Sauvegarder dans ObjectStore via qb.object_store.save_bytes()
    3. Charger dans cet algorithme et utiliser pour les predictions

    Le modele predit le prix du lendemain a partir d'une sequence de prix.
    """

    # Cle ObjectStore
    MODEL_KEY = "lstm_spy_model"

    # Parametres de trading
    SYMBOL = "SPY"
    PREDICTION_THRESHOLD_LONG = 0.01   # +1% pour acheter
    PREDICTION_THRESHOLD_SHORT = -0.01  # -1% pour liquider
    POSITION_SIZE = 1.0

    def Initialize(self):
        """Initialisation de l'algorithme."""
        self.SetStartDate(2023, 1, 1)
        self.SetEndDate(2025, 1, 1)
        self.SetCash(100000)

        # Ajouter le symbole
        self.symbol = self.AddEquity(self.SYMBOL, Resolution.Daily).Symbol

        # Charger le modele LSTM
        self.model = None
        self.seq_length = 20  # Valeur par defaut
        self.scaler_min = 0
        self.scaler_max = 1

        self.LoadModel()

        # Historique des prix
        self.price_history = []

        # Warm-up pour avoir assez de donnees
        self.SetWarmUp(50)

        self.Log(f"DLLSTMAlgorithm initialise pour {self.SYMBOL}")

    def LoadModel(self):
        """Charger le modele et les parametres depuis ObjectStore."""
        try:
            # Verifier que la cle existe
            if not self.ObjectStore.ContainsKey(self.MODEL_KEY):
                raise Exception(f"Modele non trouve dans ObjectStore: {self.MODEL_KEY}")

            # Charger le checkpoint
            model_bytes = self.ObjectStore.ReadBytes(self.MODEL_KEY)
            buffer = BytesIO(bytes(model_bytes))

            checkpoint = torch.load(buffer, map_location='cpu')

            # Recuperer les parametres
            self.scaler_min = checkpoint.get('scaler_min', 0)
            self.scaler_max = checkpoint.get('scaler_max', 1)
            self.seq_length = checkpoint.get('seq_length', 20)

            hidden_size = checkpoint.get('hidden_size', 50)
            num_layers = checkpoint.get('num_layers', 2)

            # Creer et charger le modele
            self.model = LSTMModel(hidden_size=hidden_size, num_layers=num_layers)
            self.model.load_state_dict(checkpoint['model_state_dict'])
            self.model.eval()

            self.Log(f"Modele LSTM charge avec succes")
            self.Log(f"  - hidden_size: {hidden_size}")
            self.Log(f"  - num_layers: {num_layers}")
            self.Log(f"  - seq_length: {self.seq_length}")
            self.Log(f"  - scaler range: [{self.scaler_min:.2f}, {self.scaler_max:.2f}]")

        except Exception as e:
            self.Log(f"ERREUR chargement modele: {str(e)}")
            self.Log("Veuillez executer research_lstm.ipynb pour entrainer et sauvegarder le modele")

    def OnData(self, data):
        """Appele a chaque nouveau point de donnees."""
        if self.IsWarmingUp:
            return

        if self.model is None:
            return

        # Verifier qu'on a les donnees
        if self.symbol not in data:
            return

        price = data[self.symbol].Close
        self.price_history.append(price)

        # Attendre d'avoir assez de donnees
        if len(self.price_history) < self.seq_length:
            return

        # Prendre les derniers seq_length prix
        recent_prices = np.array(self.price_history[-self.seq_length:])

        # Normaliser avec le scaler sauvegarde
        normalized = (recent_prices - self.scaler_min) / (self.scaler_max - self.scaler_min)

        # Convertir en tensor: (1, seq_length, 1)
        X = torch.FloatTensor(normalized).unsqueeze(0).unsqueeze(2)

        # Prediction
        with torch.no_grad():
            pred_normalized = self.model(X).item()

        # Denormaliser
        predicted_price = pred_normalized * (self.scaler_max - self.scaler_min) + self.scaler_min

        # Calculer le rendement predit
        current_price = price
        predicted_return = (predicted_price - current_price) / current_price

        # Logique de trading basee sur la prediction
        if predicted_return > self.PREDICTION_THRESHOLD_LONG:
            # Le modele predit une hausse significative
            if not self.Portfolio[self.symbol].Invested:
                self.SetHoldings(self.symbol, self.POSITION_SIZE)
                self.Log(f"ACHAT: prix={current_price:.2f}, pred={predicted_price:.2f}, return={predicted_return:.2%}")

        elif predicted_return < self.PREDICTION_THRESHOLD_SHORT:
            # Le modele predit une baisse significative
            if self.Portfolio[self.symbol].Invested:
                self.Liquidate(self.symbol)
                self.Log(f"LIQUIDATION: prix={current_price:.2f}, pred={predicted_price:.2f}, return={predicted_return:.2%}")

        # Zone neutre: maintenir position actuelle

    def OnEndOfAlgorithm(self):
        """Appele a la fin de l'algorithme."""
        if self.model is not None:
            self.Log("Algorithme LSTM termine avec succes")
        else:
            self.Log("ERREUR: Modele non charge - executer research_lstm.ipynb")
