#region imports
from AlgorithmImports import *

from aihedging.model import AIDeltaHedgeModel
#endregion


class AIDeltaHedgingAlgorithm(QCAlgorithm):
    """
    Port du chapitre 07-01 de Hands-On AI Trading (Better Hedging with
    Reinforcement Learning) — issue #18902. Algorithme porte verbatim du
    depot compagnon QuantConnect/HandsOnAITradingBook ; la librairie
    aihedging/ accompagne ce fichier.

    Demonstration de l'utilisation de l'apprentissage par renforcement
    pour construire un portefeuille delta-neutre : le reseau est d'abord
    entraine sur des donnees simulees a partir de la formule de
    Black-Scholes, puis specialise sur les valeurs de delta d'une action
    sous-jacente (TSLA dans le livre). Le modele est re-entraine a chaque
    debut de mois et le portefeuille reequilibre en delta-neutre a chaque
    debut de jour de bourse.
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_end_date(2024, 1, 1)
        self.set_cash(1_000_000)

        # Load parameters
        min_contract_duration = timedelta(
            self.get_parameter('min_contract_duration', 30)
        )
        max_contract_duration = timedelta(
            self.get_parameter('max_contract_duration', 120)
        )
        min_holding_period = timedelta(
            self.get_parameter('min_holding_period', 14)
        )
        base_epochs = self.get_parameter('base_epochs', 1000)
        self._training_lookback = timedelta(
            self.get_parameter('training_lookback_years', 2) * 365
        )
        self._asset_epochs = self.get_parameter('asset_epochs', 20)
        target_margin_usage = self.get_parameter('target_margin_usage', 0.1)

        # Create and train the model.
        self._model = AIDeltaHedgeModel(
            self, min_contract_duration, max_contract_duration,
            min_holding_period
        )
        self._model.train_base_model(plot=False, epochs=base_epochs)
        equity_symbol = self._model.train_asset_model(
            "TSLA", self.time-self._training_lookback, self.time,
            self._asset_epochs, self.live_mode
        )

        # Schedule periodic training sessions.
        self.train(
            self.date_rules.month_start(equity_symbol),
            self.time_rules.after_market_open(equity_symbol, -30),
            lambda: self._model.refit(
                self.live_mode, self._asset_epochs, self._training_lookback
            )
        )

        # Schedule trades.
        self.schedule.on(
            self.date_rules.every_day(equity_symbol),
            self.time_rules.after_market_open(equity_symbol, 1),
            lambda: self._model.trade(target_margin_usage)
        )

    def on_splits(self, splits):
        # Notify the model of split events.
        self._model.on_splits(
            splits, self._asset_epochs, self._training_lookback
        )
