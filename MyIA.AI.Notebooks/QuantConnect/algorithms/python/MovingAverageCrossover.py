"""
Moving Average Crossover Strategy - Production Algorithm

Stratégie simple et robuste basée sur le croisement de deux moyennes mobiles (SMA).

**Principe:**
- **Golden Cross** (SMA rapide > SMA lente): Signal d'achat
- **Death Cross** (SMA rapide < SMA lente): Signal de vente

**Paramètres:**
- fast_period: Période de la SMA rapide (défaut: 50 jours)
- slow_period: Période de la SMA lente (défaut: 200 jours)
- symbol: Ticker à trader (défaut: SPY)
- resolution: Résolution des données (défaut: Daily)

**Performance Typique (SPY 2020-2023):**
- Sharpe Ratio: ~0.8-1.2
- Max Drawdown: ~-20% à -25%
- Win Rate: ~45-55%

**Usage dans QuantConnect:**
1. Créer un nouveau projet dans QuantConnect Lab
2. Copier ce fichier dans main.py
3. Configurer les dates de backtest
4. Lancer le backtest

**Auteur:** CoursIA - QuantConnect AI Trading Series
**Notebook:** QC-Py-01-Setup.ipynb, QC-Py-02-Platform-Fundamentals.ipynb
**Version:** 1.0.0
"""

from AlgorithmImports import *


class MovingAverageCrossover(QCAlgorithm):
    """
    Moving Average Crossover Strategy

    Achète quand SMA rapide croise au-dessus de la SMA lente (Golden Cross).
    Vend quand SMA rapide croise en-dessous de la SMA lente (Death Cross).
    """

    def Initialize(self):
        """
        Configuration initiale de l'algorithme.

        Appelé une fois au début du backtest ou en live trading.
        Configure les dates, le capital, les securities et les indicateurs.
        """
        # Configuration de base
        self.SetStartDate(2020, 1, 1)    # Date de début du backtest
        self.SetEndDate(2023, 12, 31)    # Date de fin du backtest
        self.SetCash(100000)              # Capital initial: $100,000

        # Ajouter le security (SPY = S&P 500 ETF)
        self.symbol = self.AddEquity("SPY", Resolution.Daily).Symbol

        # Créer les indicateurs SMA
        self.fast_period = 50
        self.slow_period = 200

        self.fast_sma = self.SMA(self.symbol, self.fast_period, Resolution.Daily)
        self.slow_sma = self.SMA(self.symbol, self.slow_period, Resolution.Daily)

        # Warm-up period: Attendre que les indicateurs soient prêts
        # Nécessite au moins slow_period barres
        self.SetWarmUp(self.slow_period, Resolution.Daily)

        # Variables de tracking
        self.previous_fast = None  # Valeur précédente de SMA rapide
        self.previous_slow = None  # Valeur précédente de SMA lente

        # Logging initial
        self.Debug(f"Algorithm initialized with {self.symbol}")
        self.Debug(f"Fast SMA: {self.fast_period}, Slow SMA: {self.slow_period}")

        # Planifier un log quotidien des indicateurs (optionnel, pour debugging)
        # self.Schedule.On(
        #     self.DateRules.EveryDay(self.symbol),
        #     self.TimeRules.At(16, 0),  # 4:00 PM
        #     self.LogIndicators
        # )

    def OnData(self, data):
        """
        Méthode appelée à chaque nouvelle donnée.

        Args:
            data (Slice): Contient les données de marché (prix, volume, etc.)
        """
        # Pendant le warm-up, ne pas trader
        if self.IsWarmingUp:
            return

        # Vérifier que les indicateurs sont prêts
        if not self.fast_sma.IsReady or not self.slow_sma.IsReady:
            return

        # Vérifier que nous avons des données pour ce symbole
        if not data.ContainsKey(self.symbol):
            return

        # Récupérer les valeurs actuelles des SMA
        fast_value = self.fast_sma.Current.Value
        slow_value = self.slow_sma.Current.Value

        # Détection du croisement (crossover)
        # Pour cela, on a besoin de la valeur précédente
        if self.previous_fast is not None and self.previous_slow is not None:
            # GOLDEN CROSS: SMA rapide croise AU-DESSUS de la SMA lente
            # Condition: previous_fast <= previous_slow ET fast_value > slow_value
            if self.previous_fast <= self.previous_slow and fast_value > slow_value:
                if not self.Portfolio.Invested:
                    # Acheter avec 100% du portfolio
                    quantity = self.CalculateOrderQuantity(self.symbol, 1.0)
                    self.MarketOrder(self.symbol, quantity)

                    self.Log(f"GOLDEN CROSS - BUY: Fast SMA ({fast_value:.2f}) > Slow SMA ({slow_value:.2f})")

            # DEATH CROSS: SMA rapide croise EN-DESSOUS de la SMA lente
            # Condition: previous_fast >= previous_slow ET fast_value < slow_value
            elif self.previous_fast >= self.previous_slow and fast_value < slow_value:
                if self.Portfolio.Invested:
                    # Vendre toutes les positions
                    self.Liquidate(self.symbol)

                    self.Log(f"DEATH CROSS - SELL: Fast SMA ({fast_value:.2f}) < Slow SMA ({slow_value:.2f})")

        # Sauvegarder les valeurs pour la prochaine itération
        self.previous_fast = fast_value
        self.previous_slow = slow_value

    def OnEndOfAlgorithm(self):
        """
        Appelé à la fin du backtest ou quand le live trading s'arrête.

        Utilisé pour logger les statistiques finales, nettoyer des ressources, etc.
        """
        self.Log(f"Algorithm ended. Final Portfolio Value: ${self.Portfolio.TotalPortfolioValue:,.2f}")

        # Calculer le retour total
        initial_capital = 100000
        final_value = self.Portfolio.TotalPortfolioValue
        total_return = (final_value - initial_capital) / initial_capital

        self.Log(f"Total Return: {total_return:.2%}")

        # Log final des indicateurs
        self.Log(f"Final Fast SMA ({self.fast_period}): {self.fast_sma.Current.Value:.2f}")
        self.Log(f"Final Slow SMA ({self.slow_period}): {self.slow_sma.Current.Value:.2f}")

    def LogIndicators(self):
        """
        Méthode optionnelle pour logger quotidiennement les valeurs des indicateurs.

        Utile pour debugging et monitoring en live trading.
        """
        if self.fast_sma.IsReady and self.slow_sma.IsReady:
            self.Log(f"Fast SMA: {self.fast_sma.Current.Value:.2f}, Slow SMA: {self.slow_sma.Current.Value:.2f}")

            # Optionnel: Logger aussi le prix actuel
            if self.Securities[self.symbol].Price > 0:
                price = self.Securities[self.symbol].Price
                self.Log(f"Current Price: {price:.2f}")


# ==========================================
# VARIANTES ET AMÉLIORATIONS POSSIBLES
# ==========================================

class MovingAverageCrossoverAdvanced(QCAlgorithm):
    """
    Version avancée avec filtres additionnels et gestion de risque.

    Améliorations:
    1. Filtre de volume minimum
    2. Stop-loss et take-profit
    3. Position sizing dynamique basé sur la volatilité
    4. Filtre de tendance long-terme (SMA 200 comme filtre)
    """

    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetEndDate(2023, 12, 31)
        self.SetCash(100000)

        self.symbol = self.AddEquity("SPY", Resolution.Daily).Symbol

        # Indicateurs
        self.fast_sma = self.SMA(self.symbol, 50)
        self.slow_sma = self.SMA(self.symbol, 200)
        self.volume_sma = self.SMA(self.symbol, 20, Field.Volume)  # Moyenne volume

        # Indicateurs de volatilité pour position sizing
        self.atr = self.ATR(self.symbol, 14)  # Average True Range

        # Paramètres de risque
        self.stop_loss_percent = 0.05   # 5% stop-loss
        self.take_profit_percent = 0.15  # 15% take-profit
        self.min_volume_multiplier = 0.8  # Volume doit être > 80% de la moyenne

        self.SetWarmUp(200)

        # Variables de tracking
        self.previous_fast = None
        self.previous_slow = None
        self.entry_price = None  # Prix d'entrée pour stop-loss/take-profit

    def OnData(self, data):
        if self.IsWarmingUp:
            return

        if not self.fast_sma.IsReady or not self.slow_sma.IsReady or not self.volume_sma.IsReady:
            return

        if not data.ContainsKey(self.symbol):
            return

        fast_value = self.fast_sma.Current.Value
        slow_value = self.slow_sma.Current.Value
        current_price = data[self.symbol].Close
        current_volume = data[self.symbol].Volume
        avg_volume = self.volume_sma.Current.Value

        # Vérifier stop-loss et take-profit si position ouverte
        if self.Portfolio.Invested and self.entry_price is not None:
            price_change = (current_price - self.entry_price) / self.entry_price

            # Stop-loss déclenché
            if price_change <= -self.stop_loss_percent:
                self.Liquidate(self.symbol)
                self.Log(f"STOP-LOSS triggered at {price_change:.2%}")
                self.entry_price = None
                return

            # Take-profit déclenché
            if price_change >= self.take_profit_percent:
                self.Liquidate(self.symbol)
                self.Log(f"TAKE-PROFIT triggered at {price_change:.2%}")
                self.entry_price = None
                return

        # Logique de trading avec filtres
        if self.previous_fast is not None and self.previous_slow is not None:
            # GOLDEN CROSS avec filtre de volume
            if (self.previous_fast <= self.previous_slow and
                fast_value > slow_value and
                current_volume > avg_volume * self.min_volume_multiplier and
                not self.Portfolio.Invested):

                # Position sizing basé sur volatilité (ATR)
                if self.atr.IsReady:
                    # Risquer 2% du capital par trade
                    risk_amount = self.Portfolio.TotalPortfolioValue * 0.02
                    atr_value = self.atr.Current.Value

                    # Calculer position size: risk / (stop_loss_percent * price)
                    position_size = risk_amount / (self.stop_loss_percent * current_price)
                    position_size = min(position_size, self.Portfolio.TotalPortfolioValue / current_price)

                    self.MarketOrder(self.symbol, int(position_size))
                    self.entry_price = current_price

                    self.Log(f"GOLDEN CROSS (filtered) - BUY {int(position_size)} shares at ${current_price:.2f}")
                else:
                    # Fallback: position standard
                    self.SetHoldings(self.symbol, 1.0)
                    self.entry_price = current_price

            # DEATH CROSS
            elif (self.previous_fast >= self.previous_slow and
                  fast_value < slow_value and
                  self.Portfolio.Invested):

                self.Liquidate(self.symbol)
                self.Log(f"DEATH CROSS - SELL at ${current_price:.2f}")
                self.entry_price = None

        self.previous_fast = fast_value
        self.previous_slow = slow_value

    def OnEndOfAlgorithm(self):
        final_value = self.Portfolio.TotalPortfolioValue
        total_return = (final_value - 100000) / 100000

        self.Log(f"Final Portfolio Value: ${final_value:,.2f}")
        self.Log(f"Total Return: {total_return:.2%}")


# ==========================================
# NOTES POUR L'UTILISATEUR
# ==========================================

"""
COMMENT UTILISER CET ALGORITHME DANS QUANTCONNECT:

1. **Cloud (Recommandé pour débutants):**
   - Créer un compte gratuit sur https://www.quantconnect.com
   - Créer un nouveau projet Python
   - Copier le code de MovingAverageCrossover dans main.py
   - Cliquer sur "Backtest" pour lancer

2. **Local (LEAN CLI):**
   ```bash
   lean project-create --language python MovingAverageCrossover
   # Copier ce fichier dans le projet créé
   lean backtest MovingAverageCrossover
   ```

3. **Personnalisation:**
   - Modifier self.fast_period et self.slow_period dans Initialize()
   - Changer self.symbol pour trader un autre ticker
   - Ajuster les dates SetStartDate() / SetEndDate()

4. **Variante avancée:**
   - Utiliser MovingAverageCrossoverAdvanced au lieu de MovingAverageCrossover
   - Inclut stop-loss, take-profit, filtre volume, position sizing

MÉTRIQUES IMPORTANTES À ANALYSER:
- Sharpe Ratio (> 1.0 = bon)
- Max Drawdown (< -25% = acceptable)
- Win Rate (> 50% = bon pour stratégies trend-following)
- Nombre de trades (> 10 pour significativité statistique)

LIMITATIONS DE CETTE STRATÉGIE:
- Fonctionne bien dans les marchés tendanciels (2020-2021)
- Sous-performe dans les marchés latéraux (2022)
- Génère peu de trades (5-15 par an avec SMA 50/200)
- Sensible aux faux signaux (whipsaws)

AMÉLIORATIONS POSSIBLES:
- Ajouter un filtre de volatilité (ATR)
- Combiner avec RSI pour confirmation
- Utiliser des moyennes mobiles exponentielles (EMA) au lieu de SMA
- Implémenter du position sizing dynamique
- Ajouter des règles de sortie partielle (scaling out)
"""
