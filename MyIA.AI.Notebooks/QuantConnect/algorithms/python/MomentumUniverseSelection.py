"""
Momentum Universe Selection Strategy - Production Algorithm

Stratégie de sélection d'univers basée sur le momentum 12 mois.
Sélectionne les top 20 actions par performance et rebalance mensuellement.

**Principe:**
- Filtrage Coarse: Top 500 par dollar volume (liquidité)
- Filtrage Fine: Calcul momentum 12 mois, sélection top 20
- Allocation: Equal-weight (5% par position)
- Rebalancement: Premier jour du mois

**Performance Typique (2015-2023):**
- Sharpe Ratio: ~0.8-1.2
- Max Drawdown: ~-30% à -40%
- Tendance à surperformer en bull markets

**Usage dans QuantConnect:**
1. Créer un nouveau projet dans QuantConnect Lab
2. Copier ce fichier dans main.py
3. Configurer les dates de backtest
4. Lancer le backtest

**Auteur:** CoursIA - QuantConnect AI Trading Series
**Notebook:** QC-Py-05-Universe-Selection.ipynb
**Version:** 1.0.0
"""

from AlgorithmImports import *


class MomentumUniverseSelection(QCAlgorithm):
    """
    Momentum Universe Selection Strategy

    Sélectionne les top 20 actions par momentum 12 mois.
    Rebalance mensuellement avec equal-weight allocation.
    """

    def Initialize(self):
        """
        Configuration initiale de l'algorithme.
        """
        # Configuration de base
        self.SetStartDate(2018, 1, 1)
        self.SetEndDate(2023, 12, 31)
        self.SetCash(100000)

        # Paramètres de la stratégie
        self.num_coarse = 500        # Nombre d'actions après filtrage coarse
        self.num_fine = 20           # Nombre d'actions finales
        self.momentum_period = 252   # Période momentum (12 mois ≈ 252 trading days)

        # Universe settings
        self.UniverseSettings.Resolution = Resolution.Daily
        self.UniverseSettings.Leverage = 1.0

        # Ajouter l'univers avec sélection Coarse + Fine
        self.AddUniverse(self.CoarseSelectionFunction, self.FineSelectionFunction)

        # Planifier le rebalancement mensuel
        self.Schedule.On(
            self.DateRules.MonthStart("SPY"),
            self.TimeRules.AfterMarketOpen("SPY", 30),
            self.Rebalance
        )

        # Variables de tracking
        self.selected_symbols = []
        self.rebalance_flag = False

        # Logging
        self.Debug("MomentumUniverseSelection initialized")
        self.Debug(f"Universe: Top {self.num_fine} by {self.momentum_period}-day momentum")

    def CoarseSelectionFunction(self, coarse):
        """
        Premier filtre: Liquidité et données fondamentales.

        Args:
            coarse: Liste de CoarseFundamental objects

        Returns:
            Liste de Symbol pour le filtrage Fine
        """
        # Filtrer: Prix > $5, DollarVolume significatif, HasFundamentalData
        filtered = [x for x in coarse
                   if x.Price > 5
                   and x.DollarVolume > 1000000
                   and x.HasFundamentalData]

        # Trier par dollar volume et prendre top N
        sorted_by_volume = sorted(filtered,
                                  key=lambda x: x.DollarVolume,
                                  reverse=True)[:self.num_coarse]

        return [x.Symbol for x in sorted_by_volume]

    def FineSelectionFunction(self, fine):
        """
        Second filtre: Calcul du momentum et sélection finale.

        Args:
            fine: Liste de FineFundamental objects

        Returns:
            Liste des Symbol top momentum
        """
        # Filtrer les entreprises avec Market Cap > $1B (large caps)
        large_caps = [x for x in fine
                     if x.MarketCap > 1e9]

        if len(large_caps) == 0:
            return []

        # Calculer le momentum pour chaque action
        momentum_scores = {}

        for security in large_caps:
            symbol = security.Symbol

            # Récupérer l'historique des prix
            history = self.History(symbol, self.momentum_period, Resolution.Daily)

            if len(history) >= self.momentum_period:
                # Momentum = (Prix actuel - Prix il y a N jours) / Prix il y a N jours
                try:
                    old_price = history['close'].iloc[0]
                    current_price = history['close'].iloc[-1]

                    if old_price > 0:
                        momentum = (current_price - old_price) / old_price
                        momentum_scores[symbol] = momentum
                except:
                    continue

        # Trier par momentum descendant
        sorted_by_momentum = sorted(momentum_scores.items(),
                                    key=lambda x: x[1],
                                    reverse=True)

        # Prendre les top N
        self.selected_symbols = [x[0] for x in sorted_by_momentum[:self.num_fine]]
        self.rebalance_flag = True

        self.Debug(f"Selected {len(self.selected_symbols)} symbols by momentum")

        return self.selected_symbols

    def Rebalance(self):
        """
        Rebalancement mensuel du portfolio.
        Appelé le premier jour de chaque mois.
        """
        if not self.rebalance_flag:
            return

        self.rebalance_flag = False

        # Calculer les poids (equal-weight)
        if len(self.selected_symbols) == 0:
            return

        weight = 1.0 / len(self.selected_symbols)

        # Liquider les positions qui ne sont plus dans l'univers
        for symbol in self.Portfolio.Keys:
            if symbol not in self.selected_symbols and self.Portfolio[symbol].Invested:
                self.Liquidate(symbol)
                self.Debug(f"SOLD: {symbol} (no longer in universe)")

        # Ajuster les positions
        for symbol in self.selected_symbols:
            self.SetHoldings(symbol, weight)

        self.Log(f"Rebalanced: {len(self.selected_symbols)} positions at {weight*100:.1f}% each")

    def OnSecuritiesChanged(self, changes):
        """
        Appelé quand l'univers change.

        Args:
            changes: SecurityChanges object
        """
        # Log les changements
        for security in changes.AddedSecurities:
            self.Debug(f"Added: {security.Symbol}")

        for security in changes.RemovedSecurities:
            # Liquider les positions supprimées de l'univers
            if self.Portfolio[security.Symbol].Invested:
                self.Liquidate(security.Symbol)
                self.Debug(f"Removed and liquidated: {security.Symbol}")

    def OnEndOfAlgorithm(self):
        """
        Appelé à la fin du backtest.
        """
        self.Log(f"Final Portfolio Value: ${self.Portfolio.TotalPortfolioValue:,.2f}")

        # Calculer le retour total
        initial_capital = 100000
        final_value = self.Portfolio.TotalPortfolioValue
        total_return = (final_value - initial_capital) / initial_capital

        self.Log(f"Total Return: {total_return:.2%}")
        self.Log(f"Number of positions: {sum(1 for x in self.Portfolio.Values if x.Invested)}")


# ==========================================
# VARIANTE: Momentum avec Filtre Volatilité
# ==========================================

class MomentumWithVolatilityFilter(QCAlgorithm):
    """
    Version avancée: Momentum filtré par volatilité.

    Amélioration:
    - Exclut les actions trop volatiles (>50% annualisé)
    - Pondération par volatilité inverse (risk parity)
    """

    def Initialize(self):
        self.SetStartDate(2018, 1, 1)
        self.SetEndDate(2023, 12, 31)
        self.SetCash(100000)

        self.num_coarse = 500
        self.num_fine = 20
        self.momentum_period = 252
        self.volatility_period = 60
        self.max_volatility = 0.50  # Max 50% annualized volatility

        self.UniverseSettings.Resolution = Resolution.Daily
        self.AddUniverse(self.CoarseSelectionFunction, self.FineSelectionFunction)

        self.Schedule.On(
            self.DateRules.MonthStart("SPY"),
            self.TimeRules.AfterMarketOpen("SPY", 30),
            self.Rebalance
        )

        self.selected_data = {}  # {symbol: (momentum, volatility)}

    def CoarseSelectionFunction(self, coarse):
        filtered = [x for x in coarse
                   if x.Price > 5
                   and x.DollarVolume > 1000000
                   and x.HasFundamentalData]

        sorted_by_volume = sorted(filtered,
                                  key=lambda x: x.DollarVolume,
                                  reverse=True)[:self.num_coarse]

        return [x.Symbol for x in sorted_by_volume]

    def FineSelectionFunction(self, fine):
        large_caps = [x for x in fine if x.MarketCap > 1e9]

        if len(large_caps) == 0:
            return []

        self.selected_data = {}

        for security in large_caps:
            symbol = security.Symbol
            history = self.History(symbol, self.momentum_period, Resolution.Daily)

            if len(history) >= self.momentum_period:
                try:
                    returns = history['close'].pct_change().dropna()

                    # Calculer momentum
                    old_price = history['close'].iloc[0]
                    current_price = history['close'].iloc[-1]
                    momentum = (current_price - old_price) / old_price

                    # Calculer volatilité annualisée
                    volatility = returns.std() * (252 ** 0.5)

                    # Filtrer par volatilité
                    if volatility < self.max_volatility and volatility > 0:
                        self.selected_data[symbol] = (momentum, volatility)
                except:
                    continue

        # Trier par momentum
        sorted_by_momentum = sorted(self.selected_data.items(),
                                    key=lambda x: x[1][0],
                                    reverse=True)[:self.num_fine]

        return [x[0] for x in sorted_by_momentum]

    def Rebalance(self):
        if len(self.selected_data) == 0:
            return

        # Calculer les poids par volatilité inverse (risk parity)
        symbols = list(self.selected_data.keys())[:self.num_fine]

        if len(symbols) == 0:
            return

        inv_volatilities = {s: 1.0 / self.selected_data[s][1]
                          for s in symbols if s in self.selected_data}

        total_inv_vol = sum(inv_volatilities.values())

        # Liquider positions hors univers
        for symbol in self.Portfolio.Keys:
            if symbol not in symbols and self.Portfolio[symbol].Invested:
                self.Liquidate(symbol)

        # Allouer avec pondération risk parity
        for symbol in symbols:
            if symbol in inv_volatilities:
                weight = inv_volatilities[symbol] / total_inv_vol
                self.SetHoldings(symbol, weight)

        self.Log(f"Rebalanced with risk parity: {len(symbols)} positions")

    def OnEndOfAlgorithm(self):
        self.Log(f"Final Value: ${self.Portfolio.TotalPortfolioValue:,.2f}")


# ==========================================
# NOTES
# ==========================================

"""
UTILISATION:

1. Copier MomentumUniverseSelection dans main.py sur QuantConnect
2. Ajuster les paramètres:
   - num_fine: Nombre de positions (20 par défaut)
   - momentum_period: Période lookback (252 = 12 mois)
3. Backtester sur différentes périodes

ATTENTION:
- Cette stratégie performe bien en bull markets
- Peut sous-performer significativement en bear markets (momentum crash)
- Le turnover mensuel génère des frais de transaction
- Considérer ajouter un filtre de tendance global (SPY > SMA 200)

AMÉLIORATIONS POSSIBLES:
- Ajouter filtre macro (SPY momentum positif)
- Combiner momentum court-terme et long-terme
- Ajouter stop-loss dynamique
- Implémenter position sizing par volatilité
"""
