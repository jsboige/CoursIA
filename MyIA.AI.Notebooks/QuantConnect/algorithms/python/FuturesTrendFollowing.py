"""
Futures Trend Following Strategy - Production Algorithm

Stratégie de suivi de tendance sur les futures E-mini S&P 500 (ES).
Utilise un Donchian Channel breakout avec rollover automatique.

**Principe:**
- Entry: Breakout du canal Donchian 20 jours (long ou short)
- Exit: Breakout inverse du canal 10 jours
- Position sizing: 1% risque par trade
- Rollover: Automatique avant expiration

**Performance Typique:**
- Sharpe Ratio: ~0.5-0.8
- Max Drawdown: ~-25% à -35%
- Win Rate: ~35-45% (mais gros gains sur les wins)

**Usage:**
1. Créer un projet QuantConnect
2. Copier ce fichier dans main.py
3. Backtester

**Auteur:** CoursIA - QuantConnect AI Trading Series
**Notebook:** QC-Py-07-Futures-Forex.ipynb
**Version:** 1.0.0
"""

from AlgorithmImports import *
from datetime import timedelta
import numpy as np


class FuturesTrendFollowing(QCAlgorithm):
    """
    Trend Following Strategy sur ES Futures

    Utilise Donchian Channel breakout pour capturer les tendances.
    Gère automatiquement le rollover des contrats.
    """

    def Initialize(self):
        """
        Configuration initiale.
        """
        # Configuration de base
        self.SetStartDate(2019, 1, 1)
        self.SetEndDate(2023, 12, 31)
        self.SetCash(100000)

        # Ajouter le future ES (S&P 500 E-mini)
        future = self.AddFuture(
            Futures.Indices.SP500EMini,
            Resolution.Daily,
            extendedMarketHours=False,
            dataNormalizationMode=DataNormalizationMode.BackwardsRatio
        )

        # Filtrer: contrats dans les 90 prochains jours
        future.SetFilter(timedelta(0), timedelta(90))

        self.future_symbol = future.Symbol

        # Paramètres de la stratégie
        self.entry_period = 20      # Donchian entry channel
        self.exit_period = 10       # Donchian exit channel
        self.risk_percent = 0.01    # 1% risque par trade
        self.es_multiplier = 50     # Multiplicateur ES ($50 par point)

        # Variables de tracking
        self.current_contract = None
        self.entry_high = None      # Plus haut sur entry_period
        self.entry_low = None       # Plus bas sur entry_period
        self.exit_high = None       # Plus haut sur exit_period
        self.exit_low = None        # Plus bas sur exit_period
        self.position_direction = 0  # 1=long, -1=short, 0=flat
        self.entry_price = None

        # Rolling windows pour les canaux
        self.high_window = RollingWindow[float](self.entry_period)
        self.low_window = RollingWindow[float](self.entry_period)

        # Warm-up
        self.SetWarmUp(self.entry_period * 2, Resolution.Daily)

        self.Debug("FuturesTrendFollowing initialized")
        self.Debug(f"Entry Channel: {self.entry_period} days, Exit Channel: {self.exit_period} days")

    def OnData(self, slice):
        """
        Logique de trading principale.
        """
        if self.IsWarmingUp:
            return

        # Obtenir le contrat front-month
        for chain in slice.FutureChains.Values:
            if len(chain) == 0:
                continue

            # Sélectionner le contrat avec la plus proche expiration (front-month)
            sorted_by_expiry = sorted(chain, key=lambda x: x.Expiry)
            front_contract = sorted_by_expiry[0]

            # Vérifier si on doit rollover
            if self.current_contract is not None:
                if front_contract.Symbol != self.current_contract:
                    self.Rollover(front_contract.Symbol)

            self.current_contract = front_contract.Symbol

            # Mettre à jour les rolling windows
            self.high_window.Add(front_contract.High)
            self.low_window.Add(front_contract.Low)

            if not self.high_window.IsReady:
                return

            # Calculer les canaux Donchian
            self.CalculateChannels()

            # Prix actuel
            current_price = front_contract.Close

            # Logique de trading
            self.TradingLogic(current_price)

    def CalculateChannels(self):
        """
        Calculer les canaux Donchian.
        """
        # Entry channel (20 périodes)
        highs_entry = [self.high_window[i] for i in range(self.entry_period)]
        lows_entry = [self.low_window[i] for i in range(self.entry_period)]

        self.entry_high = max(highs_entry)
        self.entry_low = min(lows_entry)

        # Exit channel (10 périodes)
        highs_exit = [self.high_window[i] for i in range(min(self.exit_period, self.high_window.Count))]
        lows_exit = [self.low_window[i] for i in range(min(self.exit_period, self.low_window.Count))]

        self.exit_high = max(highs_exit)
        self.exit_low = min(lows_exit)

    def TradingLogic(self, current_price):
        """
        Logique d'entrée et sortie.
        """
        if self.current_contract is None:
            return

        # Si pas de position
        if self.position_direction == 0:
            # Breakout haussier
            if current_price > self.entry_high:
                quantity = self.CalculatePositionSize(current_price, is_long=True)
                if quantity > 0:
                    self.MarketOrder(self.current_contract, quantity)
                    self.position_direction = 1
                    self.entry_price = current_price
                    self.Log(f"LONG: {quantity} contracts at {current_price:.2f}")

            # Breakout baissier
            elif current_price < self.entry_low:
                quantity = self.CalculatePositionSize(current_price, is_long=False)
                if quantity > 0:
                    self.MarketOrder(self.current_contract, -quantity)
                    self.position_direction = -1
                    self.entry_price = current_price
                    self.Log(f"SHORT: {quantity} contracts at {current_price:.2f}")

        # Si position longue
        elif self.position_direction == 1:
            # Exit sur breakout du canal exit bas
            if current_price < self.exit_low:
                self.Liquidate(self.current_contract)
                pnl = (current_price - self.entry_price) * self.es_multiplier
                self.Log(f"EXIT LONG at {current_price:.2f}, PnL per contract: ${pnl:.2f}")
                self.position_direction = 0
                self.entry_price = None

        # Si position short
        elif self.position_direction == -1:
            # Exit sur breakout du canal exit haut
            if current_price > self.exit_high:
                self.Liquidate(self.current_contract)
                pnl = (self.entry_price - current_price) * self.es_multiplier
                self.Log(f"EXIT SHORT at {current_price:.2f}, PnL per contract: ${pnl:.2f}")
                self.position_direction = 0
                self.entry_price = None

    def CalculatePositionSize(self, price, is_long):
        """
        Calculer la taille de position basée sur le risque.
        """
        account_value = self.Portfolio.TotalPortfolioValue
        risk_amount = account_value * self.risk_percent

        # Stop distance (canal opposé)
        if is_long:
            stop_distance = price - self.exit_low
        else:
            stop_distance = self.exit_high - price

        if stop_distance <= 0:
            return 0

        # Risque par contrat = stop_distance * multiplier
        risk_per_contract = stop_distance * self.es_multiplier

        # Nombre de contrats
        quantity = int(risk_amount / risk_per_contract)

        # Limiter à un nombre raisonnable
        max_contracts = int(account_value / (price * self.es_multiplier * 0.1))  # 10% marge
        quantity = min(quantity, max_contracts, 10)  # Max 10 contrats

        return max(quantity, 1)  # Au moins 1 contrat

    def Rollover(self, new_contract):
        """
        Rollover vers le nouveau contrat front-month.
        """
        if not self.Portfolio[self.current_contract].Invested:
            self.Debug(f"Rollover: No position to roll, switching to {new_contract}")
            return

        # Obtenir la position actuelle
        current_quantity = self.Portfolio[self.current_contract].Quantity

        # Fermer l'ancienne position
        self.Liquidate(self.current_contract)

        # Ouvrir la même position sur le nouveau contrat
        self.MarketOrder(new_contract, current_quantity)

        self.Log(f"ROLLOVER: {self.current_contract} -> {new_contract}, "
                f"Quantity: {current_quantity}")

    def OnSecuritiesChanged(self, changes):
        """
        Gestion des changements de securities.
        """
        for security in changes.AddedSecurities:
            if security.Type == SecurityType.Future:
                self.Debug(f"Future added: {security.Symbol}, Expiry: {security.Expiry}")

        for security in changes.RemovedSecurities:
            if security.Type == SecurityType.Future:
                self.Debug(f"Future removed: {security.Symbol}")

    def OnEndOfAlgorithm(self):
        """
        Résumé final.
        """
        self.Log("=" * 60)
        self.Log("FUTURES TREND FOLLOWING - FINAL SUMMARY")
        self.Log("=" * 60)
        self.Log(f"Final Portfolio Value: ${self.Portfolio.TotalPortfolioValue:,.2f}")

        initial = 100000
        final = self.Portfolio.TotalPortfolioValue
        total_return = (final - initial) / initial

        self.Log(f"Total Return: {total_return:.2%}")
        self.Log("=" * 60)


# ==========================================
# VARIANTE: Multi-Futures Trend Following
# ==========================================

class MultiFuturesTrendFollowing(QCAlgorithm):
    """
    Trend Following sur plusieurs marchés futures.

    Diversification sur: ES (équités), GC (or), CL (pétrole), ZB (bonds)
    """

    def Initialize(self):
        self.SetStartDate(2019, 1, 1)
        self.SetEndDate(2023, 12, 31)
        self.SetCash(100000)

        # Définir les futures à trader
        self.futures_config = {
            Futures.Indices.SP500EMini: {'multiplier': 50, 'weight': 0.25},
            Futures.Metals.Gold: {'multiplier': 100, 'weight': 0.25},
            Futures.Energies.CrudeOilWTI: {'multiplier': 1000, 'weight': 0.25},
            Futures.Financials.Y10TreasuryNote: {'multiplier': 1000, 'weight': 0.25}
        }

        self.futures = {}
        self.positions = {}
        self.channels = {}

        for future_symbol, config in self.futures_config.items():
            future = self.AddFuture(
                future_symbol,
                Resolution.Daily,
                dataNormalizationMode=DataNormalizationMode.BackwardsRatio
            )
            future.SetFilter(timedelta(0), timedelta(90))

            self.futures[future.Symbol] = {
                'config': config,
                'contract': None,
                'high_window': RollingWindow[float](20),
                'low_window': RollingWindow[float](20),
                'direction': 0
            }

        self.entry_period = 20
        self.exit_period = 10
        self.risk_percent = 0.005  # 0.5% par trade (diversifié)

        self.SetWarmUp(self.entry_period * 2, Resolution.Daily)

    def OnData(self, slice):
        if self.IsWarmingUp:
            return

        for chain in slice.FutureChains.Values:
            if len(chain) == 0:
                continue

            # Identifier le future
            future_symbol = chain.Key
            if future_symbol not in self.futures:
                continue

            future_data = self.futures[future_symbol]

            # Front-month contract
            sorted_by_expiry = sorted(chain, key=lambda x: x.Expiry)
            front = sorted_by_expiry[0]

            # Update contract
            future_data['contract'] = front.Symbol

            # Update windows
            future_data['high_window'].Add(front.High)
            future_data['low_window'].Add(front.Low)

            if not future_data['high_window'].IsReady:
                continue

            # Calculate channels
            highs = [future_data['high_window'][i] for i in range(self.entry_period)]
            lows = [future_data['low_window'][i] for i in range(self.entry_period)]

            entry_high = max(highs)
            entry_low = min(lows)

            exit_highs = [future_data['high_window'][i] for i in range(self.exit_period)]
            exit_lows = [future_data['low_window'][i] for i in range(self.exit_period)]

            exit_high = max(exit_highs)
            exit_low = min(exit_lows)

            current_price = front.Close

            # Trading logic
            direction = future_data['direction']
            contract = future_data['contract']
            config = future_data['config']

            if direction == 0:
                # Entry signals
                if current_price > entry_high:
                    qty = self.CalculateQuantity(current_price, config['multiplier'])
                    self.MarketOrder(contract, qty)
                    future_data['direction'] = 1
                    self.Log(f"LONG {contract}: {qty} at {current_price}")

                elif current_price < entry_low:
                    qty = self.CalculateQuantity(current_price, config['multiplier'])
                    self.MarketOrder(contract, -qty)
                    future_data['direction'] = -1
                    self.Log(f"SHORT {contract}: {qty} at {current_price}")

            elif direction == 1:
                if current_price < exit_low:
                    self.Liquidate(contract)
                    future_data['direction'] = 0
                    self.Log(f"EXIT LONG {contract} at {current_price}")

            elif direction == -1:
                if current_price > exit_high:
                    self.Liquidate(contract)
                    future_data['direction'] = 0
                    self.Log(f"EXIT SHORT {contract} at {current_price}")

    def CalculateQuantity(self, price, multiplier):
        account = self.Portfolio.TotalPortfolioValue
        risk = account * self.risk_percent
        risk_per_contract = price * 0.02 * multiplier  # ~2% stop
        qty = int(risk / risk_per_contract)
        return max(qty, 1)

    def OnEndOfAlgorithm(self):
        self.Log(f"Final Value: ${self.Portfolio.TotalPortfolioValue:,.2f}")


# ==========================================
# NOTES
# ==========================================

"""
DONCHIAN CHANNEL BREAKOUT:

1. Entry:
   - Long quand prix > max(High, 20 jours)
   - Short quand prix < min(Low, 20 jours)

2. Exit:
   - Exit long quand prix < min(Low, 10 jours)
   - Exit short quand prix > max(High, 10 jours)

3. Position Sizing:
   - Risque 1% du capital par trade
   - Stop = canal opposé
   - Quantity = RiskAmount / (StopDistance * Multiplier)

FUTURES SPECIFICATIONS:
- ES (E-mini S&P 500): $50 per point, tick = 0.25 ($12.50)
- GC (Gold): $100 per oz, tick = 0.10 ($10)
- CL (Crude Oil): $1000 per contract (1000 barrels), tick = 0.01 ($10)
- ZB (30Y Bonds): $1000 per point, tick = 1/32 ($31.25)

ROLLOVER:
- Typiquement 5-7 jours avant expiration
- Coût du roll = différence entre contrats
- Contango/Backwardation affecte les returns long-terme
"""
