"""
Covered Call Strategy - Production Algorithm

Stratégie de vente de calls couverts sur SPY pour générer du premium.
Achète 100 actions SPY et vend un call OTM mensuel.

**Principe:**
- Détenir 100 actions du sous-jacent (SPY)
- Vendre un call OTM (delta ~0.30) à expiration ~30 jours
- Roll avant expiration (7 jours ou si ITM profond)
- Collecter le premium régulièrement

**Performance Typique:**
- Rendement annuel: 8-12% (premium + appréciation limitée)
- Max Drawdown: Similaire au sous-jacent
- Sharpe Ratio: ~0.6-0.9

**Usage:**
1. Créer un projet QuantConnect
2. Copier ce fichier dans main.py
3. Backtester

**Auteur:** CoursIA - QuantConnect AI Trading Series
**Notebook:** QC-Py-06-Options-Trading.ipynb
**Version:** 1.0.0
"""

from AlgorithmImports import *
from datetime import timedelta


class CoveredCallStrategy(QCAlgorithm):
    """
    Covered Call Strategy sur SPY

    Achète le sous-jacent et vend des calls OTM pour générer du premium.
    """

    def Initialize(self):
        """
        Configuration initiale.
        """
        # Configuration de base
        self.SetStartDate(2020, 1, 1)
        self.SetEndDate(2023, 12, 31)
        self.SetCash(100000)

        # Ajouter l'equity sous-jacente
        equity = self.AddEquity("SPY", Resolution.Minute)
        self.underlying = equity.Symbol

        # Ajouter les options
        option = self.AddOption("SPY", Resolution.Minute)
        self.option_symbol = option.Symbol

        # Filtrer les options: strikes proches, expirations 20-45 jours
        option.SetFilter(
            minStrike=-10,      # 10 strikes en dessous
            maxStrike=10,       # 10 strikes au dessus
            minExpiry=timedelta(days=20),
            maxExpiry=timedelta(days=45)
        )

        # Paramètres de la stratégie
        self.target_delta = 0.30        # Delta cible pour le call vendu
        self.days_to_roll = 7           # Jours avant expiration pour roll
        self.shares_per_contract = 100  # 1 contrat = 100 actions

        # Variables de tracking
        self.current_call = None        # Contrat call actuel
        self.premium_collected = 0      # Premium total collecté
        self.trades_count = 0           # Nombre de trades

        # Planifier la vérification quotidienne
        self.Schedule.On(
            self.DateRules.EveryDay(self.underlying),
            self.TimeRules.AfterMarketOpen(self.underlying, 30),
            self.ManagePosition
        )

        self.Debug("CoveredCallStrategy initialized")

    def OnData(self, slice):
        """
        Appelé à chaque nouvelle donnée.
        """
        # La logique principale est dans ManagePosition (scheduled)
        pass

    def ManagePosition(self):
        """
        Gestion quotidienne de la position.
        1. Acheter le sous-jacent si pas déjà détenu
        2. Vendre un call si pas de position options
        3. Roll si proche de l'expiration
        """
        # 1. S'assurer qu'on détient le sous-jacent
        if not self.Portfolio[self.underlying].Invested:
            # Acheter assez d'actions pour couvrir 1 contrat
            quantity = self.shares_per_contract
            self.MarketOrder(self.underlying, quantity)
            self.Debug(f"Bought {quantity} shares of {self.underlying}")
            return  # Attendre le prochain jour pour vendre le call

        # 2. Vérifier si on a un call vendu
        if self.current_call is None:
            self.SellCall()
            return

        # 3. Vérifier si on doit roll
        self.CheckRoll()

    def SellCall(self):
        """
        Vendre un call OTM avec delta proche de target_delta.
        """
        # Obtenir la chaîne d'options
        chain = self.CurrentSlice.OptionChains.get(self.option_symbol, None)

        if chain is None:
            return

        # Filtrer pour les calls seulement
        calls = [x for x in chain if x.Right == OptionRight.Call]

        if len(calls) == 0:
            return

        # Prix actuel du sous-jacent
        underlying_price = self.Securities[self.underlying].Price

        # Trouver le call avec delta le plus proche de target_delta
        # et OTM (strike > prix actuel)
        otm_calls = [x for x in calls if x.Strike > underlying_price]

        if len(otm_calls) == 0:
            return

        # Sélectionner par delta (ou par strike si Greeks non disponibles)
        best_call = None
        best_delta_diff = float('inf')

        for call in otm_calls:
            if call.Greeks.Delta != 0:
                delta_diff = abs(call.Greeks.Delta - self.target_delta)
                if delta_diff < best_delta_diff:
                    best_delta_diff = delta_diff
                    best_call = call

        # Fallback: si pas de Greeks, prendre le premier OTM à ~30 jours
        if best_call is None:
            # Filtrer par expiration ~30 jours
            target_expiry = self.Time + timedelta(days=30)
            sorted_calls = sorted(otm_calls,
                                 key=lambda x: abs((x.Expiry - target_expiry).days))
            if len(sorted_calls) > 0:
                # Prendre un strike ~2% OTM
                target_strike = underlying_price * 1.02
                best_call = min(sorted_calls[:5],
                               key=lambda x: abs(x.Strike - target_strike))

        if best_call is None:
            return

        # Vendre le call (1 contrat = -1 car on vend)
        self.MarketOrder(best_call.Symbol, -1)
        self.current_call = best_call.Symbol

        # Calculer et logger le premium
        premium = best_call.LastPrice * self.shares_per_contract
        self.premium_collected += premium
        self.trades_count += 1

        self.Log(f"SOLD CALL: Strike={best_call.Strike}, "
                f"Expiry={best_call.Expiry.strftime('%Y-%m-%d')}, "
                f"Premium=${premium:.2f}, "
                f"Delta={best_call.Greeks.Delta:.3f}")

    def CheckRoll(self):
        """
        Vérifier si on doit roll la position.
        Roll si:
        - Moins de days_to_roll jours avant expiration
        - Le call est ITM profond (strike < 98% du prix)
        """
        if self.current_call is None:
            return

        # Obtenir les infos du contrat actuel
        if self.current_call not in self.Securities:
            self.current_call = None
            return

        option = self.Securities[self.current_call]

        # Vérifier l'expiration
        days_to_expiry = (option.Expiry - self.Time).days

        # Vérifier si ITM profond
        underlying_price = self.Securities[self.underlying].Price
        is_deep_itm = option.StrikePrice < underlying_price * 0.98

        should_roll = days_to_expiry <= self.days_to_roll or is_deep_itm

        if should_roll:
            self.RollPosition(option, days_to_expiry, is_deep_itm)

    def RollPosition(self, current_option, days_to_expiry, is_deep_itm):
        """
        Roll la position vers le prochain mois.
        """
        reason = "Near expiry" if days_to_expiry <= self.days_to_roll else "Deep ITM"

        # Racheter le call vendu
        self.MarketOrder(self.current_call, 1)  # +1 pour fermer la position short

        cost_to_close = current_option.Price * self.shares_per_contract

        self.Log(f"ROLL ({reason}): Closed {self.current_call.Value}, "
                f"Cost=${cost_to_close:.2f}")

        self.current_call = None

        # Vendre un nouveau call (sera fait au prochain ManagePosition)

    def OnOrderEvent(self, orderEvent):
        """
        Appelé quand un ordre est exécuté.
        """
        if orderEvent.Status == OrderStatus.Filled:
            self.Debug(f"Order filled: {orderEvent.Symbol}, "
                      f"Qty={orderEvent.FillQuantity}, "
                      f"Price=${orderEvent.FillPrice:.2f}")

    def OnEndOfAlgorithm(self):
        """
        Résumé final.
        """
        final_value = self.Portfolio.TotalPortfolioValue
        initial_capital = 100000
        total_return = (final_value - initial_capital) / initial_capital

        self.Log("=" * 60)
        self.Log("COVERED CALL STRATEGY - FINAL SUMMARY")
        self.Log("=" * 60)
        self.Log(f"Final Portfolio Value: ${final_value:,.2f}")
        self.Log(f"Total Return: {total_return:.2%}")
        self.Log(f"Total Premium Collected: ${self.premium_collected:,.2f}")
        self.Log(f"Number of Trades: {self.trades_count}")
        self.Log("=" * 60)


# ==========================================
# VARIANTE: Iron Condor Strategy
# ==========================================

class IronCondorStrategy(QCAlgorithm):
    """
    Iron Condor Strategy sur SPY

    Stratégie neutre pour marchés latéraux.
    Vend un put spread + call spread pour collecter du premium.
    """

    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetEndDate(2023, 12, 31)
        self.SetCash(100000)

        equity = self.AddEquity("SPY", Resolution.Minute)
        self.underlying = equity.Symbol

        option = self.AddOption("SPY", Resolution.Minute)
        self.option_symbol = option.Symbol

        option.SetFilter(
            minStrike=-20,
            maxStrike=20,
            minExpiry=timedelta(days=25),
            maxExpiry=timedelta(days=35)
        )

        # Paramètres Iron Condor
        self.put_delta = -0.15      # Delta du short put
        self.call_delta = 0.15      # Delta du short call
        self.wing_width = 5         # Largeur des wings ($5)

        self.current_position = None
        self.premium_collected = 0

        self.Schedule.On(
            self.DateRules.EveryDay(self.underlying),
            self.TimeRules.AfterMarketOpen(self.underlying, 30),
            self.ManageCondor
        )

    def ManageCondor(self):
        """
        Gestion quotidienne de l'Iron Condor.
        """
        if self.current_position is not None:
            # Vérifier si proche expiration
            return

        chain = self.CurrentSlice.OptionChains.get(self.option_symbol, None)
        if chain is None:
            return

        underlying_price = self.Securities[self.underlying].Price

        # Séparer calls et puts
        calls = [x for x in chain if x.Right == OptionRight.Call]
        puts = [x for x in chain if x.Right == OptionRight.Put]

        if len(calls) < 2 or len(puts) < 2:
            return

        # Trouver expiration ~30 jours
        target_expiry = self.Time + timedelta(days=30)

        # Filtrer par expiration
        calls_30d = [x for x in calls
                    if abs((x.Expiry - target_expiry).days) < 5]
        puts_30d = [x for x in puts
                   if abs((x.Expiry - target_expiry).days) < 5]

        if len(calls_30d) < 2 or len(puts_30d) < 2:
            return

        # Trouver les strikes pour l'Iron Condor
        # Short call: ~2% OTM
        short_call_strike = underlying_price * 1.02
        short_call = min(calls_30d,
                        key=lambda x: abs(x.Strike - short_call_strike))

        # Long call: short_call + wing_width
        long_call_strike = short_call.Strike + self.wing_width
        long_calls = [x for x in calls_30d if x.Strike >= long_call_strike]
        if len(long_calls) == 0:
            return
        long_call = min(long_calls, key=lambda x: x.Strike)

        # Short put: ~2% OTM
        short_put_strike = underlying_price * 0.98
        short_put = min(puts_30d,
                       key=lambda x: abs(x.Strike - short_put_strike))

        # Long put: short_put - wing_width
        long_put_strike = short_put.Strike - self.wing_width
        long_puts = [x for x in puts_30d if x.Strike <= long_put_strike]
        if len(long_puts) == 0:
            return
        long_put = max(long_puts, key=lambda x: x.Strike)

        # Exécuter l'Iron Condor
        # Sell short call, buy long call
        self.MarketOrder(short_call.Symbol, -1)
        self.MarketOrder(long_call.Symbol, 1)

        # Sell short put, buy long put
        self.MarketOrder(short_put.Symbol, -1)
        self.MarketOrder(long_put.Symbol, 1)

        # Calculer le premium net
        premium = ((short_call.LastPrice + short_put.LastPrice) -
                  (long_call.LastPrice + long_put.LastPrice)) * 100
        self.premium_collected += premium

        self.current_position = {
            'short_call': short_call.Symbol,
            'long_call': long_call.Symbol,
            'short_put': short_put.Symbol,
            'long_put': long_put.Symbol,
            'expiry': short_call.Expiry
        }

        self.Log(f"IRON CONDOR: Collected ${premium:.2f}")
        self.Log(f"  Short Put: {short_put.Strike}, Long Put: {long_put.Strike}")
        self.Log(f"  Short Call: {short_call.Strike}, Long Call: {long_call.Strike}")

    def OnEndOfAlgorithm(self):
        self.Log(f"Total Premium Collected: ${self.premium_collected:,.2f}")
        self.Log(f"Final Value: ${self.Portfolio.TotalPortfolioValue:,.2f}")


# ==========================================
# NOTES
# ==========================================

"""
COVERED CALL - POINTS CLÉS:

1. Fonctionnement:
   - Détenir 100 actions du sous-jacent
   - Vendre 1 call OTM (droit de vendre au strike)
   - Si le prix monte > strike: actions appelées, profit limité
   - Si le prix baisse: garder le premium, subir la perte sur actions

2. Sélection du Strike:
   - Delta 0.30 ≈ 30% probabilité ITM
   - Plus OTM = moins de premium mais plus de upside
   - Plus proche ATM = plus de premium mais risque d'assignment

3. Roll Strategy:
   - Roll 7 jours avant expiration
   - Roll si deep ITM pour éviter early assignment
   - Roll "up and out" si très bullish

4. Risques:
   - Perte illimitée à la baisse (comme détenir l'action)
   - Upside limité au strike
   - Early assignment possible

IRON CONDOR - POINTS CLÉS:

1. Profit max = Premium collecté
2. Perte max = Largeur des wings - Premium
3. Break-even = Short strikes ± Premium
4. Idéal en faible volatilité, marchés range-bound
"""
