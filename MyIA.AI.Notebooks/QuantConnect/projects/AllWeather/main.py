"""
All-Weather Portfolio Strategy - Production Algorithm

Stratégie multi-asset inspirée de Ray Dalio (Bridgewater).
Portfolio diversifié conçu pour performer dans tous les environnements économiques.

**Allocation:**
- 30% Actions (SPY)
- 40% Obligations long-terme (TLT)
- 15% Obligations intermédiaires (IEF)
- 7.5% Or (GLD)
- 7.5% Commodities (DBC ou GSG)

**Principe:**
- Diversification par classe d'actifs
- Rebalancement trimestriel
- Risk parity optionnel (pondération par volatilité)

**Performance Typique:**
- Sharpe Ratio: ~0.7-1.0
- Max Drawdown: ~-15% à -25%
- Volatilité annualisée: ~8-12%

**Usage:**
1. Créer un projet QuantConnect
2. Copier ce fichier dans main.py
3. Backtester

**Auteur:** CoursIA - QuantConnect AI Trading Series
**Notebook:** QC-Py-08-Multi-Asset-Strategies.ipynb
**Version:** 1.0.0
"""

from AlgorithmImports import *
import numpy as np


class AllWeatherPortfolio(QCAlgorithm):
    """
    All-Weather Portfolio Strategy

    Portfolio multi-asset avec rebalancement trimestriel.
    Conçu pour la stabilité dans tous les environnements de marché.
    """

    def Initialize(self):
        """
        Configuration initiale.
        """
        # Configuration de base
        self.SetStartDate(2015, 1, 1)
        self.SetEndDate(2023, 12, 31)
        self.SetCash(100000)

        # Définir les actifs et leurs allocations cibles
        self.target_allocations = {
            "SPY": 0.30,   # 30% Actions US (S&P 500)
            "TLT": 0.40,   # 40% Obligations long-terme (20+ ans)
            "IEF": 0.15,   # 15% Obligations intermédiaires (7-10 ans)
            "GLD": 0.075,  # 7.5% Or
            "DBC": 0.075   # 7.5% Commodities
        }

        # Ajouter les securities
        self.symbols = {}
        for ticker in self.target_allocations.keys():
            equity = self.AddEquity(ticker, Resolution.Daily)
            self.symbols[ticker] = equity.Symbol

        # Paramètres de rebalancement
        self.rebalance_threshold = 0.05  # Rebalancer si drift > 5%
        self.last_rebalance = None

        # Planifier le rebalancement trimestriel
        self.Schedule.On(
            self.DateRules.MonthStart("SPY"),
            self.TimeRules.AfterMarketOpen("SPY", 30),
            self.CheckRebalance
        )

        # Tracking
        self.rebalance_count = 0

        self.Debug("AllWeatherPortfolio initialized")
        self.Debug(f"Target allocations: {self.target_allocations}")

    def OnData(self, slice):
        """
        Appelé à chaque nouvelle donnée.
        Utilisé principalement pour le premier investissement.
        """
        # Premier investissement
        if not self.Portfolio.Invested:
            self.Rebalance()

    def CheckRebalance(self):
        """
        Vérifier si le rebalancement est nécessaire.
        Rebalance si:
        - C'est le premier jour du trimestre (janvier, avril, juillet, octobre)
        - OU si le drift dépasse le seuil
        """
        current_month = self.Time.month

        # Rebalancement trimestriel (janvier, avril, juillet, octobre)
        if current_month in [1, 4, 7, 10]:
            if self.last_rebalance is None or self.last_rebalance.month != current_month:
                self.Rebalance()
                return

        # Vérifier le drift
        if self.CheckDrift():
            self.Debug("Rebalancing due to drift threshold exceeded")
            self.Rebalance()

    def CheckDrift(self):
        """
        Vérifier si les allocations ont dérivé au-delà du seuil.

        Returns:
            True si rebalancement nécessaire
        """
        total_value = self.Portfolio.TotalPortfolioValue

        if total_value == 0:
            return False

        for ticker, target in self.target_allocations.items():
            symbol = self.symbols[ticker]
            current_value = self.Portfolio[symbol].HoldingsValue
            current_allocation = current_value / total_value

            drift = abs(current_allocation - target)

            if drift > self.rebalance_threshold:
                return True

        return False

    def Rebalance(self):
        """
        Rebalancer le portfolio vers les allocations cibles.
        """
        self.rebalance_count += 1
        self.last_rebalance = self.Time

        self.Log(f"=== REBALANCE #{self.rebalance_count} ({self.Time.strftime('%Y-%m-%d')}) ===")

        # Logger les allocations actuelles
        total_value = self.Portfolio.TotalPortfolioValue
        self.Log(f"Portfolio Value: ${total_value:,.2f}")

        for ticker, target in self.target_allocations.items():
            symbol = self.symbols[ticker]
            current_value = self.Portfolio[symbol].HoldingsValue
            current_pct = current_value / total_value if total_value > 0 else 0

            self.Log(f"  {ticker}: Current {current_pct:.1%} -> Target {target:.1%}")

            # Ajuster la position
            self.SetHoldings(symbol, target)

        self.Log("=" * 50)

    def OnEndOfAlgorithm(self):
        """
        Résumé final du backtest.
        """
        final_value = self.Portfolio.TotalPortfolioValue
        initial = 100000
        total_return = (final_value - initial) / initial

        # Calculer le CAGR
        years = (self.EndDate - self.StartDate).days / 365.25
        cagr = (final_value / initial) ** (1 / years) - 1

        self.Log("=" * 60)
        self.Log("ALL-WEATHER PORTFOLIO - FINAL SUMMARY")
        self.Log("=" * 60)
        self.Log(f"Initial Capital: ${initial:,.2f}")
        self.Log(f"Final Value: ${final_value:,.2f}")
        self.Log(f"Total Return: {total_return:.2%}")
        self.Log(f"CAGR: {cagr:.2%}")
        self.Log(f"Total Rebalances: {self.rebalance_count}")
        self.Log("=" * 60)


# ==========================================
# VARIANTE: Risk Parity All-Weather
# ==========================================

class RiskParityAllWeather(QCAlgorithm):
    """
    All-Weather avec pondération Risk Parity.

    Les actifs sont pondérés par l'inverse de leur volatilité
    pour égaliser la contribution au risque.
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.SetEndDate(2023, 12, 31)
        self.SetCash(100000)

        # Assets
        self.tickers = ["SPY", "TLT", "IEF", "GLD", "DBC"]

        self.symbols = {}
        for ticker in self.tickers:
            equity = self.AddEquity(ticker, Resolution.Daily)
            self.symbols[ticker] = equity.Symbol

        # Volatility lookback
        self.volatility_period = 60  # 60 jours

        # Rebalancement mensuel
        self.Schedule.On(
            self.DateRules.MonthStart("SPY"),
            self.TimeRules.AfterMarketOpen("SPY", 30),
            self.Rebalance
        )

        # Warm-up
        self.SetWarmUp(self.volatility_period, Resolution.Daily)

    def Rebalance(self):
        """
        Rebalancer avec pondération risk parity.
        """
        if self.IsWarmingUp:
            return

        # Calculer les volatilités
        volatilities = {}

        for ticker in self.tickers:
            symbol = self.symbols[ticker]
            history = self.History(symbol, self.volatility_period, Resolution.Daily)

            if len(history) < self.volatility_period:
                continue

            returns = history['close'].pct_change().dropna()
            vol = returns.std() * np.sqrt(252)  # Annualisée

            if vol > 0:
                volatilities[ticker] = vol

        if len(volatilities) == 0:
            return

        # Calculer les poids (volatilité inverse)
        inv_vols = {t: 1.0 / v for t, v in volatilities.items()}
        total_inv_vol = sum(inv_vols.values())

        weights = {t: iv / total_inv_vol for t, iv in inv_vols.items()}

        # Logger et appliquer
        self.Log(f"=== RISK PARITY REBALANCE ({self.Time.strftime('%Y-%m-%d')}) ===")

        for ticker, weight in weights.items():
            vol = volatilities.get(ticker, 0)
            self.Log(f"  {ticker}: Vol={vol:.1%}, Weight={weight:.1%}")
            self.SetHoldings(self.symbols[ticker], weight)

        self.Log("=" * 50)

    def OnEndOfAlgorithm(self):
        final = self.Portfolio.TotalPortfolioValue
        self.Log(f"Final Value: ${final:,.2f}")
        self.Log(f"Total Return: {(final - 100000) / 100000:.2%}")


# ==========================================
# VARIANTE: Tactical All-Weather
# ==========================================

class TacticalAllWeather(QCAlgorithm):
    """
    All-Weather avec overlay tactique.

    Réduit l'exposition aux actifs sous leur SMA 200.
    Augmente le cash en période de stress.
    """

    def Initialize(self):
        self.SetStartDate(2015, 1, 1)
        self.SetEndDate(2023, 12, 31)
        self.SetCash(100000)

        # Base allocations
        self.base_allocations = {
            "SPY": 0.30,
            "TLT": 0.40,
            "IEF": 0.15,
            "GLD": 0.075,
            "DBC": 0.075
        }

        self.symbols = {}
        self.sma = {}

        for ticker in self.base_allocations.keys():
            equity = self.AddEquity(ticker, Resolution.Daily)
            self.symbols[ticker] = equity.Symbol

            # SMA 200 pour chaque actif
            self.sma[ticker] = self.SMA(equity.Symbol, 200, Resolution.Daily)

        # Rebalancement mensuel
        self.Schedule.On(
            self.DateRules.MonthStart("SPY"),
            self.TimeRules.AfterMarketOpen("SPY", 30),
            self.TacticalRebalance
        )

        self.SetWarmUp(200, Resolution.Daily)

    def TacticalRebalance(self):
        """
        Rebalancement tactique.
        Réduit l'allocation si prix < SMA 200.
        """
        if self.IsWarmingUp:
            return

        self.Log(f"=== TACTICAL REBALANCE ({self.Time.strftime('%Y-%m-%d')}) ===")

        tactical_allocations = {}
        total_tactical = 0

        for ticker, base_weight in self.base_allocations.items():
            symbol = self.symbols[ticker]
            sma = self.sma[ticker]

            if not sma.IsReady:
                tactical_allocations[ticker] = 0
                continue

            current_price = self.Securities[symbol].Price
            sma_value = sma.Current.Value

            # Si prix > SMA: allocation complète
            # Si prix < SMA: allocation réduite de 50%
            if current_price > sma_value:
                tactical_weight = base_weight
                signal = "BULLISH"
            else:
                tactical_weight = base_weight * 0.5
                signal = "BEARISH"

            tactical_allocations[ticker] = tactical_weight
            total_tactical += tactical_weight

            self.Log(f"  {ticker}: {signal}, Price={current_price:.2f}, "
                    f"SMA200={sma_value:.2f}, Weight={tactical_weight:.1%}")

        # La différence va en cash (implicitement)
        cash_weight = 1.0 - total_tactical
        self.Log(f"  CASH: {cash_weight:.1%}")

        # Appliquer les allocations
        for ticker, weight in tactical_allocations.items():
            self.SetHoldings(self.symbols[ticker], weight)

        self.Log("=" * 50)

    def OnEndOfAlgorithm(self):
        final = self.Portfolio.TotalPortfolioValue
        self.Log(f"Final Value: ${final:,.2f}")


# ==========================================
# NOTES
# ==========================================

"""
ALL-WEATHER PORTFOLIO (Ray Dalio / Bridgewater):

Principes fondamentaux:
1. Diversification par environnement économique:
   - Croissance en hausse: Actions performantes
   - Croissance en baisse: Bonds performants
   - Inflation en hausse: Or et commodities performants
   - Inflation en baisse: Bonds performants

2. Allocation standard:
   - 30% Actions (SPY)
   - 40% Obligations long-terme (TLT)
   - 15% Obligations moyen-terme (IEF)
   - 7.5% Or (GLD)
   - 7.5% Commodities (DBC/GSG)

3. Risk Parity:
   - Pondérer par volatilité inverse
   - Objectif: Contribution égale au risque
   - Favorise les obligations (faible vol) vs actions (haute vol)

4. Tactical overlay:
   - Réduire l'exposition quand prix < SMA 200
   - Augmente le cash en période de stress
   - Réduit le drawdown au prix de rendement moindre

LIMITATIONS:
- Underperform en bull market fort (trop de bonds)
- Sensible aux hausses de taux (bonds baissent)
- Commodities peuvent sous-performer longtemps
- Corrélations changent en période de stress

ETFs ALTERNATIVES:
- Actions: VTI (total market), QQQ (tech)
- Bonds: VGLT (long gov), BND (total bond)
- Or: IAU (alternative à GLD)
- Commodities: GSG, PDBC (moins de contango)
"""
