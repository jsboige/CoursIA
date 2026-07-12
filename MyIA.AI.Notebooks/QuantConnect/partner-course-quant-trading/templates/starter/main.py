# =============================================================================
# Strategie Starter : Croisement EMA sur BTCUSDT
# =============================================================================
# Principe : Acheter quand l'EMA rapide croise au-dessus de l'EMA lente
# (golden cross), et vendre quand elle croise en dessous (death cross).
# C'est l'une des strategies les plus simples en trading algorithmique.
# =============================================================================

from AlgorithmImports import *


class StarterEMACrossAlgorithm(QCAlgorithm):
    """Strategie de croisement de moyennes mobiles exponentielles (EMA)."""

    def Initialize(self):
        """Configuration initiale de l'algorithme."""

        # --- Periode de backtest ---
        self.SetStartDate(2023, 1, 1)
        self.SetEndDate(2024, 12, 31)

        # --- Capital initial en USDT ---
        self.SetCash(10000)

        # --- Ajout de l'actif : Bitcoin sur Binance, donnees horaires ---
        # AddCrypto retourne un objet Security ; on garde le Symbol pour la suite
        crypto = self.AddCrypto("BTCUSDT", Resolution.Hour, Market.Binance)
        self.btc = crypto.Symbol

        # --- Utiliser BTC comme benchmark pour comparer la performance ---
        self.SetBenchmark(self.btc)

        # --- Creation des indicateurs EMA ---
        # EMA rapide (12 periodes) : reagit vite aux changements de prix
        # EMA lente (26 periodes) : represente la tendance de fond
        self.ema_fast = self.EMA(self.btc, 12, Resolution.Hour)
        self.ema_slow = self.EMA(self.btc, 26, Resolution.Hour)

        # --- Prechauffage : attendre assez de donnees pour que les EMA soient pretes ---
        self.SetWarmUp(26, Resolution.Hour)

    def OnData(self, data: Slice):
        """Appelee a chaque nouvelle bougie (ici chaque heure)."""

        # Ne rien faire pendant le prechauffage ou si les indicateurs ne sont pas prets
        if self.IsWarmingUp:
            return
        if not self.ema_fast.IsReady or not self.ema_slow.IsReady:
            return

        # Verifier que les donnees BTC sont disponibles dans cette tranche
        if not data.ContainsKey(self.btc):
            return

        # --- Lecture des valeurs EMA courantes ---
        fast = self.ema_fast.Current.Value
        slow = self.ema_slow.Current.Value

        # --- Logique de trading ---
        # Golden cross : EMA rapide passe au-dessus de l'EMA lente -> signal d'achat
        if fast > slow and not self.Portfolio[self.btc].Invested:
            self.SetHoldings(self.btc, 1.0)  # Investir 100% du portefeuille
            self.Debug(f"ACHAT  | Prix={data[self.btc].Close:.2f} | EMA12={fast:.2f} > EMA26={slow:.2f}")

        # Death cross : EMA rapide passe sous l'EMA lente -> signal de vente
        elif fast < slow and self.Portfolio[self.btc].Invested:
            self.Liquidate(self.btc)  # Vendre toute la position
            self.Debug(f"VENTE  | Prix={data[self.btc].Close:.2f} | EMA12={fast:.2f} < EMA26={slow:.2f}")

    def OnOrderEvent(self, orderEvent):
        """Journalisation des ordres executes."""
        if orderEvent.Status == OrderStatus.Filled:
            direction = "Achat" if orderEvent.Direction == OrderDirection.Buy else "Vente"
            self.Debug(
                f"{self.Time.strftime('%Y-%m-%d %H:%M')} - {direction} "
                f"de {abs(orderEvent.FillQuantity):.6f} BTC "
                f"a {orderEvent.FillPrice:.2f} USDT"
            )
