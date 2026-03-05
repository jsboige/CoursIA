# region imports
from AlgorithmImports import *
# endregion


class RiskParity(QCAlgorithm):
    """
    Risk Parity Strategy (Bridgewater-style simplifie).

    Edge: Equaliser la contribution au risque de chaque classe d'actifs
    plutot que la contribution en capital.
    Reference: Asness/Frazzini 2012 "Leverage Aversion and Risk Parity"

    Universe: SPY, EFA, GLD, DBC, TLT (5 classes d'actifs diversifiees)
    Signal: Poids = 1/volatilite(60j), normalises pour sommer a 1.0
    Rebalancement: Mensuel + trigger 5% de derive
    Periode: 2015-2026
    """

    # Parametres configurables
    TICKERS = ["SPY", "EFA", "GLD", "DBC", "TLT"]
    VOL_LOOKBACK = 60       # Jours pour la volatilite realisee
    REBALANCE_DAY = 1       # Jour du mois pour rebalancement mensuel
    DRIFT_THRESHOLD = 0.05  # Seuil de derive pour rebalancement intra-mensuel
    WARMUP_DAYS = 70        # Jours de warmup pour avoir 60j de donnees

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 1, 1)
        self.set_cash(100000)

        # Ajouter les ETFs en resolution quotidienne (suffisant pour mensuel)
        self.symbols = {}
        for ticker in self.TICKERS:
            symbol = self.add_equity(ticker, Resolution.DAILY).symbol
            self.symbols[ticker] = symbol

        # Indicateurs de volatilite (ecart-type 60j des rendements log)
        self.std_indicators = {}
        for ticker, symbol in self.symbols.items():
            # STD sur les log-returns: utiliser StandardDeviation sur les prix
            # On calculera manuellement via RollingWindow
            self.std_indicators[ticker] = self.STD(symbol, self.VOL_LOOKBACK, Resolution.DAILY)

        # Poids cibles actuels
        self.target_weights = {ticker: 1.0 / len(self.TICKERS) for ticker in self.TICKERS}

        # Warmup pour remplir les indicateurs
        self.set_warm_up(self.WARMUP_DAYS)

        # Scheduler: rebalancement mensuel le 1er jour de trading du mois
        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance
        )

        self.log("RiskParity initialized: 5 ETFs, 60-day vol, monthly rebalance")

    def on_data(self, data: Slice):
        """Verifier la derive des poids intra-mensuelle."""
        if self.is_warming_up:
            return

        if not self._indicators_ready():
            return

        # Verifier si les poids actuels ont derive au-dela du seuil
        if self._check_drift():
            self.log(f"Drift threshold exceeded, rebalancing intra-month")
            self._execute_rebalance()

    def rebalance(self):
        """Rebalancement mensuel principal."""
        if self.is_warming_up:
            return

        if not self._indicators_ready():
            self.log("Indicators not ready, skipping rebalance")
            return

        self._compute_target_weights()
        self._execute_rebalance()

    def _indicators_ready(self) -> bool:
        """Verifie que tous les indicateurs sont prets."""
        return all(ind.is_ready for ind in self.std_indicators.values())

    def _compute_target_weights(self):
        """Calcule les poids inversement proportionnels a la volatilite."""
        # Recuperer la volatilite de chaque actif (STD des prix)
        # La STD des prix n'est pas la bonne mesure - on veut la vol des rendements
        # On approxime: vol_rendements ~= STD(prix) / prix_moyen
        # Mais QuantConnect STD donne directement la STD des valeurs brutes
        # Pour avoir la vol des rendements: utiliser le ratio STD/prix actuel

        vols = {}
        for ticker, symbol in self.symbols.items():
            std_val = self.std_indicators[ticker].current.value
            current_price = self.securities[symbol].price

            if current_price > 0 and std_val > 0:
                # Volatilite relative (rendements)
                vols[ticker] = std_val / current_price
            else:
                vols[ticker] = 0.01  # Valeur par defaut si donnee manquante

        # Poids = 1/vol (inverse volatility weighting)
        inv_vols = {}
        for ticker, vol in vols.items():
            if vol > 0:
                inv_vols[ticker] = 1.0 / vol
            else:
                inv_vols[ticker] = 0.0

        total_inv_vol = sum(inv_vols.values())

        if total_inv_vol > 0:
            self.target_weights = {
                ticker: inv_vol / total_inv_vol
                for ticker, inv_vol in inv_vols.items()
            }
        else:
            # Fallback: poids egaux
            n = len(self.TICKERS)
            self.target_weights = {ticker: 1.0 / n for ticker in self.TICKERS}

        # Log les poids calcules
        weight_str = ", ".join(
            f"{t}:{w:.1%}" for t, w in sorted(self.target_weights.items())
        )
        self.log(f"Target weights: {weight_str}")

    def _check_drift(self) -> bool:
        """Verifie si un actif a derive au-dela du seuil par rapport a son poids cible."""
        if not self.portfolio.invested:
            return False

        total_value = self.portfolio.total_portfolio_value
        if total_value <= 0:
            return False

        for ticker, symbol in self.symbols.items():
            target = self.target_weights.get(ticker, 0.0)
            holding = self.portfolio[symbol]
            current_weight = holding.holdings_value / total_value

            if abs(current_weight - target) > self.DRIFT_THRESHOLD:
                return True

        return False

    def _execute_rebalance(self):
        """Execute le rebalancement vers les poids cibles."""
        for ticker, symbol in self.symbols.items():
            weight = self.target_weights.get(ticker, 0.0)
            self.set_holdings(symbol, weight)

        self.log(
            f"Rebalanced | "
            f"Portfolio: ${self.portfolio.total_portfolio_value:,.0f}"
        )
