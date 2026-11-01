#region imports
from AlgorithmImports import *

from datetime import datetime
#endregion
# Indicateur Halloween (« Sell in May and go away ») — mesure pré-enregistrée #24069.
# Source : Bouman & Jacobsen, "The Halloween Indicator, 'Sell in May and Go Away':
# Another Puzzle", version de travail de juillet 2001 (à paraître dans l'AER, 2002).
# Règle de l'annexe A : le marché de fin octobre à début mai, l'actif sans risque
# (bons du Trésor à court terme) de fin avril à fin octobre.
# Ici : SPY pour le marché, BIL pour l'actif sans risque.

# Mois où la stratégie détient le marché (novembre à avril).
WINTER_MONTHS = (11, 12, 1, 2, 3, 4)


class HalloweenIndicatorAlgorithm(QCAlgorithm):

    def initialize(self):
        # Mesure contre références détenues (#24069, protocole de #22828) :
        # `strategy` (défaut) applique la règle ; `spy` (SPY détenu) et `6040`
        # (SPY 60 %, BND 40 %) sont les deux références du verdict ; `inverse`
        # (SPY de mai à octobre, BIL de novembre à avril) est le diagnostic de
        # l'asymétrie saisonnière.
        self._mode = self.get_parameter("mode", "strategy").lower()
        if self._mode not in ("strategy", "spy", "6040", "inverse"):
            raise ValueError(
                f"unknown mode parameter: {self._mode} (strategy | spy | 6040 | inverse)"
            )

        start = self.get_parameter("start_date", "2016-01-01")
        end = self.get_parameter("end_date", "2026-07-01")
        self.set_start_date(datetime.strptime(start, "%Y-%m-%d"))
        self.set_end_date(datetime.strptime(end, "%Y-%m-%d"))
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        # Sans prix amorcé, la première séance planifiée voit un prix nul et
        # n'investit pas.
        self.settings.seed_initial_prices = True

        self._spy = self.add_equity("SPY", Resolution.DAILY).symbol
        # Chaque mode n'abonne que ses titres : BIL pour les deux modes
        # saisonniers, BND pour le 60/40.
        self._bil = (
            self.add_equity("BIL", Resolution.DAILY).symbol
            if self._mode in ("strategy", "inverse")
            else None
        )
        self._bnd = (
            self.add_equity("BND", Resolution.DAILY).symbol
            if self._mode == "6040"
            else None
        )
        # Une bascule envoie la vente de la ligne détenue et l'achat de la
        # nouvelle, remplies à la même clôture. Le contrôle de marge de l'achat
        # ne déduit pas la vente en attente : avec le levier de 2 du modèle de
        # courtage, l'achat de 100 % tombe à la limite et Lean le refuse
        # certaines séances (écart déclaré sur #24069). Le levier maximal
        # autorisé passe à 4 ; les cibles restent à 100 % de la valeur du
        # portefeuille, l'exposition ne change pas.
        for symbol in (self._spy, self._bil, self._bnd):
            if symbol is not None:
                self.securities[symbol].set_leverage(4)

        # Décision au début de chaque mois, une minute après l'ouverture de SPY.
        # En résolution journalière, l'ordre se remplit à la clôture de la séance.
        self._held = None
        self._invalid_orders = 0
        self.schedule.on(
            self.date_rules.month_start(self._spy),
            self.time_rules.after_market_open(self._spy, 1),
            self._rebalance,
        )

        # Trace journalière `shadow` (contrat #18923) : valeur du portefeuille à
        # l'ouverture de chaque séance de SPY, répartie sur e0..e4. Tous les modes
        # la prennent au même instant, sur la clôture précédente.
        self._closes = 0
        self.schedule.on(
            self.date_rules.every_day(self._spy),
            self.time_rules.after_market_open(self._spy, 0),
            self._trace,
        )

    def _seasonal_asset(self):
        winter = self.time.month in WINTER_MONTHS
        if self._mode == "strategy":
            return self._spy if winter else self._bil
        return self._bil if winter else self._spy

    def _rebalance(self):
        if self._mode == "spy":
            self.set_holdings([PortfolioTarget(self._spy, 1.0)])
            return
        if self._mode == "6040":
            self.set_holdings([
                PortfolioTarget(self._spy, 0.6),
                PortfolioTarget(self._bnd, 0.4),
            ])
            return
        # Modes saisonniers : un ordre ne part qu'au changement de régime, ou à
        # l'entrée dans la fenêtre. Le portefeuille bascule à 100 % sur la ligne
        # du régime, sans levier ; les quantités se calculent sur la position
        # finale (un seul appel, liquidation comprise).
        target = self._seasonal_asset()
        if target == self._held:
            return
        self.transactions.cancel_open_orders()
        self.set_holdings([PortfolioTarget(target, 1.0)], liquidate_existing_holdings=True)
        self._held = target

    def _trace(self):
        self.plot("shadow", f"e{self._closes % 5}", self.portfolio.total_portfolio_value)
        self._closes += 1

    def on_order_event(self, order_event):
        if order_event.status == OrderStatus.INVALID:
            self._invalid_orders += 1
            self.set_runtime_statistic("invalid_orders", str(self._invalid_orders))

    def on_end_of_algorithm(self):
        self.set_runtime_statistic("invalid_orders", str(self._invalid_orders))
