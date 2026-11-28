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

        start = datetime.strptime(self.get_parameter("start"), "%Y-%m-%d")
        end = datetime.strptime(self.get_parameter("end"), "%Y-%m-%d")
        self.set_start_date(start.year, start.month, start.day)
        self.set_end_date(end.year, end.month, end.day)
        self.set_cash(100000)
        self.start_value = 100000.0
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        # Sans prix amorcé, la première séance planifiée voit un prix nul et
        # n'investit pas.
        self.settings.seed_initial_prices = True

        self._spy = self.add_equity("SPY", Resolution.DAILY).symbol
        # Témoin de publication du suivi en ombre (#27482) : `ingest-qc` lit le
        # graphique `Benchmark` du backtest. Sans benchmark déclaré, ce graphique
        # vaut 0.0 partout, chaque séance s'y lit comme figée et le passage est
        # refusé.
        self.set_benchmark(self._spy)
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
        # l'ouverture de chaque séance de SPY, répartie sur e0..e4, plus les séries
        # `fees` et `turnover` à chaque séance (contrat #27482). Tous les modes
        # la prennent au même instant, sur la clôture précédente.
        # Règle 2 du contrat : le point n'est tracé que si `on_data` a reçu cette
        # clôture publiée, pour SPY et pour chaque titre détenu. Une barre
        # recopiée vers l'avant (séance pas encore publiée en fin de fenêtre)
        # saute le point. `_stale` vaut la liste des barres recopiées de la
        # dernière clôture reçue, `None` tant qu'aucune n'est arrivée depuis le
        # point précédent ; la liste vide du départ laisse passer le premier
        # point, la valeur initiale du portefeuille.
        self._closes = 0
        self.traded = 0.0
        self._stale = []
        self.shadow_skips = 0
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

    def on_data(self, data):
        if data.bars.contains_key(self._spy):
            self._stale = self._fill_forward(data)

    def _fill_forward(self, data):
        """SPY et titres détenus dont la barre de la séance est recopiée vers l'avant."""
        symbols = [self._spy] + [holding.symbol for holding in self.portfolio.values()
                                 if holding.invested and holding.symbol != self._spy]
        return sorted(symbol.value for symbol in symbols
                      if data.bars.contains_key(symbol)
                      and data.bars[symbol].is_fill_forward)

    def _trace(self):
        stale, self._stale = self._stale, None
        if stale is None or stale:
            self.shadow_skips += 1
            cause = ", ".join(stale) if stale else "aucune barre de SPY reçue"
            self.log(f"{self.time:%Y-%m-%d} shadow: point sauté, clôture de la veille "
                     f"non publiée ({cause})")
            return
        self.plot("shadow", f"e{self._closes % 5}", self.portfolio.total_portfolio_value)
        self.plot("shadow", "fees", self.portfolio.total_fees / self.start_value)
        self.plot("shadow", "turnover", self.traded)
        self._closes += 1

    def on_order_event(self, order_event):
        if order_event.status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            self.traded += (abs(order_event.fill_quantity * order_event.fill_price)
                            / self.portfolio.total_portfolio_value)
        if order_event.status == OrderStatus.INVALID:
            self._invalid_orders += 1
            self.set_runtime_statistic("invalid_orders", str(self._invalid_orders))

    def on_end_of_algorithm(self):
        self.set_runtime_statistic("invalid_orders", str(self._invalid_orders))
        self.set_runtime_statistic("Shadow skips FF", str(self.shadow_skips))
