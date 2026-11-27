# region imports
from AlgorithmImports import *
# endregion

# Anomalie de nuit sur le SPY (article de recherche QuantConnect n° 15296,
# « Overnight Anomaly »). L'article achète le SPY à la clôture et le revend à
# l'ouverture suivante, chaque jour de bourse, et conclut que le rendement de
# nuit disparaît une fois payés les frais. Ce projet mesure la règle contre son
# miroir (détenir la séance seulement) et contre le SPY détenu, avec et sans
# frais.
#
# Modes :
#   overnight : achat au marché à la clôture (ordre MOC envoyé 20 minutes avant
#               la clôture), revente au marché à l'ouverture suivante (ordre MOO
#               envoyé après la clôture) ;
#   intraday  : le miroir, achat MOO à l'ouverture et revente MOC à la clôture ;
#   hold      : achat MOO à la première ouverture, puis plus aucun ordre.
# Les trois modes engagent la même fraction du portefeuille (EXPOSURE).

MODES = ("overnight", "intraday", "hold")
EXPOSURE = 0.98  # marge laissée aux écarts entre le cours d'envoi et le cours rempli


class OvernightAnomalyAlgorithm(QCAlgorithm):

    def initialize(self):
        self._mode = self.get_parameter("mode", "overnight").lower()
        if self._mode not in MODES:
            raise ValueError(f"unknown mode parameter: {self._mode} ({' | '.join(MODES)})")
        fees = self.get_parameter("fees", "ib").lower()
        if fees not in ("ib", "none"):
            raise ValueError(f"unknown fees parameter: {fees} (ib | none)")
        slip_bps = float(self.get_parameter("slip_bps", "0"))

        # Dates sans valeur par défaut : un backtest lancé sans elles échoue au
        # lieu de tourner sur une période implicite, et une fin explicite évite
        # que la coupure d'environ 90 jours de certains nœuds la raccourcisse.
        start = self.get_parameter("start")
        end = self.get_parameter("end")
        if not start or not end:
            raise ValueError("parameters start and end are required (ISO dates)")
        self.set_start_date(datetime.strptime(start, "%Y-%m-%d"))
        self.set_end_date(datetime.strptime(end, "%Y-%m-%d"))
        self.set_cash(100000)
        self._start_value = 100000.0

        # Courtier IB (frais par action, minimum par ordre).
        # Cours bruts : les frais par action portent sur le vrai nombre de titres,
        # et les dividendes sont versés en liquidités à qui détient le titre.
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        equity = self.add_equity("SPY", Resolution.MINUTE,
                                 data_normalization_mode=DataNormalizationMode.RAW)
        self._spy = equity.symbol
        if fees == "none":
            equity.set_fee_model(ConstantFeeModel(0))
        if slip_bps > 0:
            equity.set_slippage_model(ConstantSlippageModel(slip_bps / 10000.0))
        self.set_benchmark(self._spy)

        self._traded = 0.0  # rotation cumulée, en fraction du portefeuille
        self._invalid_orders = 0
        self._closes = 0
        self._held_once = False

        every_day = self.date_rules.every_day(self._spy)
        # Un ordre MOC n'est accepté que 15,5 minutes avant la clôture au moins :
        # 20 minutes laissent la marge, y compris les jours de clôture anticipée.
        self.schedule.on(every_day, self.time_rules.before_market_close(self._spy, 20), self._before_close)
        self.schedule.on(every_day, self.time_rules.after_market_close(self._spy, 5), self._after_close)

    def _quantity(self) -> int:
        price = float(self.securities[self._spy].price)
        if price <= 0:
            return 0
        return int(EXPOSURE * float(self.portfolio.total_portfolio_value) / price)

    def _before_close(self):
        held = int(self.portfolio[self._spy].quantity)
        if self._mode == "overnight" and held == 0:
            qty = self._quantity()
            if qty > 0:
                self.market_on_close_order(self._spy, qty)
        elif self._mode == "intraday" and held > 0:
            self.market_on_close_order(self._spy, -held)

    def _after_close(self):
        # Trace journalière `shadow` (contrat #18923) : valeur du portefeuille à la
        # clôture de chaque séance (séries e0..e4 à tour de rôle), frais cumulés
        # divisés par la valeur de départ, rotation cumulée.
        self.plot("shadow", f"e{self._closes % 5}", self.portfolio.total_portfolio_value)
        self.plot("shadow", "fees", float(self.portfolio.total_fees) / self._start_value)
        self.plot("shadow", "turnover", self._traded)
        self._closes += 1

        held = int(self.portfolio[self._spy].quantity)
        if self._mode == "overnight" and held > 0:
            self.market_on_open_order(self._spy, -held)
        elif self._mode == "intraday" and held == 0:
            qty = self._quantity()
            if qty > 0:
                self.market_on_open_order(self._spy, qty)
        elif self._mode == "hold" and not self._held_once:
            qty = self._quantity()
            if qty > 0:
                self.market_on_open_order(self._spy, qty)
                self._held_once = True

    def on_order_event(self, order_event):
        if order_event.status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            self._traded += (abs(float(order_event.fill_quantity) * float(order_event.fill_price))
                             / float(self.portfolio.total_portfolio_value))
        if order_event.status == OrderStatus.INVALID:
            self._invalid_orders += 1

    def on_end_of_algorithm(self):
        self.set_runtime_statistic("invalid_orders", str(self._invalid_orders))
        self.set_runtime_statistic("fees_pct_start",
                                   f"{100.0 * float(self.portfolio.total_fees) / self._start_value:.2f}")
        self.set_runtime_statistic("turnover", f"{self._traded:.1f}")
