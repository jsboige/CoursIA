# region imports
from AlgorithmImports import *
# endregion
from datetime import datetime


class ShadowExample(QCAlgorithm):
    """Candidate d'exemple du suivi en ombre (#18923) : 60/40 SPY/IEF, rebalance chaque mois.

    Elle montre le contrat d'une candidate QuantConnect (shadow/README.md) et sert au test de
    bout en bout de `plan-qc` / `ingest-qc`. Sa logique est volontairement triviale : ce n'est
    pas une candidate a suivre.

    Contrat :
    - les dates viennent des parametres `start` et `end` (ISO), sans valeur par defaut : un
      backtest lance sans eux echoue au lieu de tourner sur une periode implicite ;
    - a chaque cloture de seance, la valeur du portefeuille va dans le graphique `shadow`, series
      `e0` a `e4` a tour de role (une serie par seance sur cinq garde chaque point a sa date) ;
    - au meme moment, `fees` (frais cumules / valeur de depart) et `turnover` (somme des
      montants executes / valeur du portefeuille au moment de l'execution).
    """

    def initialize(self):
        start = datetime.strptime(self.get_parameter("start"), "%Y-%m-%d")
        end = datetime.strptime(self.get_parameter("end"), "%Y-%m-%d")
        self.set_start_date(start.year, start.month, start.day)
        self.set_end_date(end.year, end.month, end.day)
        self.set_cash(100000)
        self.start_value = 100000.0

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        ief = self.add_equity("IEF", Resolution.DAILY).symbol
        self.targets = [PortfolioTarget(self.spy, 0.6), PortfolioTarget(ief, 0.4)]
        # month_start sans symbole saute les mois dont le 1er n'est pas une seance (#18941).
        self.schedule.on(self.date_rules.month_start(self.spy),
                         self.time_rules.after_market_open(self.spy, 30), self.rebalance)

        self.closes = 0     # seances tracees, pour l'alternance e0..e4
        self.traded = 0.0   # rotation cumulee, en fraction du portefeuille

    def rebalance(self):
        self.set_holdings(self.targets)

    def on_order_event(self, event):
        if event.status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            self.traded += (abs(event.fill_quantity * event.fill_price)
                            / self.portfolio.total_portfolio_value)

    def on_data(self, data):
        if not data.bars.contains_key(self.spy):
            return
        self.plot("shadow", f"e{self.closes % 5}", self.portfolio.total_portfolio_value)
        self.plot("shadow", "fees", self.portfolio.total_fees / self.start_value)
        self.plot("shadow", "turnover", self.traded)
        self.closes += 1
