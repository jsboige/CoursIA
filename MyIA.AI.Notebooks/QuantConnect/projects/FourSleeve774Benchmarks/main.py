# region imports
from AlgorithmImports import *
# endregion
# References de comparaison pour l'evaluation de la reimplementation declaree de la
# strategie 774 (issue #18904). Un seul projet, mode par parametre de backtest :
#   spy   SPY detenu (reference principale du verdict)
#   6040  60 % SPY / 40 % IEF (seconde reference, correction de Holm)
#   vt2   SPY / QQQ / IEF / GLD a poids egaux (panier proxy, correlations seulement)
#   aw    SPY 0,30 / IEF 0,30 / GLD 0,30 / XLP 0,10 (panier proxy, correlations seulement)
# Rebalancement le premier jour de bourse du mois, frais du courtier mis a l'echelle
# comme dans la strategie.
#
# Contrat du rejeu en ombre (#18923, shadow/README.md) : dates par les parametres
# `start` et `end` sans valeur par defaut ; valeur du portefeuille a chaque cloture dans
# le graphique `shadow` (series e0..e4 a tour de role), plus `fees` et `turnover`.

from datetime import datetime

MODES = {
    "spy": {"SPY": 1.0},
    "6040": {"SPY": 0.6, "IEF": 0.4},
    "vt2": {"SPY": 0.25, "QQQ": 0.25, "IEF": 0.25, "GLD": 0.25},
    "aw": {"SPY": 0.30, "IEF": 0.30, "GLD": 0.30, "XLP": 0.10},
}

class _ScaledFeeModel(FeeModel):
    """Frais du courtier (modele par defaut de Lean), mis a l'echelle (identite a 1.0)."""

    def __init__(self, multiplier):
        self._multiplier = multiplier
        self._base = InteractiveBrokersFeeModel()

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None or self._multiplier == 1.0:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))

class Bench774(QCAlgorithm):

    def initialize(self):
        start = datetime.strptime(self.get_parameter("start"), "%Y-%m-%d")
        end = datetime.strptime(self.get_parameter("end"), "%Y-%m-%d")
        self.set_start_date(start.year, start.month, start.day)
        self.set_end_date(end.year, end.month, end.day)
        self.set_cash(100000)
        self.start_value = 100000.0

        mode = self.get_parameter("mode", "spy")
        if mode not in MODES:
            raise ValueError(f"mode inconnu : {mode}")
        self.fee_mult = float(self.get_parameter("fee_mult", "1"))
        self.set_security_initializer(
            lambda security: security.set_fee_model(_ScaledFeeModel(self.fee_mult)))

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.weights = {}
        for ticker, w in MODES[mode].items():
            symbol = self.spy if ticker == "SPY" else self.add_equity(ticker, Resolution.DAILY).symbol
            self.weights[symbol] = w

        # month_start sans symbole saute les mois dont le 1er n'est pas une seance (#18941).
        self.schedule.on(self.date_rules.month_start(self.spy),
                         self.time_rules.after_market_open(self.spy, 30), self._rebalance)

        self.closes = 0
        self.traded = 0.0

    def _rebalance(self):
        self.set_holdings([PortfolioTarget(s, w) for s, w in self.weights.items()])

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
