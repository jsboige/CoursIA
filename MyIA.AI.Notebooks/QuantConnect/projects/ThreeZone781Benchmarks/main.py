# Benchmarks de comparaison pour l'evaluation de la strategie 781 (issue #18905,
# point 3) : SPY detenu et 60/40 (SPY/IEF), meme fenetre 2018-2026, meme modele
# de frais IBKR que la strategie. Un seul projet, mode par parametre de backtest.

from AlgorithmImports import *


class _ScaledFeeModel(FeeModel):
    """Frais IBKR mis a l'echelle (identite a 1.0, cf #18905 point 4)."""

    def __init__(self, multiplier):
        self._multiplier = multiplier
        self._base = InteractiveBrokersFeeModel()

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None or self._multiplier == 1.0:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))


class Bench781(QCAlgorithm):

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_end_date(2026, 9, 25)
        self.set_cash(100000)

        self.set_security_initializer(self._ibkr_fees)

        self.mode = self.get_parameter("mode", "spy")
        self.fee_mult = float(self.get_parameter("fee_mult", "1"))

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.ief = None
        if self.mode == "6040":
            self.ief = self.add_equity("IEF", Resolution.DAILY).symbol

        # Rebalancement mensuel (le 60/40 en a besoin ; le mode spy est idempotent).
        self.schedule.on(
            self.date_rules.month_start(self.spy),
            self.time_rules.after_market_open(self.spy, 30),
            self._rebalance,
        )

    def _ibkr_fees(self, security):
        security.set_fee_model(_ScaledFeeModel(self.fee_mult))

    def _rebalance(self):
        if self.mode == "6040":
            self.set_holdings(
                [PortfolioTarget(self.spy, 0.6), PortfolioTarget(self.ief, 0.4)], True
            )
        else:
            self.set_holdings([PortfolioTarget(self.spy, 1.0)], True)
