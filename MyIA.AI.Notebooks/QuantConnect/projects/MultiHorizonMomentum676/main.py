# region imports
from AlgorithmImports import *
# endregion
# Reimplementation declaree de la strategie publique 676 du Strategy Explorer QuantConnect
# ("Multi-Horizon ETF Momentum Rotation Strategy", auteur affiche : Jon Thibodeaux,
# v1.1.0), evaluee dans l'issue #19174. Ecrite d'apres la description publique de la
# fiche : aucune ligne du code d'origine n'est reprise. Points laisses ouverts par la
# description et choix retenus : README.md.
#
# Regle : le premier jour de bourse du mois, score de chaque ETF = moyenne des taux de
# variation sur 5, 21, 63, 126 et 252 seances, chacun mesure avec un saut de `skip`
# seances ; les `top` meilleurs sont retenus, tout en liquidites si leurs scores sont
# tous negatifs ; poids inverses de l'ecart-type des rendements journaliers sur 63
# seances. Avec `liquidate=1`, tout est vendu avant l'achat des nouvelles cibles.
#
# Contrat du rejeu en ombre (#18923, shadow/README.md) : dates par les parametres
# `start` et `end` sans valeur par defaut ; valeur du portefeuille a chaque cloture dans
# le graphique `shadow` (series e0..e4 a tour de role), plus `fees` et `turnover`.

from datetime import datetime

import numpy as np

# 15 lignes choisies ici, puis les 5 ajouts nommes par la version 1.1.0 de la fiche.
UNIVERSE = [
    "SPY", "QQQ", "IWM", "VNQ",           # actions US
    "EFA", "EEM", "EWJ", "VGK",           # actions hors US
    "TLT", "IEF", "SHY", "LQD", "TIP",    # obligations
    "GLD", "DBC",                         # matieres premieres
    "UUP", "FXF", "AIA", "DBA", "RLY",    # ajouts de la version 1.1.0
]
HORIZONS = (5, 21, 63, 126, 252)
VOL_WINDOW = 63


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


class MultiHorizonMomentum676(QCAlgorithm):

    def initialize(self):
        start = datetime.strptime(self.get_parameter("start"), "%Y-%m-%d")
        end = datetime.strptime(self.get_parameter("end"), "%Y-%m-%d")
        self.set_start_date(start.year, start.month, start.day)
        self.set_end_date(end.year, end.month, end.day)
        self.set_cash(100000)
        self.start_value = 100000.0

        self.fee_mult = float(self.get_parameter("fee_mult", "1"))
        self.top = int(self.get_parameter("top", "5"))
        self.skip = int(self.get_parameter("skip", "21"))
        self.liquidate_all = self.get_parameter("liquidate", "1") == "1"
        self.weighting = self.get_parameter("weights", "invvol")
        if self.weighting not in ("invvol", "equal"):
            raise ValueError(f"weights inconnu : {self.weighting}")
        self.set_security_initializer(
            lambda security: security.set_fee_model(_ScaledFeeModel(self.fee_mult)))

        self.symbols = [self.add_equity(t, Resolution.DAILY).symbol for t in UNIVERSE]
        self.spy = self.symbols[0]
        # clotures necessaires : le plus long horizon apres le saut, et la fenetre de volatilite
        self.need = max(self.skip + max(HORIZONS), VOL_WINDOW) + 1

        # month_start sans symbole saute les mois dont le 1er n'est pas une seance (#18941).
        self.schedule.on(self.date_rules.month_start(self.spy),
                         self.time_rules.after_market_open(self.spy, 30), self._rebalance)

        self.closes = 0
        self.traded = 0.0

    def _signals(self):
        """Score et volatilite de chaque ETF, sur les clotures jusqu'a la seance precedente."""
        hist = self.history(self.symbols, self.need + 10, Resolution.DAILY)
        scores, vols = {}, {}
        if hist.empty:
            return scores, vols
        for symbol in self.symbols:
            try:
                closes = hist.loc[symbol]["close"].dropna().values
            except KeyError:
                continue
            if len(closes) < self.need:
                continue
            base = closes[-1 - self.skip]
            scores[symbol] = float(np.mean(
                [base / closes[-1 - self.skip - h] - 1.0 for h in HORIZONS]))
            window = closes[-(VOL_WINDOW + 1):]
            vols[symbol] = float(np.std(window[1:] / window[:-1] - 1.0, ddof=1))
        return scores, vols

    def _rebalance(self):
        scores, vols = self._signals()
        ranked = sorted(scores, key=scores.get, reverse=True)[:self.top]
        day = self.time.strftime("%Y-%m-%d")
        if not ranked or all(scores[s] < 0 for s in ranked):
            self.liquidate()
            self.log(f"sel {day} cash")
            return
        if self.weighting == "equal":
            raw = {s: 1.0 for s in ranked}
        else:
            raw = {s: 1.0 / vols[s] for s in ranked}
        total = sum(raw.values())
        weights = {s: w / total for s, w in raw.items()}
        if self.liquidate_all:
            # En donnees journalieres, l'ordre passe a 10 h s'execute a la cloture : apres
            # liquidate(), set_holdings calculerait ses quantites contre des positions pas
            # encore vendues et n'enverrait que les ecarts (defaut de la v1, #19174). Les
            # quantites cibles absolues sont donc fixees avant la liquidation ; ventes et
            # achats s'executent a la meme cloture, ventes d'abord.
            quantities = {s: self.portfolio[s].quantity + self.calculate_order_quantity(s, w)
                          for s, w in weights.items()}
            self.liquidate()
            for s, q in quantities.items():
                if q > 0:
                    self.market_order(s, q)
        else:
            self.set_holdings([PortfolioTarget(s, w) for s, w in weights.items()],
                              liquidate_existing_holdings=True)
        self.log(f"sel {day} " + " ".join(
            f"{s.value}:{weights[s]:.3f}:{scores[s]:+.4f}" for s in ranked))

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
