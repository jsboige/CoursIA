# region imports
from AlgorithmImports import *
# endregion

# Rotation BTC/ETH par force relative (#20189, ligue #19821).
#
# Toujours investie : a chaque revue, la strategie detient 99 % de sa valeur dans l'actif
# dont le rendement sur les `lookback` dernieres barres est le plus fort. Aucune jambe de
# liquidites. Place de marche : Bitfinex, dont l'historique journalier QC des deux paires
# en USD est le plus long (sonde du 2026-10-10 : ETHUSD des le 2016-03-09).
#
# Parametres, tous optionnels :
# - start / end : dates AAAA-MM-JJ (defaut 2017-01-01 -> 2026-06-30) ;
# - lookback : nombre de barres du rendement compare (defaut 28) ;
# - review : "weekly" (barre horodatee le lundi, cloture du dimanche UTC) ou "daily" ;
# - mode : "stronger" (defaut) ou "weaker" (controle descriptif : l'actif le plus faible) ;
# - fee_mult : multiplie les frais du modele de courtier (1 = identite).
# Graphique "shadow" : une valeur par barre journaliere, tracee avant toute decision dans
# e0..e4 (valeur du portefeuille), b0..b4 (cloture BTCUSD) et h0..h4 (cloture ETHUSD).


class _ScaledFeeModel(FeeModel):
    """Frais du modele de courtier de la place, mis a l'echelle."""

    def __init__(self, base, multiplier):
        super().__init__()
        self._base = base
        self._multiplier = multiplier

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))


class BtcEthRotationAlgorithm(QCAlgorithm):

    TARGET = 0.99

    def initialize(self):
        start = self.get_parameter("start") or "2017-01-01"
        end = self.get_parameter("end") or "2026-06-30"
        self.set_start_date(*map(int, start.split("-")))
        self.set_end_date(*map(int, end.split("-")))
        self.set_account_currency("USD")
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.BITFINEX, AccountType.CASH)

        self.lookback = int(self.get_parameter("lookback") or 28)
        self.review = self.get_parameter("review") or "weekly"
        self.mode = self.get_parameter("mode") or "stronger"
        self.fee_mult = float(self.get_parameter("fee_mult") or 1)
        if self.review not in ("weekly", "daily") or self.mode not in ("stronger", "weaker"):
            raise ValueError(f"review={self.review} mode={self.mode}")

        self.btc = self.add_crypto("BTCUSD", Resolution.DAILY, Market.BITFINEX).symbol
        self.eth = self.add_crypto("ETHUSD", Resolution.DAILY, Market.BITFINEX).symbol
        self.set_benchmark(self.btc)
        if self.fee_mult != 1.0:
            for sym in (self.btc, self.eth):
                sec = self.securities[sym]
                sec.set_fee_model(_ScaledFeeModel(sec.fee_model, self.fee_mult))

        self.roc_btc = self.roc(self.btc, self.lookback, Resolution.DAILY)
        self.roc_eth = self.roc(self.eth, self.lookback, Resolution.DAILY)
        self.set_warm_up(self.lookback + 5, Resolution.DAILY)

        # Compteurs de mesure (#20189)
        self.held = None
        self.closes = 0
        self.switches = 0
        self.days_btc = 0
        self.days_eth = 0
        self.days_cash = 0
        self.bars = {self.btc: 0, self.eth: 0}
        self.first_bar = {}
        self.first_decision = None

    def on_data(self, data):
        for sym in (self.btc, self.eth):
            if data.bars.contains_key(sym):
                self.bars[sym] += 1
                self.first_bar.setdefault(sym, self.time)
        if self.is_warming_up:
            return
        if not (data.bars.contains_key(self.btc) and data.bars.contains_key(self.eth)):
            return
        # Graphique shadow : une valeur par barre commune, avant toute decision.
        k = self.closes % 5
        self.plot("shadow", f"e{k}", self.portfolio.total_portfolio_value)
        self.plot("shadow", f"b{k}", float(data.bars[self.btc].close))
        self.plot("shadow", f"h{k}", float(data.bars[self.eth].close))
        self.closes += 1
        if self.held == self.btc:
            self.days_btc += 1
        elif self.held == self.eth:
            self.days_eth += 1
        else:
            self.days_cash += 1

        if not (self.roc_btc.is_ready and self.roc_eth.is_ready):
            return
        if self.review == "weekly" and self.time.weekday() != 0:
            return
        rb, re = self.roc_btc.current.value, self.roc_eth.current.value
        if rb == re:
            return
        stronger = self.btc if rb > re else self.eth
        target = stronger if self.mode == "stronger" else (self.eth if stronger == self.btc else self.btc)
        if target == self.held:
            return
        if self.first_decision is None:
            self.first_decision = self.time
        # Quantite absolue calculee avant la vente : en backtest, la vente passe d'abord
        # a la meme cloture, puis l'achat.
        price = float(data.bars[target].close)
        qty = round(self.TARGET * self.portfolio.total_portfolio_value / price, 6)
        if self.held is not None:
            old = self.portfolio[self.held].quantity
            if old > 0:
                self.market_order(self.held, -old, tag="rotation: vente")
            self.switches += 1
        self.market_order(target, qty, tag="rotation: achat")
        self.held = target

    def on_end_of_algorithm(self):
        def day(t):
            return f"{t:%Y-%m-%d}" if t else "none"
        stats = {
            "Bars common": self.closes,
            "Bars BTC": self.bars[self.btc],
            "Bars ETH": self.bars[self.eth],
            "First bar BTC": day(self.first_bar.get(self.btc)),
            "First bar ETH": day(self.first_bar.get(self.eth)),
            "First decision": day(self.first_decision),
            "Switches": self.switches,
            "Days BTC": self.days_btc,
            "Days ETH": self.days_eth,
            "Days cash": self.days_cash,
            "Fees total": f"{float(self.portfolio.total_fees):.2f}",
            "Params": (f"lookback={self.lookback} review={self.review} mode={self.mode} "
                       f"fee_mult={self.fee_mult}"),
        }
        for key, value in stats.items():
            self.set_runtime_statistic(key, str(value))
