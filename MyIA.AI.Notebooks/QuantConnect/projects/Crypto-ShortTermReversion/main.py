# region imports
from AlgorithmImports import *
# endregion

# Parametres de mesure (issue de pre-enregistrement), tous optionnels : sans eux,
# l'algorithme garde sa forme d'origine (RSI(2) Wilder < 10 en entree, sortie RSI > 60
# ou garde temporelle de 10 seances, position 95 % du cash, Binance compte cash en
# USDT, frais du modele de courtier Binance).
# - start / end : dates au format AAAA-MM-JJ ;
# - rsi_period : periode du RSI (2 par defaut) ;
# - entry / exit : seuils du RSI en entree (10) et en sortie (60) ;
# - time_stop : nombre maximal de seances de detention (10 ; 0 = coupe) ;
# - size : fraction du cash deployee en entree (0.95) ;
# - fee_mult : multiplie les frais du modele de courtier Binance (1 = identite).
# Compteurs publies en statistiques d'execution, et graphique "shadow" : une valeur
# par jour, tracee dans e0..e4 (equity) et b0..b4 (cloture BTCUSDT) en alternance,
# pour que le graphique garde une valeur par barre journaliere.


class _ScaledFeeModel(FeeModel):
    """Frais du modele de courtier Binance, mis a l'echelle."""

    def __init__(self, multiplier):
        super().__init__()
        self._multiplier = multiplier
        self._base = BinanceFeeModel()

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))


class CryptoShortTermReversion(QCAlgorithm):
    """Retour a la moyenne court terme sur BTCUSDT (barres journalieres Binance).

    Regle d'entree : RSI(2) de Wilder < 10 -> achat de 95 % du cash disponible.
    Regle de sortie : RSI(2) > 60, ou garde temporelle de 10 seances si le
    rebond n'est pas venu. Sans filtre de tendance : l'idee mesuree (EPIC de la
    ligue) est un candidat qui se decorrele des strategies de tendance, pas une
    variante filtree. La garde temporelle borne le cas du couteau qui tombe.

    Motif du choix de la regle : RSI(2) de Connors est la regle canonique du
    retour a la moyenne court terme documentee (Short Term Trading Strategies
    That Work) ; la version crypto retire le filtre de tendance du canon actions
    pour repondre a la question de decorrelation de la ligue. Aucun parametre
    n'a ete regle sur les donnees : les valeurs par defaut sont celles du canon.
    """

    def initialize(self):
        start = self.get_parameter("start")
        end = self.get_parameter("end")
        if start:
            self.set_start_date(*map(int, start.split("-")))
        else:
            self.set_start_date(2018, 1, 1)
        if end:
            self.set_end_date(*map(int, end.split("-")))
        else:
            self.set_end_date(2024, 12, 31)

        self.set_account_currency("USDT")
        self.set_cash(10000)
        self.btc = self.add_crypto("BTCUSDT", Resolution.DAILY, Market.BINANCE).symbol
        self.set_benchmark(self.btc)
        self.set_brokerage_model(BrokerageName.BINANCE, AccountType.CASH)
        self.fee_mult = float(self.get_parameter("fee_mult") or 1)
        if self.fee_mult != 1.0:
            self.securities[self.btc].set_fee_model(_ScaledFeeModel(self.fee_mult))

        self.rsi_period = int(self.get_parameter("rsi_period") or 2)
        self.entry_threshold = float(self.get_parameter("entry") or 10)
        self.exit_threshold = float(self.get_parameter("exit") or 60)
        ts = self.get_parameter("time_stop")
        self.time_stop = int(ts) if ts else 10
        self.position_size = float(self.get_parameter("size") or 0.95)

        self.rsi = self.rsi(self.btc, self.rsi_period, MovingAverageType.WILDERS, Resolution.DAILY)

        # Compteurs de mesure
        self.closes = 0
        self.days_invested = 0
        self.n_entries = 0
        self.n_rsi_exits = 0
        self.n_time_exits = 0
        self.entry_bar = None
        self.holding_bars = []
        self.first_bar = None
        self.first_ready = None

        self.set_warm_up(self.rsi_period + 10, Resolution.DAILY)

    def on_data(self, data):
        if data.bars.contains_key(self.btc) and self.first_bar is None:
            self.first_bar = self.time
        if self.is_warming_up:
            return
        if data.bars.contains_key(self.btc):
            # Graphique shadow : une valeur par barre journaliere, avant toute decision.
            self.plot("shadow", f"e{self.closes % 5}", self.portfolio.total_portfolio_value)
            self.plot("shadow", f"b{self.closes % 5}", float(data.bars[self.btc].close))
            self.closes += 1
            if self.portfolio[self.btc].invested:
                self.days_invested += 1
        if not self.rsi.is_ready:
            return
        if not data.bars.contains_key(self.btc):
            return
        if self.first_ready is None:
            self.first_ready = self.time

        price = float(data.bars[self.btc].close)
        rsi_value = float(self.rsi.current.value)
        invested = self.portfolio[self.btc].invested

        if invested:
            held = self.closes - self.entry_bar
            if rsi_value > self.exit_threshold:
                self.liquidate(self.btc, tag="exit rsi")
                self.n_rsi_exits += 1
                self.holding_bars.append(held)
            elif self.time_stop and held >= self.time_stop:
                self.liquidate(self.btc, tag="exit garde temporelle")
                self.n_time_exits += 1
                self.holding_bars.append(held)
        elif rsi_value < self.entry_threshold:
            quantity = (self.portfolio.cash * self.position_size) / price
            if quantity > 0:
                self.market_order(self.btc, quantity, tag="entree rsi bas")
                self.n_entries += 1
                self.entry_bar = self.closes

    def on_end_of_algorithm(self):
        if self.holding_bars:
            avg_hold = sum(self.holding_bars) / len(self.holding_bars)
            self.debug(f"detention moyenne: {avg_hold:.1f} seances")
        self.debug(
            f"entries={self.n_entries} rsi_exits={self.n_rsi_exits} "
            f"time_exits={self.n_time_exits} days_invested={self.days_invested} "
            f"closes={self.closes}"
        )
        self.debug(f"first_bar={self.first_bar} first_ready={self.first_ready}")
