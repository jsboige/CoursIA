# region imports
from AlgorithmImports import *
# endregion

# Momentum crypto en coupe, top N avec filtre de tendance (#20214, ligue #19821).
#
# Chaque lundi, la strategie classe les actifs du panier par rendement sur les `lookback`
# dernieres barres, retient les `top_n` plus forts et detient chacun a 99 % / top_n de sa
# valeur si son rendement est positif ; sinon sa part reste en liquidites (USD).
# Place de marche : Bitfinex, paires en USD, barres journalieres, compte cash.
#
# Parametres, tous optionnels :
# - start / end : dates AAAA-MM-JJ (defaut 2018-01-01 -> 2026-06-30) ;
# - lookback : nombre de barres du rendement compare (defaut 28) ;
# - top_n : nombre d'actifs retenus (defaut 3) ;
# - mode : "top" (defaut), "bottom" (les plus faibles, meme filtre), "nofilter" (les plus
#   forts sans filtre de tendance) ou "probe" (sonde des donnees, aucun ordre) ;
# - fee_mult : multiplie les frais du modele de courtier (1 = identite).
# Graphique "shadow" : une valeur par barre journaliere de BTCUSD, tracee avant toute
# decision, dans e0..e4 (valeur du portefeuille), b0..b4 (cloture BTCUSD) et w0..w4
# (indice du panier equipondere, reequilibre chaque lundi, sans frais).

# Liste fixee par la regle de #20214 : alias de ticker essayes dans l'ordre.
CANDIDATES = {
    "BTC": ["BTCUSD"], "ETH": ["ETHUSD"], "XRP": ["XRPUSD"], "LTC": ["LTCUSD"],
    "BCH": ["BCHUSD", "BCHNUSD", "BABUSD", "BCHABCUSD"], "EOS": ["EOSUSD"],
    "ETC": ["ETCUSD"], "XMR": ["XMRUSD"], "ZEC": ["ZECUSD"], "DASH": ["DASHUSD", "DSHUSD"],
    "NEO": ["NEOUSD"], "IOTA": ["IOTAUSD", "IOTUSD"], "XLM": ["XLMUSD"], "TRX": ["TRXUSD"],
    "OMG": ["OMGUSD"],
}

# Panier retenu par la sonde du 2026-10-10 sans remplissage (#20214, regle point 2) :
# barres du 2017-11-01 au 2026-06-30. Exclues : BCH (BCHNUSD, premiere barre 2020-11-15),
# TRX (2018-02-02), XLM (2018-05-02), OMG (derniere barre 2025-07-16).
UNIVERSE = ["BTCUSD", "ETHUSD", "XRPUSD", "LTCUSD", "EOSUSD", "ETCUSD", "XMRUSD",
            "ZECUSD", "DASHUSD", "NEOUSD", "IOTAUSD"]


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


class CryptoMomentumTopNAlgorithm(QCAlgorithm):

    TARGET = 0.99

    def initialize(self):
        self.mode = self.get_parameter("mode") or "top"
        if self.mode not in ("top", "bottom", "nofilter", "probe"):
            raise ValueError(f"mode={self.mode}")
        default_start = "2016-01-01" if self.mode == "probe" else "2018-01-01"
        start = self.get_parameter("start") or default_start
        end = self.get_parameter("end") or "2026-06-30"
        self.set_start_date(*map(int, start.split("-")))
        self.set_end_date(*map(int, end.split("-")))
        self.set_account_currency("USD")
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.BITFINEX, AccountType.CASH)

        self.lookback = int(self.get_parameter("lookback") or 28)
        self.top_n = int(self.get_parameter("top_n") or 3)
        self.fee_mult = float(self.get_parameter("fee_mult") or 1)

        if self.mode == "probe":
            self._init_probe()
            return
        if not UNIVERSE:
            raise ValueError("UNIVERSE vide : lancer la sonde (mode=probe) d'abord")

        self.assets = [self.add_crypto(t, Resolution.DAILY, Market.BITFINEX).symbol for t in UNIVERSE]
        self.btc = self.assets[UNIVERSE.index("BTCUSD")]
        self.set_benchmark(self.btc)
        if self.fee_mult != 1.0:
            for sym in self.assets:
                sec = self.securities[sym]
                sec.set_fee_model(_ScaledFeeModel(sec.fee_model, self.fee_mult))
        self.rocs = {s: self.roc(s, self.lookback, Resolution.DAILY) for s in self.assets}
        self.set_warm_up(self.lookback + 5, Resolution.DAILY)

        # Indice de reference equipondere (sans frais), reequilibre chaque lundi.
        self.last_close = {}
        self.ref_index = 1.0
        self.ref_w = None

        # Compteurs de mesure (#20214)
        self.closes = 0
        self.reviews = 0
        self.days_cash = 0
        self.line_days = 0
        self.held = set()
        self.bars = {s: 0 for s in self.assets}
        self.first_bar = {}
        self.first_decision = None

    # --- sonde -------------------------------------------------------------------------
    def _init_probe(self):
        self.probe = {}
        self.probe_missing = []
        for coin, aliases in CANDIDATES.items():
            for ticker in aliases:
                try:
                    # Sans remplissage : les jours sans echange restent vides, ce qui
                    # donne la vraie derniere barre et les vrais trous.
                    sym = self.add_crypto(ticker, Resolution.DAILY, Market.BITFINEX,
                                          fill_forward=False).symbol
                except Exception:
                    continue
                self.probe[coin] = {"ticker": ticker, "symbol": sym, "bars": 0,
                                    "first": None, "last": None, "gap": 0}
                break
            else:
                self.probe_missing.append(coin)

    def _on_data_probe(self, data):
        for coin, rec in self.probe.items():
            if data.bars.contains_key(rec["symbol"]):
                if rec["last"] is not None:
                    rec["gap"] = max(rec["gap"], (self.time - rec["last"]).days)
                rec["bars"] += 1
                rec["first"] = rec["first"] or self.time
                rec["last"] = self.time

    # --- strategie ----------------------------------------------------------------------
    def on_data(self, data):
        if self.mode == "probe":
            self._on_data_probe(data)
            return
        for sym in self.assets:
            if data.bars.contains_key(sym):
                self.bars[sym] += 1
                self.first_bar.setdefault(sym, self.time)
        if self.is_warming_up or not data.bars.contains_key(self.btc):
            for sym in self.assets:
                if data.bars.contains_key(sym):
                    self.last_close[sym] = float(data.bars[sym].close)
            return

        # Reference equipondere : rendement du jour avec les poids courants, puis derive.
        rets = {}
        for sym in self.assets:
            if data.bars.contains_key(sym):
                close = float(data.bars[sym].close)
                prev = self.last_close.get(sym)
                rets[sym] = close / prev - 1 if prev else 0.0
                self.last_close[sym] = close
            else:
                rets[sym] = 0.0
        if self.ref_w is None:
            self.ref_w = {s: 1.0 / len(self.assets) for s in self.assets}
        r = sum(self.ref_w[s] * rets[s] for s in self.assets)
        self.ref_index *= 1 + r
        self.ref_w = {s: self.ref_w[s] * (1 + rets[s]) / (1 + r) for s in self.assets}
        monday = self.time.weekday() == 0
        if monday:
            self.ref_w = {s: 1.0 / len(self.assets) for s in self.assets}

        # Graphique shadow : une valeur par barre de BTC, avant toute decision.
        k = self.closes % 5
        self.plot("shadow", f"e{k}", self.portfolio.total_portfolio_value)
        self.plot("shadow", f"b{k}", float(data.bars[self.btc].close))
        self.plot("shadow", f"w{k}", self.ref_index)
        self.closes += 1
        if self.held:
            self.line_days += len(self.held)
        else:
            self.days_cash += 1

        if not monday or not all(roc.is_ready for roc in self.rocs.values()):
            return
        self._rebalance()

    def _rebalance(self):
        scores = {s: self.rocs[s].current.value for s in self.assets if s in self.last_close}
        ranked = sorted(scores, key=lambda s: scores[s], reverse=(self.mode != "bottom"))
        chosen = ranked[:self.top_n]
        if self.mode != "nofilter":
            chosen = [s for s in chosen if scores[s] > 0]
        if self.first_decision is None:
            self.first_decision = self.time
        self.reviews += 1

        tpv = float(self.portfolio.total_portfolio_value)
        weight = self.TARGET / self.top_n
        targets = {s: (round(weight * tpv / self.last_close[s], 6) if s in chosen else 0.0)
                   for s in self.assets}
        # Ventes d'abord, puis achats : en backtest, les ordres passent dans cet ordre a la
        # meme cloture.
        for sym in self.assets:
            delta = targets[sym] - float(self.portfolio[sym].quantity)
            if delta < 0 and self.portfolio[sym].quantity > 0:
                qty = -float(self.portfolio[sym].quantity) if targets[sym] == 0 else delta
                self.market_order(sym, qty, tag="momentum: vente")
        for sym in self.assets:
            delta = targets[sym] - float(self.portfolio[sym].quantity)
            if delta > 0:
                self.market_order(sym, delta, tag="momentum: achat")
        self.held = set(chosen)

    def on_end_of_algorithm(self):
        def day(t):
            return f"{t:%Y-%m-%d}" if t else "none"
        if self.mode == "probe":
            for coin, rec in self.probe.items():
                self.set_runtime_statistic(
                    f"Probe {coin}",
                    f"{rec['ticker']} bars={rec['bars']} first={day(rec['first'])} "
                    f"last={day(rec['last'])} maxgap={rec['gap']}")
            self.set_runtime_statistic("Probe missing", ",".join(self.probe_missing) or "none")
            return
        stats = {
            "Universe": ",".join(UNIVERSE),
            "Bars common": self.closes,
            "First bars": " ".join(f"{s.value}:{day(self.first_bar.get(s))}" for s in self.assets),
            "First decision": day(self.first_decision),
            "Reviews": self.reviews,
            "Days cash": self.days_cash,
            "Avg lines": f"{self.line_days / max(self.closes, 1):.3f}",
            "Fees total": f"{float(self.portfolio.total_fees):.2f}",
            "Params": (f"lookback={self.lookback} top_n={self.top_n} mode={self.mode} "
                       f"fee_mult={self.fee_mult}"),
        }
        for key, value in stats.items():
            self.set_runtime_statistic(key, str(value))
