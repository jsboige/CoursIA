#region imports
from AlgorithmImports import *
from datetime import datetime
import numpy as np
#endregion
# CAPM Alpha Ranking Strategy On Dow 30 Companies -- Jing Wu, QuantConnect Research 15345
# https://www.quantconnect.com/research/15345/capm-alpha-ranking-strategy-on-dow-30-companies/
# Mise a jour STAFF (Derek Melchin) : exposition reduite, initialiseur de titres.
#
# Port du code publie (#19680). La regression est reprise TELLE QUELLE : le code publie
# resout `benchmark ~ pente * action + constante` (np.linalg.lstsq(returns, benchmark)),
# alors que la prose de l'article annonce l'inverse (action sur benchmark). La constante
# retenue comme « alpha » est donc celle du benchmark regresse sur l'action.
#
# Parametres de mesure (defauts = code de l'article) :
#   regression = article (sens publie) | capm (action regressee sur le benchmark, sens CAPM)
#   exposure   = poids de chacune des deux lignes (1.0 dans l'article, levier 2 ; reduit
#                dans la mise a jour STAFF)
#   mode       = strategy | spy (SPY detenu a 100 %, reference sur le meme harnais)
#   fee_mult   = multiplicateur des frais IBKR (1 = inchanges)
#   timing     = article (ventes et achats le meme jour, comme le code publie) | intent
#                (achats a la seance suivante). En resolution journaliere, la vente part a la
#                cloture : le jour du reequilibrage, la marge des anciennes lignes n'est pas
#                encore liberee et, a levier 2, les achats de nouveaux titres sont refuses
#                (pouvoir d'achat insuffisant). `intent` attend que les ventes soient
#                executees pour acheter, et vise le levier que la regle annonce.
#   start, end = fenetre ; le code de l'article ne peut pas commencer avant le 2015-03-19
#                (derniere entree au Dow de sa liste figee, AAPL).
#
# La liste des 30 titres n'est pas dans le texte de l'article (seulement dans son backtest
# joint) : c'est la composition du Dow Jones au 2015-03-19, figee. Biais du survivant
# assume : la liste ne suit pas les sorties de l'indice apres cette date.
# Valeur du portefeuille a chaque cloture dans le graphique "shadow" (contrat de rejeu en
# ombre, #18923).

DOW_2015 = ["MMM", "AXP", "AAPL", "BA", "CAT", "CVX", "CSCO", "KO", "DIS", "DD",
            "XOM", "GE", "GS", "HD", "IBM", "INTC", "JNJ", "JPM", "MCD", "MRK",
            "MSFT", "NKE", "PFE", "PG", "TRV", "UTX", "UNH", "VZ", "V", "WMT"]


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


class CAPMAlphaRankingDow30(QCAlgorithm):

    def initialize(self):
        start = datetime.strptime(self.get_parameter("start") or "2015-03-19", "%Y-%m-%d")
        end = datetime.strptime(self.get_parameter("end") or "2026-09-30", "%Y-%m-%d")
        self.set_start_date(start.year, start.month, start.day)
        self.set_end_date(end.year, end.month, end.day)
        self.start_value = 1000000.0
        self.set_cash(self.start_value)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self.regression = self.get_parameter("regression") or "article"
        self.exposure = float(self.get_parameter("exposure") or 1.0)
        self.mode = self.get_parameter("mode") or "strategy"
        self.fee_mult = float(self.get_parameter("fee_mult") or 1)
        self.timing = self.get_parameter("timing") or "article"
        if (self.regression not in ("article", "capm") or self.mode not in ("strategy", "spy")
                or self.timing not in ("article", "intent")):
            raise ValueError(f"parametres inconnus : {self.regression}/{self.mode}/{self.timing}")

        # Initialiseur de la mise a jour STAFF : prix amorces des l'ajout du titre, pour que
        # le premier set_holdings ne bute pas sur un prix nul. Sans effet sur la regle.
        seeder = FuncSecuritySeeder(self.get_last_known_prices)
        base_init = BrokerageModelSecurityInitializer(self.brokerage_model, seeder)
        fee_mult = self.fee_mult

        def init(security):
            base_init.initialize(security)
            if fee_mult != 1.0:
                security.set_fee_model(_ScaledFeeModel(fee_mult))

        self.set_security_initializer(init)

        self.lookback = 21
        self.symbols = [self.add_equity(t, Resolution.DAILY).symbol for t in DOW_2015]
        # `self.benchmark` dans l'article : sous l'API snake_case, le nom est pris par
        # QCAlgorithm.benchmark (IBenchmark) et l'initialisation echoue. Seul le nom change.
        self._benchmark = self.add_equity("SPY", Resolution.DAILY).symbol

        if self.mode == "strategy":
            self.schedule.on(self.date_rules.month_start(self.symbols[0]),
                             self.time_rules.after_market_open(self.symbols[0]),
                             self.rebalance)
            if self.timing == "intent":
                self.schedule.on(self.date_rules.every_day(self.symbols[0]),
                                 self.time_rules.after_market_open(self.symbols[0]),
                                 self.buy_pending)

        self._pending = None
        self._rebalance_day = None
        self.closes = 0
        self.traded = 0.0
        self.margin_calls = 0
        self.margin_call_days = []
        self.rebalances = 0

    def select_symbols(self, history):
        '''Select symbols with the highest intercept/alpha to the benchmark
        '''
        alphas = dict()

        # Get the benchmark returns
        benchmark = history[self._benchmark].pct_change().dropna()

        # Conducts linear regression for each symbol and save the intercept/alpha
        for symbol in self.symbols:
            if symbol not in history.columns:
                continue

            # Get the security returns
            returns = history[symbol].pct_change().dropna()
            if len(returns) != len(benchmark):
                continue

            if self.regression == "article":
                # Code publie : benchmark regresse sur l'action.
                returns = np.vstack([returns, np.ones(len(returns))]).T
                result = np.linalg.lstsq(returns, benchmark, rcond=None)
            else:
                # Sens CAPM de la prose : action regressee sur le benchmark.
                design = np.vstack([benchmark, np.ones(len(benchmark))]).T
                result = np.linalg.lstsq(design, returns, rcond=None)
            alphas[symbol] = result[0][1]

        # Select symbols with the highest intercept/alpha to the benchmark
        selected = sorted(alphas.items(), key=lambda x: x[1], reverse=True)[:2]
        return [x[0] for x in selected]

    def rebalance(self):

        # Fetch the historical data to perform the linear regression
        history = self.history(
            self.symbols + [self._benchmark],
            self.lookback,
            Resolution.DAILY).close.unstack(level=0)

        symbols = self.select_symbols(history)
        self.rebalances += 1
        self._rebalance_day = self.time.date()
        self.log("SEL " + ",".join(s.value for s in symbols))

        # Liquidate positions that are not held by selected symbols
        for holdings in self.portfolio.values():
            symbol = holdings.symbol
            if symbol not in symbols and holdings.invested:
                self.liquidate(symbol)

        if self.timing == "intent":
            self._pending = symbols
            return

        # Invest in each of the selected symbols (100 % in the article)
        for symbol in symbols:
            self.set_holdings(symbol, self.exposure)

    def buy_pending(self):
        # Seance suivant le reequilibrage : les ventes ont ete executees a la cloture d'hier.
        if not self._pending or self.time.date() == self._rebalance_day:
            return
        self.set_holdings([PortfolioTarget(s, self.exposure) for s in self._pending])
        self._pending = None

    def on_margin_call(self, requests):
        self.margin_calls += 1
        day = str(self.time.date())
        if day not in self.margin_call_days:
            self.margin_call_days.append(day)
        return requests

    def on_order_event(self, event):
        if event.status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            self.traded += abs(event.fill_quantity * event.fill_price) / self.portfolio.total_portfolio_value

    def on_data(self, data):
        if self.mode == "spy" and not self.portfolio.invested and data.bars.contains_key(self._benchmark):
            self.set_holdings(self._benchmark, 1.0)
        if data.bars.contains_key(self._benchmark):
            self.plot("shadow", f"e{self.closes % 5}", self.portfolio.total_portfolio_value)
            self.plot("shadow", "fees", self.portfolio.total_fees / self.start_value)
            self.plot("shadow", "turnover", self.traded)
            self.closes += 1

    def on_end_of_algorithm(self):
        self.set_runtime_statistic("margin_calls", str(self.margin_calls))
        self.set_runtime_statistic("margin_call_days", ",".join(self.margin_call_days[:12]) or "-")
        self.set_runtime_statistic("rebalances", str(self.rebalances))
