#region imports
from AlgorithmImports import *
from datetime import datetime
#endregion
# https://www.quantconnect.com/research/21195/bitcoin-regime-signal-for-growth-equities/
# Bitcoin Regime Signal for Growth Equities by Derek Melchin (QC Research, published Aug 2026)
# Distilled per issue #18576 (re-evaluation of #12748: sources Faber 2007 SSRN 962461,
# Liu & Tsyvinski 2021 RFS 34(6), Iyer 2022 IMF GFSN 2022/001 -- BTC spillovers drive
# 14-18% of equity vol variation, S&P 500 ~17%).
# Rule: hold QQQ when (BTC > SMA50 BTC) AND (ROC20 BTC > 0), else hold SHY.
# Rebalance weekly on the first trading day at 8:00 ET (before the US equity open),
# reading the BTC regime from a 24/7 market (no halts, circuit breakers, or closing bell).
# Author-reported reference (2014-2026): Sharpe 0.838 vs QQQ 0.682 / SPY 0.564.
#
# Instrumentation de mesure (#19929) : les parametres d'origine (start-year/
# start-month/end-year/end-month) restent les defauts ; "start"/"end" (ISO
# YYYY-MM-DD) les surchargent quand fournis. mode = "gate" (defaut, le gate
# distille -- la regle et le couple liquidate/set_holdings sont inchanges),
# "hold-qqq" (benchmark buy-and-hold QQQ), "spy" et "sixty40" (references
# detenues : SPY seul, ou 60 % SPY / 40 % IEF, reequilibrees le premier jour de
# bourse du mois). sma_window (50), roc_window (20) et frequency ("weekly"
# defaut, "monthly" optionnel) parametrent le signal et la cadence ; fee_mult (1)
# met a l'echelle les frais du courtier (identite a 1.0). Valeur du portefeuille
# a chaque cloture dans le graphique "shadow" (e0..e4, echelle e0-e4, contrat de
# rejeu en ombre #18923) ; compteurs en statistiques d'execution : switches de
# cible (total et par jambe), exposition brute.
#
# Bras d'execution (#20006) : "base" (defaut) conserve exactement le couple
# liquidate/set_holdings ; "settled" memorise la cible a la decision, ne soumet
# que la liquidation de l'autre ETF, puis soumet l'achat depuis on_data a une
# barre ulterieure (autre quantite nulle, aucun ordre QQQ/SHY ouvert, barre cible
# presente). Une vente echouee est reattemptee a la decision hebdomadaire suivante
# (jamais deux fois le meme jour). Statistiques : decisions differees, ordres
# annules/invalides, soumissions d'achat, seances en liquidites, pending final,
# delai decision->soumission. Ne change ni le signal, ni la cadence, ni les frais,
# ni les references QQQ/SPY/60-40.

SMA_WINDOW_DEFAULT = 50
ROC_WINDOW_DEFAULT = 20

MODES = ("gate", "hold-qqq", "spy", "sixty40")
# References detenues, tradees hors du gate et reequilibrees le premier jour de
# bourse de chaque mois.
REFERENCE_WEIGHTS = {"spy": {"SPY": 1.0}, "sixty40": {"SPY": 0.6, "IEF": 0.4}}


class _ScaledFeeModel(FeeModel):
    """Frais du courtier (modele par defaut de Lean), mis a l'echelle (identite a 1.0)."""

    def __init__(self, multiplier):
        super().__init__()
        self._multiplier = multiplier
        self._base = InteractiveBrokersFeeModel()

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None or self._multiplier == 1.0:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))


class _ScaledFeeInitializer(BrokerageModelSecurityInitializer):
    """Conserve les reglages du modele de courtier, puis substitue les frais mis a l'echelle."""

    def __init__(self, brokerage_model, security_seeder, multiplier):
        super().__init__(brokerage_model, security_seeder)
        self._multiplier = multiplier

    def initialize(self, security):
        super().initialize(security)
        security.set_fee_model(_ScaledFeeModel(self._multiplier))


class BitcoinRegimeGate(QCAlgorithm):

    def initialize(self):
        # mode: "gate" (defaut, le gate distille), "hold-qqq" (buy-and-hold
        # benchmark), "spy"/"sixty40" (references detenues).
        self.mode = self.get_parameter("mode") or "gate"
        if self.mode not in MODES:
            raise ValueError(f"mode inconnu : {self.mode}")

        # Execution (#20006) : "base" (defaut) conserve exactement le couple
        # liquidation puis allocation ; "settled" memorise la cible a la decision,
        # ne soumet que la liquidation de l'autre ETF, puis differe l'achat a une
        # barre ulterieure (voir rebalance/on_data). Sans effet hors du mode "gate".
        self._execution_mode = self.get_parameter("execution") or "base"
        if self._execution_mode not in ("base", "settled"):
            raise ValueError(f"execution inconnue : {self._execution_mode}")

        # Dates: parametres d'origine (start-year/start-month/end-year/end-month)
        # surcharges par "start"/"end" (ISO YYYY-MM-DD) quand fournis.
        start = self.get_parameter("start")
        if start:
            d = datetime.strptime(start, "%Y-%m-%d")
            self.set_start_date(d.year, d.month, d.day)
        else:
            self.set_start_date(int(self.get_parameter("start-year", 2016)),
                                int(self.get_parameter("start-month", 1)), 1)
        end = self.get_parameter("end")
        if end:
            d = datetime.strptime(end, "%Y-%m-%d")
            self.set_end_date(d.year, d.month, d.day)
        else:
            self.set_end_date(int(self.get_parameter("end-year", 2026)),
                              int(self.get_parameter("end-month", 6)), 30)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self.sma_window = int(self.get_parameter("sma_window") or SMA_WINDOW_DEFAULT)
        self.roc_window = int(self.get_parameter("roc_window") or ROC_WINDOW_DEFAULT)
        self.frequency = self.get_parameter("frequency") or "weekly"
        if self.frequency not in ("weekly", "monthly"):
            raise ValueError(f"frequency inconnue : {self.frequency}")

        self.fee_mult = float(self.get_parameter("fee_mult") or 1)
        if self.fee_mult != 1.0:
            self.set_security_initializer(_ScaledFeeInitializer(
                self.brokerage_model, FuncSecuritySeeder(self.get_last_known_prices), self.fee_mult))

        # Etat des compteurs (graphique shadow #18923 + statistiques d'execution)
        self.start_value = 100000.0
        self.closes = 0
        self.traded = 0.0
        self.order_counts = {}
        self.gross_sum = 0.0
        self.n_switches = 0
        self.n_to_qqq = 0
        self.n_to_shy = 0
        self._ref_month = -1

        # Etat du bras d'execution "settled" (#20006)
        self._pending_target = None
        self._decision_time = None
        self.n_deferred = 0
        self.n_invalid = 0
        self.n_canceled = 0
        self.acquire_count = 0
        self.delay_seconds = 0.0
        self.cash_closes = 0

        # References detenues : rien a signaler, on detient et on reequilibre.
        if self.mode in REFERENCE_WEIGHTS:
            self.ref_symbols = {}
            for ticker in REFERENCE_WEIGHTS[self.mode]:
                self.ref_symbols[ticker] = self.add_equity(ticker, Resolution.DAILY).symbol
            self.shadow_symbol = self.ref_symbols["SPY"]
            self.set_warm_up(timedelta(60))
            return

        self.qqq = self.add_equity("QQQ", Resolution.DAILY).symbol
        self.shy = self.add_equity("SHY", Resolution.DAILY).symbol
        self.shadow_symbol = self.qqq

        # Bitcoin trades 24/7: the regime source never sleeps through an equity crash.
        self.btc = self.add_crypto("BTCUSD", Resolution.DAILY, market=Market.BITFINEX).symbol

        self.sma = self.sma(self.btc, self.sma_window, Resolution.DAILY)
        self.roc = self.roc(self.btc, self.roc_window, Resolution.DAILY)

        # Recheck on the first trading day (weekly by default, monthly optional),
        # 8:00 ET, before the equity open.
        if self.frequency == "monthly":
            self.schedule.on(
                self.date_rules.month_start(self.qqq),
                self.time_rules.at(8, 0),
                self.rebalance,
            )
        else:
            self.schedule.on(
                self.date_rules.week_start(self.qqq),
                self.time_rules.at(8, 0),
                self.rebalance,
            )

        # The default 50-day SMA needs 50 daily BTC bars; the warm-up scales with
        # the window and stays 60 days for the default (50, 20) pair.
        self.set_warm_up(timedelta(max(self.sma_window, self.roc_window) + 10))

    def on_warmup_finished(self):
        if self.mode in REFERENCE_WEIGHTS:
            return
        self.debug(f"Warmup done: SMA{self.sma_window} ready={self.sma.is_ready}, "
                   f"ROC{self.roc_window} ready={self.roc.is_ready}")

    def rebalance(self) -> None:
        if self.is_warming_up or not self.sma.is_ready or not self.roc.is_ready:
            return

        if self.mode == "hold-qqq":
            if not self.portfolio[self.qqq].invested:
                self.set_holdings(self.qqq, 1.0)
            return

        btc_price = self.securities[self.btc].price
        risk_on = btc_price > self.sma.current.value and self.roc.current.value > 0
        target = self.qqq if risk_on else self.shy

        current = [h.symbol for h in self.portfolio.values() if h.invested]
        if current == [target]:
            # Cible deja detenue seule : effacer toute intention differee obsolete
            # (ex. vente echouee vers la jambe opposee), sans aucune allocation.
            if self._execution_mode == "settled" and self._pending_target is not None:
                self._pending_target = None
                self._decision_time = None
            return

        # Bras "settled" (#20006) : cible memorisee a la decision, seule la
        # liquidation de l'autre ETF est soumise, l'achat est differe. "base"
        # (defaut) reste ci-dessous inchange (liquidation puis allocation).
        if self._execution_mode == "settled":
            self._rebalance_settled(target, btc_price, risk_on)
            return

        self.liquidate()
        self.set_holdings(target, 1.0)
        self.n_switches += 1
        if target == self.qqq:
            self.n_to_qqq += 1
        else:
            self.n_to_shy += 1
        self.debug(f"{self.time:%Y-%m-%d} BTC={btc_price:,.0f} "
                   f"SMA{self.sma_window}={self.sma.current.value:,.0f} "
                   f"ROC{self.roc_window}={self.roc.current.value:+.3f} "
                   f"-> {'QQQ' if risk_on else 'SHY'}")

    def _has_open_orders(self) -> bool:
        """Vrai si un ordre QQQ ou SHY est ouvert (bloque toute acquisition)."""
        for order in self.transactions.get_open_orders():
            if order.symbol == self.qqq or order.symbol == self.shy:
                return True
        return False

    def _rebalance_settled(self, target, btc_price, risk_on) -> None:
        """Decision du bras "settled" (#20006).

        Memorise la cible et l'horodatage AVANT de soumettre, puis ne soumet que
        la liquidation de l'autre ETF. Un ordre QQQ/SHY ouvert suspend la nouvelle
        soumission (comptee) : aucun doublon ni annulation implicite. Une transition
        deja en vol vers la meme cible n'est pas re-soumise.
        """
        if self._has_open_orders():
            self.n_deferred += 1
            self.debug(f"{self.time:%Y-%m-%d} settled: decision suspendue, ordre QQQ/SHY ouvert")
            return
        if (self._pending_target == target and self._decision_time is not None
                and self.time.date() == self._decision_time.date()):
            # Decision repetee le meme jour : rien a re-soumettre (aucun doublon).
            return
        # Cible et horodatage installes avant la liquidation. Une vente echouee
        # (annulee/refusee) laissant une quantite non nulle est reattemptee a la
        # decision hebdomadaire suivante, jamais deux fois le meme jour.
        self._pending_target = target
        self._decision_time = self.time
        other = self.shy if target == self.qqq else self.qqq
        if self.portfolio[other].invested:
            self.liquidate(other)
        self.n_switches += 1
        if target == self.qqq:
            self.n_to_qqq += 1
        else:
            self.n_to_shy += 1
        self.debug(f"{self.time:%Y-%m-%d} BTC={btc_price:,.0f} "
                   f"SMA{self.sma_window}={self.sma.current.value:,.0f} "
                   f"ROC{self.roc_window}={self.roc.current.value:+.3f} "
                   f"-> {'QQQ' if risk_on else 'SHY'} (settled: liquidation seule)")

    def _try_acquire(self, data) -> None:
        """Acquisition differee du bras "settled" (#20006), depuis on_data.

        S'execute seulement si : une cible est en attente, la barre est posterieure
        a la decision, l'autre jambe a une quantite nulle, aucun ordre QQQ/SHY n'est
        ouvert, et la barre de la cible est presente. L'intention est effacee AVANT
        la soumission (aucune reentrance, aucun achat en callback d'ordre).
        """
        if self._pending_target is None:
            return
        target = self._pending_target
        if self._decision_time is not None and self.time.date() <= self._decision_time.date():
            return
        other = self.shy if target == self.qqq else self.qqq
        if self.portfolio[other].quantity != 0:
            return
        if self._has_open_orders():
            return
        if not data.bars.contains_key(target):
            return

        decision_time = self._decision_time
        # Effacer l'intention AVANT la soumission : aucune reentrance possible.
        self._pending_target = None
        self._decision_time = None
        self.set_holdings(target, 1.0)
        self.acquire_count += 1
        if decision_time is not None:
            delay = (self.time - decision_time).total_seconds()
            self.delay_seconds += delay
            self.log(f"{self.time:%Y-%m-%d %H:%M} settled soumission d'achat {target.value} "
                     f"decision={decision_time:%Y-%m-%d %H:%M} "
                     f"delai decision->soumission={delay / 86400:.1f}j")

    def on_data(self, data):
        if self.is_warming_up:
            return
        if self.mode in REFERENCE_WEIGHTS and self.time.month != self._ref_month:
            # Reference detenue, reequilibree a la premiere barre journaliere du mois.
            self._ref_month = self.time.month
            for ticker, weight in REFERENCE_WEIGHTS[self.mode].items():
                self.set_holdings(self.ref_symbols[ticker], weight)
        if data.bars.contains_key(self.shadow_symbol):
            value = self.portfolio.total_portfolio_value
            self.plot("shadow", f"e{self.closes % 5}", value)
            self.plot("shadow", "fees", self.portfolio.total_fees / self.start_value)
            self.plot("shadow", "turnover", self.traded)
            gross = sum(abs(holding.holdings_value) for holding in self.portfolio.values())
            self.gross_sum += gross / value if value > 0 else 0.0
            self.closes += 1
            if gross == 0.0:
                # Seance cloturee sans aucune position (audit #20006).
                self.cash_closes += 1

        # Bras "settled" (#20006) : acquisition differee depuis on_data, a une
        # barre posterieure a la decision (voir _try_acquire).
        if self.mode == "gate" and self._execution_mode == "settled":
            self._try_acquire(data)

    def on_order_event(self, order_event):
        if order_event.status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            self.traded += (abs(order_event.fill_quantity * order_event.fill_price)
                            / self.portfolio.total_portfolio_value)
        if order_event.status == OrderStatus.FILLED:
            ticker = order_event.symbol.value
            self.order_counts[ticker] = self.order_counts.get(ticker, 0) + 1
        # Bras "settled" (#20006) : comptage des issues d'execution. Jamais
        # d'achat ici (l'acquisition est pilotee par on_data, pas par callback).
        if self._execution_mode == "settled":
            if order_event.status == OrderStatus.INVALID:
                self.n_invalid += 1
            elif order_event.status == OrderStatus.CANCELED:
                self.n_canceled += 1

    def on_end_of_algorithm(self):
        for ticker in ("QQQ", "SHY", "SPY", "IEF"):
            self.set_runtime_statistic(f"Orders {ticker}", str(self.order_counts.get(ticker, 0)))
        gross = self.gross_sum / self.closes if self.closes else 0.0
        self.set_runtime_statistic("Gross exposure", f"{gross:.3f}")
        self.set_runtime_statistic("Target switches", str(self.n_switches))
        self.set_runtime_statistic("Switches QQQ", str(self.n_to_qqq))
        self.set_runtime_statistic("Switches SHY", str(self.n_to_shy))
        self.set_runtime_statistic("Mode", self.mode)
        self.set_runtime_statistic("Frequency", self.frequency)
        if self._execution_mode == "settled":
            # Les "acquisitions" comptent des SOUMISSIONS d'achat, pas des
            # remplissages ; le delai va de la decision a la soumission, pas au fill.
            self.set_runtime_statistic("Execution", self._execution_mode)
            self.set_runtime_statistic("Settled decisions differees", str(self.n_deferred))
            self.set_runtime_statistic("Settled ordres annules", str(self.n_canceled))
            self.set_runtime_statistic("Settled ordres invalides", str(self.n_invalid))
            self.set_runtime_statistic("Settled acquisitions (soumissions)", str(self.acquire_count))
            self.set_runtime_statistic("Settled seances en liquidites", str(self.cash_closes))
            self.set_runtime_statistic(
                "Settled pending target (fin)",
                self._pending_target.value if self._pending_target is not None else "aucune")
            avg = self.delay_seconds / self.acquire_count / 86400 if self.acquire_count else 0.0
            self.set_runtime_statistic("Settled delai decision->soumission (j)", f"{avg:.1f}")
        final = self.portfolio.total_portfolio_value
        self.log(f"BITCOIN REGIME GATE ({self.mode}): Final=${final:,.2f}, "
                 f"Return={(final - self.start_value) / self.start_value:.2%}, gross exposure={gross:.3f}")
