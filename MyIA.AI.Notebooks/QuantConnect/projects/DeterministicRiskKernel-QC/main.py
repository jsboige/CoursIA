#region imports
from AlgorithmImports import *
import numpy as np
#endregion
# Noyau de risque deterministe de Steward (Feng et al., arXiv:2610.30557, section 5.5,
# table 11), porte dans LEAN. Etape 2 de #24698 : verification independante du carnet
# QuantConnect/Python/QC-Py-45 sur le chemin momentum, avec les donnees et le modele
# d'execution de LEAN au lieu du moteur vectorise du carnet.
#
# Entrees : chaque premier jour de bourse de la semaine, les 10 ETF au plus fort momentum
# sur 126 seances en sautant les 5 dernieres, signal pris sur la cloture precedente,
# ordres MarketOnOpen. Le noyau ajoute quatre regles :
#   - stop a 2 ATR(14) sous le prix d'entree, fixe a l'ouverture de la ligne ; une ligne
#     stoppee reste a plat jusqu'au rebalancement suivant ;
#   - plafond de 40 % par groupe d'actifs, reduction au prorata ;
#   - exposition d'au plus 90 % (9 % par ligne) ;
#   - coupe-circuit apres une seance a -3 % ou pire.
# Les ecarts au carnet imposes par des donnees journalieres sont decrits dans le README.
#
# Parametre `stop_handling` (suite de l'etape 2) :
#   - `recreate` (defaut) : le stop d'une ligne est annule avant tout ordre sur elle et
#     repose a son execution ; la ligne n'a pas de stop le jour de cet ordre ;
#   - `keep` : sur une ligne qui reste detenue, le stop n'est pas annule ; sa quantite
#     passe a la quantite cible des la decision, avant l'ouverture. Seule l'ouverture
#     d'une ligne reste sans stop ce jour-la.
#
# Parametres `entries` et `seed` (ablation a 50 graines, suite de l'etape 2) :
#   - `entries=momentum` (defaut) : les entrees decrites plus haut ;
#   - `entries=random` : chaque semaine, 10 lignes tirees uniformement sans remise, avec le
#     tirage du carnet (`np.random.default_rng(seed).choice(23, 10, replace=False)`, un
#     appel par semaine, indices dans l'ordre de GROUPS). Le tirage ne depend d'aucun
#     etat du portefeuille : a graine egale, toutes les variantes recoivent les memes lignes.

GROUPS = {
    "actions_us": ["XLB", "XLE", "XLF", "XLI", "XLK", "XLP", "XLU", "XLV", "XLY", "IWM"],
    "actions_hors_us": ["EFA", "EEM", "EWJ", "VGK"],
    "obligations": ["TLT", "IEF", "LQD", "HYG", "TIP"],
    "matieres_immobilier": ["GLD", "SLV", "DBC", "VNQ"],
}

# mode : (poids par ligne, stops, plafond de groupe, coupe-circuit) -- memes variantes
# que la table VARIANTES du carnet QC-Py-45.
MODES = {
    "nokernel": (0.10, False, False, False),
    "exposure90": (0.09, False, False, False),
    "kernel_nocb": (0.09, True, True, False),
    "kernel": (0.09, True, True, True),
    # kernel_sized (point 2 de #25532) : poids par ligne None -> dimensionnement a
    # risque fixe : 0,5 % du capital risque par ligne, distance au stop = 2 ATR(14),
    # exposition totale plafonnee a 90 %.
    "kernel_sized": (None, True, True, True),
}

FEE_RATE = 0.0005      # 5 points de base par cote
STOP_ATR_MULT = 2.0
GROUP_CAP = 0.40
CB_THRESHOLD = -0.03
TOP_N = 10
RISK_PER_LINE = 0.005   # 0,5 % du capital risque par ligne (mode kernel_sized)
MAX_EXPOSURE = 0.90     # plafond d'exposition totale (mode kernel_sized)
STOP_HANDLING = ("recreate", "keep")   # parametre stop_handling, defaut en tete
ENTRIES = ("momentum", "random")       # parametre entries, defaut en tete
N_LOGGED_DRAWS = 3                     # tirages journalises, pour le controle contre le carnet


class ProportionalFeeModel(FeeModel):
    """Frais proportionnels a la valeur de l'ordre, comme dans le carnet."""

    def get_order_fee(self, parameters):
        value = abs(parameters.order.quantity) * parameters.security.price
        return OrderFee(CashAmount(FEE_RATE * value, "USD"))


class DeterministicRiskKernelAlgorithm(QCAlgorithm):

    def initialize(self):
        self._mode = self.get_parameter("mode", "kernel").lower()
        if self._mode not in MODES and self._mode != "spy":
            raise ValueError(f"unknown mode parameter: {self._mode} "
                             f"({' | '.join(list(MODES) + ['spy'])})")
        self._stop_handling = self.get_parameter("stop_handling", "recreate").lower()
        if self._stop_handling not in STOP_HANDLING:
            raise ValueError(f"unknown stop_handling parameter: {self._stop_handling} "
                             f"({' | '.join(STOP_HANDLING)})")
        self._entries = self.get_parameter("entries", "momentum").lower()
        if self._entries not in ENTRIES:
            raise ValueError(f"unknown entries parameter: {self._entries} "
                             f"({' | '.join(ENTRIES)})")
        self._seed = int(self.get_parameter("seed", "0"))
        self._rng = np.random.default_rng(self._seed)
        self._n_draws = 0

        start = self.get_parameter("start_date", "2015-01-02")
        end = self.get_parameter("end_date", "2026-07-31")
        self.set_start_date(datetime.strptime(start, "%Y-%m-%d"))
        self.set_end_date(datetime.strptime(end, "%Y-%m-%d"))
        self.set_cash(100000)

        self._spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.securities[self._spy].set_fee_model(ProportionalFeeModel())
        self._symbols = []
        self._group = {}
        self._closes = {}
        self._atr = {}
        for group, tickers in GROUPS.items():
            for ticker in tickers:
                security = self.add_equity(ticker, Resolution.DAILY)
                security.set_fee_model(ProportionalFeeModel())
                symbol = security.symbol
                self._symbols.append(symbol)
                self._group[symbol] = group
                self._closes[symbol] = RollingWindow[float](132)
                self._atr[symbol] = self.atr(symbol, 14, MovingAverageType.SIMPLE, Resolution.DAILY)
        self.set_warm_up(timedelta(days=200))

        if self._mode == "spy":
            self._weight, self._use_stops, self._use_cap, self._use_cb = 1.0, False, False, False
        else:
            self._weight, self._use_stops, self._use_cap, self._use_cb = MODES[self._mode]

        self._lines = []
        self._stopped = set()
        self._stop_level = {}
        self._stop_tickets = {}
        self._atr_signal = {}
        self._last_week = None
        self._cb_pending = False
        self._reentry = False
        self._prev_close_value = None
        self._spy_bought = False

        # Compteurs de controle, publies en statistiques d'execution.
        self._n_stops = 0
        self._n_stops_rule = 0      # stops executes au plus bas de l'ouverture et du stop
        self._n_cuts = 0
        self._n_invalid = 0
        self._n_kept = 0            # stops gardes sur une ligne redimensionnee (mode keep)
        self._n_kept_failed = 0     # mises a jour refusees, stop annule a la place
        self._n_logged = 0
        self._exposure_max = 0.0
        self._cash_min = float("inf")
        self._group_max = 0.0
        self._seen_dates = set()   # dates distinctes vues par on_data (point 1 de #25532)
        self._n_flat = 0          # seances a plat : aucune position de l'univers detenue

        # Decisions avant l'ouverture, sur la cloture de la veille.
        self.schedule.on(self.date_rules.every_day(self._spy),
                         self.time_rules.before_market_open(self._spy, 60),
                         self._before_open)
        # Trace journaliere `shadow` (contrat #18923) : valeur du portefeuille a l'ouverture
        # de chaque seance de SPY, repartie sur e0..e4.
        self._trace_count = 0
        self.schedule.on(self.date_rules.every_day(self._spy),
                         self.time_rules.after_market_open(self._spy, 0),
                         self._trace)

    # ------------------------------------------------------------------ donnees

    def on_data(self, slice):
        if not self.is_warming_up:
            self._seen_dates.add(self.time.date())
        for symbol in self._symbols:
            bar = slice.bars.get(symbol)
            if bar is not None:
                self._closes[symbol].add(float(bar.close))
        if self.is_warming_up or self._mode == "spy":
            return
        value = self.portfolio.total_portfolio_value
        held = sum(abs(self.portfolio[s].holdings_value) for s in self._symbols)
        if held == 0:
            self._n_flat += 1
        self._exposure_max = max(self._exposure_max, held / value)
        self._cash_min = min(self._cash_min, float(self.portfolio.cash))
        for group in GROUPS:
            weight = sum(self.portfolio[s].holdings_value for s in self._symbols
                         if self._group[s] == group) / value
            self._group_max = max(self._group_max, weight)
        invested = held > 0
        if (self._use_cb and invested and self._prev_close_value is not None
                and value / self._prev_close_value - 1 <= CB_THRESHOLD):
            # Seance a -3 % ou pire : en donnees journalieres la cloture n'est connue
            # qu'apres coup, la liquidation part donc a l'ouverture suivante.
            for symbol in self._symbols:
                self._cancel_stop(symbol)
                self._stop_level.pop(symbol, None)
                quantity = self.portfolio[symbol].quantity
                if quantity != 0:
                    self.market_on_open_order(symbol, -quantity, tag="coupe-circuit")
            self._cb_pending = True
            self._n_cuts += 1
        self._prev_close_value = value

    # ------------------------------------------------------------------ decisions

    def _before_open(self):
        if self.is_warming_up:
            return
        if self._mode == "spy":
            if not self._spy_bought and self.securities[self._spy].price > 0:
                quantity = int(0.999 * self.portfolio.total_portfolio_value
                               / self.securities[self._spy].price)
                self.market_on_open_order(self._spy, quantity, tag="spy")
                self._spy_bought = True
            return

        week = self.time.isocalendar()[:2]
        new_week = week != self._last_week
        self._last_week = week
        if new_week:
            self._lines = self._select()
            self._stopped.clear()
        if self._cb_pending:
            # La liquidation du coupe-circuit s'execute a cette ouverture ; retour a la
            # suivante, avec les lignes de la semaine.
            self._cb_pending = False
            self._reentry = True
            return
        if new_week or self._reentry:
            self._reentry = False
            self._atr_signal = {s: self._atr[s].current.value for s in self._symbols}
            self._rebalance_to(self._target_weights(self._lines))

    def _select(self):
        if self._entries == "random":
            index = self._rng.choice(len(self._symbols), TOP_N, replace=False)
            self._n_draws += 1
            if self._n_draws <= N_LOGGED_DRAWS:
                self.log(f"tirage {self._n_draws} {self.time.date()} graine={self._seed} "
                         f"indices={','.join(str(int(i)) for i in index)}")
            return [self._symbols[int(i)] for i in index]
        scores = {}
        for symbol in self._symbols:
            window = self._closes[symbol]
            if window.is_ready and window[131] > 0:
                scores[symbol] = window[5] / window[131] - 1
        return sorted(scores, key=scores.get, reverse=True)[:TOP_N]

    def _target_weights(self, lines):
        if self._mode == "kernel_sized":
            # Dimensionnement a risque fixe (point 2 de #25532) : la quantite par
            # ligne porte 0,5 % du capital si le stop (2 ATR sous l'entree) se
            # declenche. Exprimee en poids (quantity * price / value) pour reutiliser
            # le plafond de groupe ; l'exposition totale est plafonnee ensuite a 90 %.
            value = self.portfolio.total_portfolio_value
            weights = {}
            for symbol in lines:
                price = self.securities[symbol].price
                atr = self._atr[symbol].current.value
                if price <= 0 or not atr or atr <= 0:
                    continue
                quantity = RISK_PER_LINE * value / (STOP_ATR_MULT * atr)
                weights[symbol] = quantity * price / value
        else:
            weights = {symbol: self._weight for symbol in lines}
        if self._use_cap:
            for group in GROUPS:
                members = [s for s in weights if self._group[s] == group]
                total = sum(weights[s] for s in members)
                if total > GROUP_CAP + 1e-12:
                    for symbol in members:
                        weights[symbol] *= GROUP_CAP / total
        if self._mode == "kernel_sized":
            total = sum(weights.values())
            if total > MAX_EXPOSURE + 1e-12:
                scale = MAX_EXPOSURE / total
                for symbol in weights:
                    weights[symbol] *= scale
        for symbol in self._stopped:
            weights[symbol] = 0.0
        return weights

    def _rebalance_to(self, weights):
        value = self.portfolio.total_portfolio_value
        for symbol in self._symbols:
            price = self.securities[symbol].price
            if price <= 0:
                continue
            target = int(weights.get(symbol, 0.0) * value / price)
            held = self.portfolio[symbol].quantity
            delta = target - held
            if delta != 0:
                if not (self._stop_handling == "keep" and held > 0 and target > 0
                        and self._resize_stop(symbol, target)):
                    # Le stop est repose a l'execution, sur la nouvelle quantite.
                    self._cancel_stop(symbol)
                self.market_on_open_order(symbol, delta, tag="rebalancement")

    def _live_stop(self, symbol):
        ticket = self._stop_tickets.get(symbol)
        if ticket is None or ticket.status in (OrderStatus.FILLED, OrderStatus.CANCELED,
                                               OrderStatus.INVALID):
            return None
        return ticket

    def _resize_stop(self, symbol, quantity):
        # Le stop garde couvre la quantite cible : s'il se declenche a l'ouverture, la
        # ligne entiere est vendue, quel que soit l'ordre d'execution du stop et de
        # l'ordre MarketOnOpen, comme dans le carnet.
        ticket = self._live_stop(symbol)
        if ticket is None:
            return False
        if ticket.quantity != -quantity:
            fields = UpdateOrderFields()
            fields.quantity = -quantity
            if not ticket.update(fields).is_success:
                self._n_kept_failed += 1
                return False
        self._n_kept += 1
        return True

    def _cancel_stop(self, symbol):
        ticket = self._stop_tickets.pop(symbol, None)
        if ticket is not None and ticket.status not in (OrderStatus.FILLED, OrderStatus.CANCELED):
            ticket.cancel()

    # ------------------------------------------------------------------ executions

    def on_order_event(self, order_event):
        if order_event.status == OrderStatus.INVALID:
            self._n_invalid += 1
            return
        if order_event.status != OrderStatus.FILLED:
            return
        symbol = order_event.symbol
        if symbol == self._spy or not self._use_stops:
            return
        order = self.transactions.get_order_by_id(order_event.order_id)
        if order.type == OrderType.STOP_MARKET:
            level = self._stop_level.pop(symbol, None)
            self._stop_tickets.pop(symbol, None)
            self._stopped.add(symbol)
            self._n_stops += 1
            security = self.securities[symbol]
            if level is not None and abs(order_event.fill_price - min(security.open, level)) < 0.005:
                self._n_stops_rule += 1
            if self._n_logged < 15 and level is not None:
                self._n_logged += 1
                self.log(f"stop {symbol.value} niveau={level:.4f} execution={order_event.fill_price:.4f} "
                         f"ouverture={security.open:.4f} plus_bas={security.low:.4f}")
            return
        quantity = self.portfolio[symbol].quantity
        if quantity <= 0:
            self._stop_level.pop(symbol, None)
            return
        if self._stop_handling == "keep" and self._live_stop(symbol) is not None:
            # Stop garde pendant le redimensionnement : sa quantite suit la position.
            ticket = self._stop_tickets[symbol]
            if ticket.quantity != -quantity:
                fields = UpdateOrderFields()
                fields.quantity = -quantity
                if ticket.update(fields).is_success:
                    return
                self._n_kept_failed += 1
                self._cancel_stop(symbol)
            else:
                return
        if symbol not in self._stop_level:
            # Ligne ouverte : stop fixe une fois pour toutes, sous le prix d'entree.
            self._stop_level[symbol] = order_event.fill_price - STOP_ATR_MULT * self._atr_signal[symbol]
        self._stop_tickets[symbol] = self.stop_market_order(symbol, -quantity,
                                                            self._stop_level[symbol], tag="stop")

    # ------------------------------------------------------------------ traces

    def _trace(self):
        self.plot("shadow", f"e{self._trace_count % 5}", self.portfolio.total_portfolio_value)
        self._trace_count += 1

    def on_end_of_algorithm(self):
        self.set_runtime_statistic("Stops", str(self._n_stops))
        self.set_runtime_statistic("Stops au min(ouverture, stop)", str(self._n_stops_rule))
        self.set_runtime_statistic("Coupures", str(self._n_cuts))
        self.set_runtime_statistic("Ordres invalides", str(self._n_invalid))
        self.set_runtime_statistic("Traitement du stop", self._stop_handling)
        self.set_runtime_statistic("Entrees", self._entries)
        self.set_runtime_statistic("Graine", str(self._seed) if self._entries == "random" else "-")
        self.set_runtime_statistic("Tirages", str(self._n_draws))
        self.set_runtime_statistic("Stops gardes au redimensionnement", str(self._n_kept))
        self.set_runtime_statistic("Mises a jour de stop refusees", str(self._n_kept_failed))
        self.set_runtime_statistic("Exposition max", f"{self._exposure_max:.4f}")
        self.set_runtime_statistic("Liquidites min", f"{self._cash_min:.2f}")
        self.set_runtime_statistic("Poids de groupe max", f"{self._group_max:.4f}")
        self.set_runtime_statistic("Dates vues par on_data", str(len(self._seen_dates)))
        self.set_runtime_statistic("Seances a plat", str(self._n_flat))
