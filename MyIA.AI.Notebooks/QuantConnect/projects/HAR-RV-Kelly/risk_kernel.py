# region imports
from AlgorithmImports import *
# endregion
"""Noyau de risque deterministe (#24698), partage par les strategies du depot.

Copie canonique : projects/RiskKernel/risk_kernel.py. QuantConnect n'importe que
les fichiers du projet : chaque projet qui utilise le noyau en porte une copie
identique a l'octet, et scripts/quantconnect/check_risk_kernel_copies.py echoue
des qu'une copie diverge. On modifie ici, puis on recopie.

Trois protections, choisies par le parametre `kernel` de la strategie :
- plafond : exposition brute d'au plus 90 %, sans levier ;
- stop : chaque ordre d'entree porte un stop a 2 ATR(14) sous le prix ; une
  ligne stoppee reste hors marche jusqu'au rebalancement suivant ;
- coupe-circuit : apres une seance close a -3 % ou pire, liquidation a
  l'ouverture suivante, une seance a plat, puis re-entree sur les cibles du
  dernier rebalancement.

La strategie garde ses signaux et son calendrier. Elle appelle :
- `cap(weights)` sur ses poids cibles ;
- `rebalance(weights)` a chaque rebalancement : vrai si le noyau a pris les
  ordres en charge, faux si la strategie passe les siens (modes `off`, `cap90`) ;
- `on_close()` une fois par seance close ;
- `on_order_event(event)` depuis son propre `on_order_event` ;
- `statistics()` en fin de backtest.
"""

# mode -> (plafond, stop, coupe-circuit)
MODES = {"off": (False, False, False), "cap90": (True, False, False),
         "kernel_nocb": (True, True, False), "kernel": (True, True, True)}
EXPOSURE_CAP = 0.90    # exposition brute maximale, sans levier
STOP_ATR = 2.0         # stop a 2 ATR sous le prix de l'ordre, ligne par ligne
ATR_PERIOD = 14
CB_THRESHOLD = -0.03   # coupe-circuit apres une seance a -3 % ou pire
MIN_WEIGHT = 0.001     # en dessous, la ligne est soldee


def check_mode(mode):
    """Refuse un mode inconnu (a appeler avant les controles propres a la strategie)."""
    if mode not in MODES:
        raise ValueError(f"unknown kernel {mode}")


class RiskKernel:
    """Etat et ordres du noyau pour un ensemble de lignes {ticker: Symbol}.

    L'ordre du dictionnaire `symbols` est l'ordre de passage des ordres.
    A construire dans `initialize`, apres l'enregistrement du rebalancement : la
    tache quotidienne du coupe-circuit passe alors apres lui le meme jour.
    """

    def __init__(self, algorithm, mode, symbols, schedule_symbol):
        check_mode(mode)
        self.algo = algorithm
        self.mode = mode
        self.use_cap, self.use_stop, self.use_cb = MODES[mode]
        self.symbols = dict(symbols)
        self._ticker_of = {sym.value: t for t, sym in self.symbols.items()}
        self.targets = {}
        self.stopped = {t: False for t in self.symbols}
        self.stop_ticket = {t: None for t in self.symbols}
        self.stop_level = {t: None for t in self.symbols}
        self.cb_pending = False
        self.reentry = False
        self.prev_value = None
        self.stops = 0
        self.cuts = 0
        self.invalid = 0
        self.exposure_max = 0.0
        self.sessions = 0
        self.flat_sessions = 0
        if self.use_stop:
            self.atr = {t: algorithm.atr(sym, ATR_PERIOD, MovingAverageType.SIMPLE,
                                         Resolution.DAILY)
                        for t, sym in self.symbols.items()}
        if self.use_cb:
            algorithm.schedule.on(
                algorithm.date_rules.every_day(schedule_symbol),
                algorithm.time_rules.after_market_open(schedule_symbol, 30),
                self.daily,
            )

    def cap(self, weights):
        """Plafond d'exposition brute, proportionnel sur toutes les lignes."""
        if not self.use_cap:
            return weights
        gross = sum(weights.values())
        if gross > EXPOSURE_CAP:
            return {t: w * EXPOSURE_CAP / gross for t, w in weights.items()}
        return weights

    def rebalance(self, weights):
        """Rebalancement de la strategie. Faux : la strategie passe ses ordres."""
        if not (self.use_stop or self.use_cb):
            return False
        # Le rebalancement rouvre les lignes stoppees depuis le precedent.
        self.stopped = {t: False for t in self.symbols}
        self.targets = dict(weights)
        if self.cb_pending or self.reentry:
            # Liquidation du coupe-circuit en cours : la re-entree part plus tard,
            # avec ces cibles.
            return True
        self.enter(self.targets)
        return True

    def on_close(self):
        """Cloture de la seance : exposition relevee, puis coupe-circuit a -3 %."""
        algo = self.algo
        value = algo.portfolio.total_portfolio_value
        held = sum(abs(algo.portfolio[s].holdings_value) for s in self.symbols.values())
        self.sessions += 1
        if held <= 0:
            self.flat_sessions += 1
        if value > 0:
            self.exposure_max = max(self.exposure_max, held / value)
        if (self.use_cb and held > 0 and not self.cb_pending
                and self.prev_value is not None
                and value / self.prev_value - 1 <= CB_THRESHOLD):
            # En donnees journalieres la cloture n'est connue qu'apres coup : la
            # liquidation part a l'ouverture suivante, la re-entree a celle d'apres.
            for ticker, sym in self.symbols.items():
                self.cancel_stop(ticker)
                quantity = algo.portfolio[sym].quantity
                if quantity != 0:
                    algo.market_on_open_order(sym, -quantity, tag="coupe-circuit")
            self.cb_pending = True
            self.cuts += 1
        self.prev_value = value

    def daily(self):
        """30 min apres l'ouverture : seance a plat apres une coupure, puis re-entree."""
        if self.algo.is_warming_up:
            return
        if self.cb_pending:
            self.cb_pending = False
            self.reentry = True
            return
        if self.reentry:
            self.reentry = False
            if self.targets:
                self.enter(self.targets)

    def reopen_stopped(self):
        """Variante diagnostique : les lignes stoppees reviennent sur les cibles
        du dernier rebalancement, sans attendre le suivant."""
        if self.algo.is_warming_up or not any(self.stopped.values()):
            return
        if self.cb_pending or self.reentry or not self.targets:
            return
        self.stopped = {t: False for t in self.symbols}
        self.enter(self.targets)

    def enter(self, weights):
        """Ordre deterministe : chaque ordre d'entree porte son stop a 2 ATR(14)."""
        algo = self.algo
        for ticker, sym in self.symbols.items():
            w = 0.0 if self.stopped[ticker] else weights.get(ticker, 0.0)
            if w > MIN_WEIGHT:
                if self.use_stop:
                    self.cancel_stop(ticker)
                    atr = self.atr[ticker]
                    self.stop_level[ticker] = (
                        algo.securities[sym].price - STOP_ATR * atr.current.value
                        if atr.is_ready else None)
                algo.set_holdings(sym, w, tag="rebalancement")
                self.place_stop(ticker)
            else:
                self.cancel_stop(ticker)
                algo.liquidate(sym)

    def live_stop(self, ticker):
        ticket = self.stop_ticket[ticker]
        if ticket is None:
            return None
        if ticket.status in (OrderStatus.FILLED, OrderStatus.CANCELED, OrderStatus.INVALID):
            self.stop_ticket[ticker] = None
            return None
        return ticket

    def place_stop(self, ticker):
        """Stop de la ligne a sa quantite courante (cree, ou mis a jour)."""
        sym = self.symbols[ticker]
        quantity = self.algo.portfolio[sym].quantity
        level = self.stop_level[ticker]
        if not self.use_stop or quantity <= 0 or level is None or level <= 0:
            self.cancel_stop(ticker)
            return
        ticket = self.live_stop(ticker)
        if ticket is not None:
            if ticket.quantity != -quantity:
                fields = UpdateOrderFields()
                fields.quantity = -quantity
                ticket.update(fields)
            return
        self.stop_ticket[ticker] = self.algo.stop_market_order(sym, -quantity, level,
                                                               tag="stop")

    def cancel_stop(self, ticker):
        ticket = self.live_stop(ticker)
        if ticket is not None:
            ticket.cancel()
        self.stop_ticket[ticker] = None

    def on_order_event(self, order_event):
        if self.mode == "off":
            return
        if order_event.status == OrderStatus.INVALID:
            self.invalid += 1
            return
        if order_event.status != OrderStatus.FILLED:
            return
        ticker = self._ticker_of.get(order_event.symbol.value)
        if ticker is None:
            return
        order = self.algo.transactions.get_order_by_id(order_event.order_id)
        if order.type == OrderType.STOP_MARKET:
            # Stop touche : la ligne reste hors marche jusqu'au rebalancement suivant.
            self.stopped[ticker] = True
            self.stops += 1
            self.stop_ticket[ticker] = None
        elif order.tag == "rebalancement":
            self.place_stop(ticker)

    def statistics(self):
        """Statistiques d'execution du noyau, a poser en fin de backtest."""
        return {
            "Noyau": self.mode,
            "Stops": str(self.stops),
            "Coupures": str(self.cuts),
            "Ordres invalides": str(self.invalid),
            "Exposition max": f"{self.exposure_max:.4f}",
            "Seances a plat": f"{self.flat_sessions}/{self.sessions}",
        }
