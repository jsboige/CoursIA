# region imports
from AlgorithmImports import *

# endregion
# https://www.quantconnect.com/research/15366/short-term-reversal-with-futures/
# Short Term Reversal With Futures (Jing Wu, QC research 15366, draft/pending review)
# Portage fidele verifie sous frais de courtier IBKR -- See #18466, EPIC #11698
#
# Adaptations documentees (detail et mesure dans README.md) :
#   a1  La propriete `return` de l'article est impossible en Python : `def
#       return(self)` et `x.return` sont des erreurs de syntaxe (mot reserve).
#       Renommee `return_value`. La version PEP8 annoncee par Derek Melchin
#       (STAFF) dans le fil de l'article a necessairement fait de meme.
#   a2  L'article montre le bloc selection + ordres sans son declencheur.
#       Reconstruction : le rebalancement se declenche quand au moins un
#       consolidateur hebdomadaire (mercredi) a emis dans la slice courante ET
#       que tous les SymbolData sont prets. Sans ce portillon, `is_ready`
#       (collant apres la deuxieme semaine) ferait re-trader chaque jour des
#       valeurs hebdomadaires perimees.
#   a3  Garde `qty != 0` avant chaque ordre -- mise a jour Derek Melchin
#       (STAFF) annoncee dans le fil : "Added a check to see if quantity != 0
#       before placing orders".
#   a4  Fenetre et capital non specifies par l'article : parametres
#       `start`/`end` (defaut 20160101 -> 20260630), cash 1 M, brokerage IBKR
#       marge et `seed_initial_prices` (convention du depot pour la
#       verification sous frais courtier, campagne #1630).
#   a5  La prose de l'article annonce "the intersection of the top volume
#       group and bottom open interest group" ; son code prend l'UNION des 4
#       plus BAS volume-ROC et des 4 plus HAUT OI-ROC, corrobore par le
#       commentaire du code lui-meme ("lowest volume change and highest OI
#       change"). Le port suit le code -- l'artefact executable. Divergence
#       prose/code documentee, pas tranchee en faveur de la prose.
#   a6  `self.portfolio.keys` (propriete dans l'article) se lie en METHODE sur
#       LEAN courant : "'MethodBinding' object is not iterable", mesure au
#       premier rebalancement du run 1 (crash 2017-07-19, 0 ordres). Remplace
#       par list(self.portfolio.keys()).
#
#   a7  Dimensionnement (#23689), parametre `fix` (defaut "on"). Sur un
#       contrat a terme, `calculate_order_quantity` rend deja des CONTRATS,
#       dimensionnes a la marge initiale ; l'article les divise encore par le
#       contract_multiplier, et la division entiere de Python arrondit vers
#       -inf : une jambe courte garde -1 contrat, une jambe longue tombe a 0
#       sauf sur YM. Meme motif au rollover (`quantity // multiplier`).
#       "on" : cible au notionnel, +/-0.3 x valeur / (prix x multiplicateur)
#       en contrats entiers, et report de la quantite telle quelle au
#       rollover. "off" : code de l'article, temoin. Compteurs passifs
#       (jambes, ordres, jours detenus par racine, rollovers, notionnel brut
#       et net) en statistiques d'execution, sans effet sur les ordres.


class ShortTermReversalFuturesAlgorithm(QCAlgorithm):

    def initialize(self):
        start = self.get_parameter("start", "20160101")
        end = self.get_parameter("end", "20260630")
        self.set_start_date(int(start[:4]), int(start[4:6]), int(start[6:]))
        self.set_end_date(int(end[:4]), int(end[4:6]), int(end[6:]))
        self.set_cash(1000000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        self.settings.seed_initial_prices = True  # a4
        self.fix = self.get_parameter("fix", "on") == "on"  # a7

        # a7 : compteurs passifs
        self._legs = {}  # racine -> [jambes longues, ordres longs, jambes courtes, ordres courts]
        self._days = {}  # racine -> [seances detenues longues, seances detenues courtes]
        self._roll = [0, 0, 0]  # rollovers, report nul, report reduit
        self._gross = []  # notionnel brut / valeur du portefeuille, par slice
        self._net = []

        self.tickers = [
            Futures.Currencies.CHF,
            Futures.Currencies.GBP,
            Futures.Currencies.CAD,
            Futures.Currencies.EUR,
            Futures.Indices.NASDAQ100EMini,
            Futures.Indices.Russell2000EMini,
            Futures.Indices.SP500EMini,
            Futures.Indices.Dow30EMini,
        ]
        self.length = len(self.tickers)

        self.symbol_data = {}

        for ticker in self.tickers:
            future = self.add_future(
                ticker,
                resolution=Resolution.DAILY,
                extended_market_hours=True,
                data_normalization_mode=DataNormalizationMode.BACKWARDS_RATIO,
                data_mapping_mode=DataMappingMode.OPEN_INTEREST,
                contract_depth_offset=0,
            )
            future.set_leverage(1)
            self.symbol_data[future.symbol] = SymbolData(self, future)

    def on_data(self, slice):
        self._sample_exposure()  # a7

        # a2 : re-armement du portillon hebdo avant les mises a jour
        for symbol_data in self.symbol_data.values():
            symbol_data.consolidated_this_slice = False

        for symbol, symbol_data in self.symbol_data.items():
            # Update SymbolData
            symbol_data.update(slice)

            # Rollover
            if slice.symbol_changed_events.contains_key(symbol):
                changed_event = slice.symbol_changed_events[symbol]
                old_symbol = changed_event.old_symbol
                new_symbol = changed_event.new_symbol
                tag = f"Rollover - Symbol changed at {self.time}: {old_symbol} -> {new_symbol}"
                quantity = self.portfolio[old_symbol].quantity

                # Rolling over: to liquidate any position of the old mapped
                # contract and switch to the newly mapped contract
                self.liquidate(old_symbol, tag=tag)
                if quantity != 0:  # a3
                    if self.fix:  # a7 : la quantite est deja en contrats
                        carried = int(quantity)
                    else:
                        carried = quantity // self.securities[new_symbol].symbol_properties.contract_multiplier
                    self._roll[0] += 1
                    if carried == 0:
                        self._roll[1] += 1
                    elif abs(carried) < abs(quantity):
                        self._roll[2] += 1
                    self.market_order(new_symbol, carried, tag=tag)

        # a2 : portillon hebdo -- trade seulement a l'emission hebdomadaire
        if not any(sd.consolidated_this_slice for sd in self.symbol_data.values()):
            return
        if not all(sd.is_ready for sd in self.symbol_data.values()):
            return

        # Select futures with most weekly extreme return out of lowest volume
        # change and highest OI change (a5 : union, comme le code de l'article)
        trade_group = set(
            sorted(self.symbol_data.values(), key=lambda x: x.volume_return)[: int(self.length * 0.5)]
            + sorted(self.symbol_data.values(), key=lambda x: x.open_interest_return)[-int(self.length * 0.5):]
        )
        sorted_by_returns = sorted(trade_group, key=lambda x: x.return_value)  # a1
        short_symbol = sorted_by_returns[-1].mapped
        long_symbol = sorted_by_returns[0].mapped

        # a6 : `portfolio.keys` (propriete dans l'article) se lie en methode sur
        # LEAN courant -- 'MethodBinding' object is not iterable, mesure au
        # premier rebalancement du run 1 (crash 2017-07-19, 0 ordres)
        for symbol in list(self.portfolio.keys()):
            if self.portfolio[symbol].invested and symbol not in [short_symbol, long_symbol]:
                self.liquidate(symbol)

        # Adjust for contract multiplier for order size
        for trade_symbol, magnitude in [(short_symbol, -0.3), (long_symbol, 0.3)]:
            multiplier = self.securities[trade_symbol].symbol_properties.contract_multiplier
            if self.fix:  # a7 : cible au notionnel, en contrats entiers
                price = self.securities[trade_symbol].price
                target = 0
                if price > 0:
                    target = int(round(magnitude * self.portfolio.total_portfolio_value / (price * multiplier)))
                qty = target - int(self.portfolio[trade_symbol].quantity)
            else:
                qty = self.calculate_order_quantity(trade_symbol, magnitude)
                qty = int(qty // multiplier)
            self._count_leg(trade_symbol, magnitude, qty)
            if qty != 0:  # a3
                self.market_order(trade_symbol, qty)

    # a7 : compteurs passifs, sans effet sur les ordres
    def _count_leg(self, symbol, magnitude, qty):
        counts = self._legs.setdefault(symbol.id.symbol, [0, 0, 0, 0])
        i = 0 if magnitude > 0 else 2
        counts[i] += 1
        if qty != 0:
            counts[i + 1] += 1

    def _sample_exposure(self):
        tpv = self.portfolio.total_portfolio_value
        if tpv <= 0:
            return
        values = []
        for symbol in list(self.portfolio.keys()):
            holding = self.portfolio[symbol]
            if not holding.invested:
                continue
            values.append(holding.holdings_value)
            days = self._days.setdefault(symbol.id.symbol, [0, 0])
            days[0 if holding.quantity > 0 else 1] += 1
        self._gross.append(sum(abs(v) for v in values) / tpv)
        self._net.append(sum(values) / tpv)

    def on_end_of_algorithm(self):
        for root, c in sorted(self._legs.items()):
            d = self._days.get(root, [0, 0])
            self.set_runtime_statistic(root, f"L{c[0]}/{c[1]} S{c[2]}/{c[3]} dL{d[0]} dS{d[1]}")
        self.set_runtime_statistic("roll", f"{self._roll[0]} q0={self._roll[1]} red={self._roll[2]}")
        if self._gross:
            g, n = sorted(self._gross), sorted(self._net)
            self.set_runtime_statistic("gross", f"med={g[len(g) // 2]:.2f} max={g[-1]:.2f}")
            self.set_runtime_statistic("net", f"med={n[len(n) // 2]:.2f} min={n[0]:.2f} max={n[-1]:.2f}")
            self.set_runtime_statistic("flat", f"{sum(1 for x in g if x == 0) / len(g):.2f}")


class SymbolData:
    def __init__(self, algorithm, future):
        self._future = future
        self.symbol = future.symbol
        self._is_volume_ready = False
        self._is_oi_ready = False
        self._is_return_ready = False
        self.consolidated_this_slice = False  # a2

        # create ROC(1) indicator to get the volume and open interest return,
        # and handler to update state
        self._volume_roc = RateOfChange(1)
        self._oi_roc = RateOfChange(1)
        self._return = RateOfChange(1)
        self._volume_roc.updated += self.on_volume_roc_updated
        self._oi_roc.updated += self.on_oi_roc_updated
        self._return.updated += self.on_return_updated

        # Create the consolidator with the consolidation period method, and
        # handler to update ROC indicators
        self.consolidator = TradeBarConsolidator(self.consolidation_period)
        self.oi_consolidator = OpenInterestConsolidator(self.consolidation_period)
        self.consolidator.data_consolidated += self.on_trade_bar_consolidated
        self.oi_consolidator.data_consolidated += lambda sender, oi: self._oi_roc.update(oi.time, oi.value)

        # warm up
        history = algorithm.history[TradeBar](future.symbol, 14, Resolution.DAILY)
        oi_history = algorithm.history[OpenInterest](future.symbol, 14, Resolution.DAILY)
        for bar, oi in zip(history, oi_history):
            self.consolidator.update(bar)
            self.oi_consolidator.update(oi)

    @property
    def is_ready(self):
        return (
            self._volume_roc.is_ready
            and self._oi_roc.is_ready
            and self._is_volume_ready
            and self._is_oi_ready
            and self._is_return_ready
        )

    @property
    def mapped(self):
        return self._future.mapped

    @property
    def volume_return(self):
        return self._volume_roc.current.value

    @property
    def open_interest_return(self):
        return self._oi_roc.current.value

    @property
    def return_value(self):  # a1
        return self._return.current.value

    def update(self, slice):
        if slice.bars.contains_key(self.symbol):
            self.consolidator.update(slice.bars[self.symbol])

            oi = OpenInterest(slice.time, self.symbol, self._future.open_interest)
            self.oi_consolidator.update(oi)

    def on_volume_roc_updated(self, sender, updated):
        self._is_volume_ready = True

    def on_oi_roc_updated(self, sender, updated):
        self._is_oi_ready = True

    def on_return_updated(self, sender, updated):
        self._is_return_ready = True

    def on_trade_bar_consolidated(self, sender, bar):
        self._volume_roc.update(bar.end_time, bar.volume)
        self._return.update(bar.end_time, bar.close)
        self.consolidated_this_slice = True  # a2

    def consolidation_period(self, dt):
        period = timedelta(7)

        dt = dt.replace(hour=0, minute=0, second=0, microsecond=0)
        weekday = dt.weekday()
        if weekday > 2:
            delta = weekday - 2
        elif weekday < 2:
            delta = weekday + 5
        else:
            delta = 0
        start = dt - timedelta(delta)

        return CalendarInfo(start, period)
