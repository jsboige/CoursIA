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
# Defaut porte tel quel, non corrige : au rollover, l'article divise par le
# contract_multiplier une quantite deja exprimee en contrats
# (`portfolio[old].quantity // multiplier`), ce qui ecrase la position
# reportee vers ~0. Conserve parce que le rebalancement hebdomadaire
# re-cible +/-0.3 la semaine suivante : l'effet est borne et measurable.


class ShortTermReversalFuturesAlgorithm(QCAlgorithm):

    def initialize(self):
        start = self.get_parameter("start", "20160101")
        end = self.get_parameter("end", "20260630")
        self.set_start_date(int(start[:4]), int(start[4:6]), int(start[6:]))
        self.set_end_date(int(end[:4]), int(end[4:6]), int(end[6:]))
        self.set_cash(1000000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        self.settings.seed_initial_prices = True  # a4

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
                    self.market_order(
                        new_symbol,
                        quantity // self.securities[new_symbol].symbol_properties.contract_multiplier,
                        tag=tag,
                    )

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
            qty = self.calculate_order_quantity(trade_symbol, magnitude)
            multiplier = self.securities[trade_symbol].symbol_properties.contract_multiplier
            qty = int(qty // multiplier)
            if qty != 0:  # a3
                self.market_order(trade_symbol, qty)


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
