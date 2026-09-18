# Opening Range Breakout for Stocks in Play
#
# Portage de l'article QuantConnect Research 18444 (Derek Melchin, QC Staff),
# lui-meme une reproduction partielle du papier Zarattini, Barbon & Aziz 2024
# "A Profitable Day Trading Strategy For The U.S. Equity Market"
# (SSRN 4729284, DOI 10.2139/ssrn.4729284).
#
# Mecanisme : range d'ouverture de 5 minutes sur les 20 actions les plus
# "in play" (volume 5 min du jour / moyenne 14 j du volume 5 min > 1) issues
# des 1 000 actions les plus liquides (prix > 5 $, ATR(14) > 0,50 $).
# Long sur cassure du haut du range apres barre d'ouverture haussiere,
# short symetrique. Stop = entree -+ k x ATR(14). Sizing a 1 % de risque
# par position, plafonne au poids equal-weight. Sortie a la cloture.
#
# Garde-fous du portage (issue #16355) :
#   1. Fenetre pleine 2016-2023, dev 2016-2019 / OOS 2020-2023 (parametres
#      start_date / end_date ci-dessous).
#   2. Frais reelistes : modeles QC par defaut (commissions + slippage),
#      la communaute mesure ~25 % de drag sur le PnL.
#   3. Params papier (5 min / 1000) ET variante communaute (1 min / 2000)
#      via les parametres opening_minutes / universe_size.
#   4. Si l'edge ne survit pas aux frais sur la fenetre pleine : verdict
#      IGNORE avec preuve, la piste famille se referme.

from AlgorithmImports import *
import math
from datetime import datetime as py_datetime, time as datetime_time, timedelta


class SymbolData:
    """Etat par symbole : range d'ouverture, volume relatif, ATR."""

    def __init__(self, algorithm: QCAlgorithm, symbol: Symbol, opening_minutes: int,
                 relvol_days: int, atr_period: int) -> None:
        self.symbol = symbol
        self.opening_minutes = opening_minutes
        self.opening_bar: TradeBar | None = None
        self.opening_volume_history = RollingWindow[float](relvol_days)
        self.current_opening_volume: float | None = None
        self.atr = AverageTrueRange(atr_period, MovingAverageType.WILDERS)
        algorithm.subscription_manager.add_consolidator(symbol, self._consolidator(algorithm))

    def _consolidator(self, algorithm: QCAlgorithm) -> TradeBarConsolidator:
        consolidator = TradeBarConsolidator(timedelta(minutes=self.opening_minutes))
        consolidator.data_consolidated += self._on_opening_bar
        return consolidator

    def _on_opening_bar(self, sender: object, bar: TradeBar) -> None:
        heure = bar.end_time.time()
        # Premiere barre de la journee : c'est le range d'ouverture.
        if heure <= datetime_time(9, 30 + self.opening_minutes + 1):
            if self.current_opening_volume is not None:
                self.opening_volume_history.add(self.current_opening_volume)
            self.opening_bar = bar
            self.current_opening_volume = float(bar.volume)
        else:
            self.opening_bar = None

    def on_daily_bar(self, bar: TradeBar) -> None:
        self.atr.update(bar)

    @property
    def relative_volume(self) -> float:
        """Volume 5 min du jour / moyenne 14 j du volume 5 min d'ouverture."""
        if self.current_opening_volume is None or self.opening_volume_history.count < 3:
            return 0.0
        moyenne = sum(self.opening_volume_history) / self.opening_volume_history.count
        return self.current_opening_volume / moyenne if moyenne > 0 else 0.0


class OpeningRangeBreakout(QCAlgorithm):

    def initialize(self) -> None:
        # Fenetres dev/OOS passees en parametres de backtest ; defaut = dev.
        debut = self.get_parameter("start_date", "2016-01-01")
        fin = self.get_parameter("end_date", "2019-12-31")
        self.set_start_date(py_datetime.strptime(debut, "%Y-%m-%d"))
        self.set_end_date(py_datetime.strptime(fin, "%Y-%m-%d"))
        self.set_cash(100_000)

        self.universe_size = int(self.get_parameter("universe_size", 1000))
        self.max_positions = int(self.get_parameter("max_positions", 20))
        self.opening_minutes = int(self.get_parameter("opening_minutes", 5))
        self.atr_threshold = float(self.get_parameter("atr_threshold", 0.50))
        # Multiplicateur k du stop (entree -+ k x ATR). Le corps de l'article
        # 18444 ne chiffre pas k ; les backtests sources l'utilisent a 1.0.
        self.stop_atr_distance = float(self.get_parameter("stop_atr_distance", 1.0))
        self.risk_per_trade = float(self.get_parameter("risk_per_trade", 0.01))

        self.set_benchmark("SPY")
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE)
        # OrderId du ticket d'entree -> (symbole, direction, prix de stop) ;
        # le stop de sortie n'est place qu'une fois l'entree remplie.
        self._stops_en_attente: dict[int, tuple[Symbol, int, float]] = {}

        # Univers : actions US, minute sur les selectionnees (le range
        # d'ouverture exige la resolution minute ; RAM documentee comme
        # contrainte par la communaute -- reduire universe_size si besoin).
        self.universe_settings.resolution = Resolution.MINUTE
        self.universe_settings.leverage = 1.0
        self._symbols: dict[Symbol, SymbolData] = {}
        self._daily_consolidators: dict[Symbol, TradeBarConsolidator] = {}
        self.add_universe(self._select_coarse)

        # Scan d'entree a la cloture de la barre d'ouverture.
        self.schedule.on(
            self.date_rules.every_day(),
            self.time_rules.at(9, 30 + self.opening_minutes),
            self._scan_entries,
        )
        # Sortie totale juste avant la cloture (strategie intraday).
        self.schedule.on(
            self.date_rules.every_day(),
            self.time_rules.at(15, 50),
            self._liquidate_all,
        )

    def _select_coarse(self, coarse: list[CoarseFundamental]) -> list[Symbol]:
        triees = sorted(
            (c for c in coarse if c.price > 5 and c.dollar_volume > 0),
            key=lambda c: c.dollar_volume,
            reverse=True,
        )[: self.universe_size]
        selection = [c.symbol for c in triees]
        # Deselection : retirer l'etat des symboles partis.
        for symbol in list(self._symbols):
            if symbol not in selection and not self.portfolio[symbol].invested:
                if symbol in self._daily_consolidators:
                    self.subscription_manager.remove_consolidator(
                        symbol, self._daily_consolidators.pop(symbol)
                    )
                self._symbols.pop(symbol, None)
        return selection

    def on_securities_changed(self, changes: SecurityChanges) -> None:
        for change in changes.added_securities:
            symbol = change.symbol
            if symbol not in self._symbols:
                self._symbols[symbol] = SymbolData(
                    self, symbol, self.opening_minutes, 14, 14
                )
                # Barres journalieres pour l'ATR(14), independantes du
                # consolidateur d'ouverture.
                daily = TradeBarConsolidator(timedelta(days=1))
                daily.data_consolidated += lambda s, b, sym=symbol: self._on_daily(sym, b)
                self.subscription_manager.add_consolidator(symbol, daily)
                self._daily_consolidators[symbol] = daily

    def _on_daily(self, symbol: Symbol, bar: TradeBar) -> None:
        data = self._symbols.get(symbol)
        if data is not None:
            data.on_daily_bar(bar)

    def _n_invested(self) -> int:
        return sum(1 for s in self._symbols if self.portfolio[s].invested)

    def _scan_entries(self) -> None:
        if self._n_invested() >= self.max_positions:
            return
        candidates = []
        for symbol, data in self._symbols.items():
            if data.opening_bar is None or not data.atr.is_ready:
                continue
            if data.relative_volume > 1 and data.atr > self.atr_threshold:
                candidates.append((data.relative_volume, symbol, data))
        candidates.sort(key=lambda t: t[0], reverse=True)
        places_disponibles = self.max_positions - self._n_invested()
        for _, symbol, data in candidates[:places_disponibles]:
            self._place_entry(symbol, data)

    def _place_entry(self, symbol: Symbol, data: SymbolData) -> None:
        barre = data.opening_bar
        atr = float(data.atr)
        if barre.close > barre.open:
            entree, stop = float(barre.high), float(barre.high) - self.stop_atr_distance * atr
            direction = 1
        elif barre.close < barre.open:
            entree, stop = float(barre.low), float(barre.low) + self.stop_atr_distance * atr
            direction = -1
        else:
            return
        if direction == 1 and stop >= entree:
            return
        if direction == -1 and stop <= entree:
            return
        risque_dollars = self.risk_per_trade * self.portfolio.total_portfolio_value
        distance = abs(entree - stop)
        if distance <= 0:
            return
        quantite = math.floor(risque_dollars / distance)
        # Plafond equal-weight : au plus 1 / max_positions de la valeur.
        plafond = math.floor(
            self.portfolio.total_portfolio_value / self.max_positions / entree
        )
        quantite = min(quantite, plafond)
        if quantite <= 0:
            return
        ticket = self.stop_market_order(symbol, direction * quantite, entree, "Entree ORB")
        # Stop de sortie des que l'entree est declenchee.
        self._stops_en_attente[ticket.order_id] = (symbol, direction, stop)

    def on_order_event(self, order_event: OrderEvent) -> None:
        if order_event.status != OrderStatus.FILLED:
            return
        en_attente = self._stops_en_attente.get(order_event.order_id)
        if en_attente is not None:
            symbol, direction, stop = en_attente
            self.stop_market_order(symbol, -direction * abs(order_event.fill_quantity), stop, "Stop ORB")
            del self._stops_en_attente[order_event.order_id]

    def _liquidate_all(self) -> None:
        self.liquidate()
