# region imports
from AlgorithmImports import *

from sklearn.linear_model import LinearRegression
# endregion
# Variante d'evaluation de l'exercice 07 du chapitre 6 de Hands-On AI Trading
# (Jared Broad et al.), projet du depot Positive-Negative-Splits-ML, classe
# SplitEventsAlgorithm. Evaluee dans l'issue #19242, dont la regle de verdict et la
# grille ont ete fixees avant le premier backtest.
#
# La regle d'origine est reprise telle quelle : a chaque annonce de division d'actions
# du secteur Technologie, une regression lineaire (facteur de division, taux de
# variation de XLK sur 22 seances) predit le rendement a `hold_days` jours ; position
# de 1/`max_open` du portefeuille dans le sens de la prediction, sortie a l'ouverture
# apres `hold_days` jours ; modele reentraine chaque mois sur `lookback_years` ans.
# Seuls changent les points rendus parametrables (README.md). Avec long_only=0,
# fee_mult=1 et les autres defauts, c'est la regle d'origine.
#
# Contrat du rejeu en ombre (#18923, shadow/README.md) : dates par les parametres
# `start` et `end` sans valeur par defaut ; valeur du portefeuille a chaque cloture dans
# le graphique `shadow` (series e0..e4 a tour de role), plus `fees` et `turnover`.

from datetime import datetime


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


class SplitEventsLongOnly(QCAlgorithm):

    def initialize(self):
        start = datetime.strptime(self.get_parameter("start"), "%Y-%m-%d")
        end = datetime.strptime(self.get_parameter("end"), "%Y-%m-%d")
        self.set_start_date(start.year, start.month, start.day)
        self.set_end_date(end.year, end.month, end.day)
        self.set_cash(100_000)
        self.start_value = 100_000.0
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self.long_only = self.get_parameter("long_only", "1") == "1"
        self.fee_mult = float(self.get_parameter("fee_mult", "1"))
        self._max_open_trades = int(self.get_parameter("max_open", "4"))
        self._hold_duration = timedelta(int(self.get_parameter("hold_days", "3")))
        self._training_lookback = timedelta(
            int(self.get_parameter("lookback_years", "4")) * 365)
        self._min_dollar_volume = float(self.get_parameter("min_dollar_volume", "0"))

        self.universe_settings.resolution = Resolution.HOUR
        self.universe_settings.fill_forward = False
        self.universe_settings.asynchronous = True
        self.universe_settings.data_normalization_mode = DataNormalizationMode.RAW
        self._universe = self.add_universe(
            lambda fundamental: [
                x.symbol
                for x in fundamental
                if (x.asset_classification.morningstar_sector_code ==
                    MorningstarSectorCode.TECHNOLOGY
                    and x.dollar_volume >= self._min_dollar_volume)
            ]
        )

        # sector_prices=raw (defaut, code d'origine) : XLK herite de la normalisation RAW de
        # l'univers, et sa division de decembre 2025 apparait comme une baisse de 50 % du
        # taux de variation pendant 22 seances. `adjusted` sert au run de diagnostic (README).
        sector_mode = (DataNormalizationMode.ADJUSTED
                       if self.get_parameter("sector_prices", "raw") == "adjusted"
                       else self.universe_settings.data_normalization_mode)
        self._sector_etf = self.add_equity("XLK", self.universe_settings.resolution,
                                           data_normalization_mode=sector_mode)
        self._sector_etf.set_fee_model(_ScaledFeeModel(self.fee_mult))
        self._sector_etf.roc = self.roc(self._sector_etf.symbol, 22, Resolution.DAILY)
        self._sector_etf.roc_history = pd.Series()
        self._sector_etf.roc.updated += self._update_event_handler
        bars = self.history[TradeBar](
            self._sector_etf.symbol,
            self._training_lookback.days + self._sector_etf.roc.warm_up_period,
            Resolution.DAILY
        )
        for bar in bars:
            self._sector_etf.roc.update(bar.end_time, bar.close)

        self._target_exposure_per_trade = 1 / self._max_open_trades
        self._trades_by_symbol = {}
        self._model = LinearRegression()
        self.train(
            self.date_rules.month_start(self._sector_etf.symbol),
            self.time_rules.midnight,
            self._train
        )
        self.schedule.on(
            self.date_rules.every_day(),
            self.time_rules.midnight,
            self._scan_for_trade_exits
        )
        # Une mesure par seance, apres la derniere barre horaire.
        self.schedule.on(
            self.date_rules.every_day(self._sector_etf.symbol),
            self.time_rules.after_market_close(self._sector_etf.symbol, 1),
            self._record
        )

        self.closes = 0
        self.invested_closes = 0
        self.traded = 0.0
        self.signals = {"long": 0, "short": 0, "skip": 0}

    def on_securities_changed(self, changes):
        for security in changes.added_securities:
            security.set_fee_model(_ScaledFeeModel(self.fee_mult))

    def _update_event_handler(self, indicator, indicator_data_point):
        if not indicator.is_ready:
            return
        t = indicator_data_point.end_time
        self._sector_etf.roc_history.loc[t] = indicator_data_point.value
        self._sector_etf.roc_history = self._sector_etf.roc_history[
            self._sector_etf.roc_history.index > t - self._training_lookback
        ]

    def _train(self):
        splits = self.history[Split](self._universe.selected, self._training_lookback)
        assets_with_splits = set()
        for splits_dict in splits:
            for symbol in splits_dict.keys():
                assets_with_splits.add(symbol)
        prices = self.history(
            list(assets_with_splits), self._training_lookback,
            Resolution.DAILY,
            data_normalization_mode=DataNormalizationMode.SCALED_RAW
        )['open'].unstack(0)

        samples = np.empty((0, 3))
        for splits_dict in splits:
            for symbol, split in splits_dict.items():
                if split.type == SplitType.SPLIT_OCCURRED:
                    continue
                t = split.end_time
                entry_series = prices[symbol].loc[t < prices.index]
                if entry_series.empty or np.isnan(entry_series[0]):
                    continue
                entry_price = entry_series[0]
                exit_series = prices[symbol].loc[t + self._hold_duration < prices.index]
                if exit_series.empty or np.isnan(exit_series[0]):
                    continue
                exit_price = exit_series[0]
                roc_before = self._sector_etf.roc_history[
                    self._sector_etf.roc_history.index <= t
                ]
                if roc_before.empty:
                    continue
                sector_roc = roc_before.iloc[-1]
                sample = np.array([
                    split.split_factor,
                    sector_roc,
                    (exit_price - entry_price) / entry_price
                ])
                samples = np.append(samples, [sample], axis=0)

        self.plot("Samples", "Count", len(samples))
        if len(samples) > 2:
            self._model.fit(samples[:, :2], samples[:, -1])

    def on_splits(self, splits):
        for symbol, split in splits.items():
            if symbol == self._sector_etf.symbol:
                continue

            if (split.type == SplitType.WARNING and
                    sum(len(trades) for trades in self._trades_by_symbol.values())
                    < self._max_open_trades):
                # Ecart a l'original : sans modele ajuste, l'original leverait une erreur.
                if not hasattr(self._model, "coef_"):
                    continue
                factors = [split.split_factor, self._sector_etf.roc.current.value]
                predicted_return = self._model.predict([factors])[0]
                if predicted_return == 0:
                    continue
                side = "long" if predicted_return > 0 else "short"
                if self.long_only and side == "short":
                    side = "skip"
                self.signals[side] += 1
                self.log(f"sig {self.time:%Y-%m-%d} {symbol.value} "
                         f"f={split.split_factor:.4f} roc={factors[1]:+.4f} "
                         f"pred={predicted_return:+.5f} {side}")
                if side == "skip":
                    continue

                if symbol not in self._trades_by_symbol:
                    self._trades_by_symbol[symbol] = []
                quantity = self.calculate_order_quantity(
                    symbol, np.sign(predicted_return) * self._target_exposure_per_trade)
                if quantity == 0:
                    continue
                self._trades_by_symbol[symbol].append(
                    Trade(self, symbol, self._hold_duration, quantity))

            elif (split.type == SplitType.SPLIT_OCCURRED and
                    symbol in self._trades_by_symbol):
                for trade in self._trades_by_symbol[symbol]:
                    trade.on_split_occurred(split)

    def _scan_for_trade_exits(self):
        for symbol, trades in self._trades_by_symbol.items():
            closed_trades = []
            for i, trade in enumerate(trades):
                trade.scan(self)
                if trade.closed:
                    closed_trades.append(i)
            for i in closed_trades[::-1]:
                del trades[i]

    def on_order_event(self, event):
        if event.status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            value = abs(event.fill_quantity * event.fill_price)
            self.traded += value / self.portfolio.total_portfolio_value
            self.log(f"fill {self.time:%Y-%m-%d} {event.symbol.value} "
                     f"{event.fill_quantity:+.0f} @ {event.fill_price:.4f}")

    def _record(self):
        self.plot("shadow", f"e{self.closes % 5}", self.portfolio.total_portfolio_value)
        self.plot("shadow", "fees", self.portfolio.total_fees / self.start_value)
        self.plot("shadow", "turnover", self.traded)
        self.closes += 1
        if self.portfolio.invested:
            self.invested_closes += 1

    def on_end_of_algorithm(self):
        self.log(f"end closes={self.closes} invested={self.invested_closes} "
                 f"long={self.signals['long']} short={self.signals['short']} "
                 f"skip={self.signals['skip']}")


class Trade:
    """Une position d'evenement de division, sortie a date fixe (code d'origine)."""

    def __init__(self, algorithm, symbol, hold_duration, quantity):
        self.closed = False
        self._symbol = symbol
        self._close_time = algorithm.time + hold_duration
        self._quantity = quantity
        algorithm.market_on_open_order(symbol, quantity)

    def on_split_occurred(self, split):
        self._quantity = int(self._quantity / split.split_factor)

    def scan(self, algorithm):
        if not self.closed and self._close_time <= algorithm.time:
            algorithm.market_on_open_order(self._symbol, -self._quantity)
            self.closed = True
