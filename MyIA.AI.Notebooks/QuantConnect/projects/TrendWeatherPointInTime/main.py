# region imports
from AlgorithmImports import *
from alpha_models import TrendStocksAlpha, AllWeatherAlpha
from portfolio_construction import MultiStrategyPCM
# endregion
# Variante d'evaluation du projet du depot Framework_Composite_TrendWeather (composite
# TrendStocks 75 % + All Weather 25 %). Evaluee dans l'issue #19393, dont la regle de
# verdict et la grille ont ete fixees avant le premier backtest.
#
# La regle d'origine est reprise telle quelle. Seuls changent les points rendus
# parametrables (README.md) :
# - `universe` : `fixed` = les 15 titres fixes dans le code d'origine ; `pit` = chaque mois,
#   les `top_n` plus grandes capitalisations d'actions americaines, d'apres les donnees
#   fondamentales disponibles a cette date ;
# - `trend_alloc` (part de la poche tendance), `top_n`, `weighting` (`momentum` ou `equal`),
#   `fee_mult` (frais du courtier multiplies, identite a 1).
# Avec universe=fixed et les autres defauts, c'est la regle d'origine.
#
# Contrat du rejeu en ombre (#18923, shadow/README.md) : dates par les parametres
# `start` et `end` sans valeur par defaut ; valeur du portefeuille a chaque cloture dans
# le graphique `shadow` (series e0..e4 a tour de role), plus `fees` et `turnover`.

from datetime import datetime

TREND_TICKERS = [
    "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA",
    "JPM", "V", "MA",
    "UNH", "JNJ",
    "XOM", "CVX",
    "HD", "PG", "KO"
]
AW_TICKERS = ["SPY", "IEF", "GLD", "XLP"]


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


class _Initializer(BrokerageModelSecurityInitializer):
    """Initialisation du courtier, plus le prix connu a l'ajout et les frais mis a l'echelle."""

    def __init__(self, brokerage_model, seeder, fee_mult):
        super().__init__(brokerage_model, seeder)
        self._fee_mult = fee_mult

    def initialize(self, security):
        super().initialize(security)
        if self._fee_mult != 1.0:
            security.set_fee_model(_ScaledFeeModel(self._fee_mult))


class TrendWeatherPointInTime(QCAlgorithm):

    def initialize(self):
        start = datetime.strptime(self.get_parameter("start"), "%Y-%m-%d")
        end = datetime.strptime(self.get_parameter("end"), "%Y-%m-%d")
        self.set_start_date(start.year, start.month, start.day)
        self.set_end_date(end.year, end.month, end.day)
        self.set_cash(100000)
        self.start_value = 100000.0
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self.universe_mode = self.get_parameter("universe", "fixed")
        trend_alloc = float(self.get_parameter("trend_alloc", "0.75"))
        self.top_n = int(self.get_parameter("top_n", "15"))
        weighting = self.get_parameter("weighting", "momentum")
        fee_mult = float(self.get_parameter("fee_mult", "1"))
        pit = self.universe_mode == "pit"

        if pit or fee_mult != 1.0:
            seeder = FuncSecuritySeeder(self.get_last_known_prices) if pit else SecuritySeeder.NULL
            self.set_security_initializer(_Initializer(self.brokerage_model, seeder, fee_mult))

        for ticker in AW_TICKERS + ([] if pit else TREND_TICKERS):
            self.add_equity(ticker, Resolution.DAILY)

        self._trend = TrendStocksAlpha(
            tickers=None if pit else TREND_TICKERS,
            exclude=AW_TICKERS,
            weighting=weighting,
            warm_new=pit,
        )
        if pit:
            self.universe_settings.resolution = Resolution.DAILY
            self._sel_month = -1
            self.add_universe(self._select)

        self.set_alpha(CompositeAlphaModel(
            self._trend,
            AllWeatherAlpha(AW_TICKERS)
        ))

        self.set_portfolio_construction(MultiStrategyPCM(
            alpha_allocations={
                "TrendStocks": trend_alloc,
                "AllWeather": 1.0 - trend_alloc,
            },
            rebalance=timedelta(days=31)
        ))

        self.set_risk_management(NullRiskManagementModel())
        self.set_execution(ImmediateExecutionModel())
        self.set_benchmark("SPY")
        self.set_warm_up(270, Resolution.DAILY)

        spy = self.securities["SPY"].symbol
        self.schedule.on(
            self.date_rules.every_day(spy),
            self.time_rules.after_market_close(spy, 1),
            self._record
        )
        self.closes = 0
        self.invested_closes = 0
        self.traded = 0.0

    def _select(self, fundamental):
        """Univers ex ante : les top_n plus grandes capitalisations, une fois par mois."""
        if self.time.month == self._sel_month:
            return Universe.UNCHANGED
        self._sel_month = self.time.month
        rows = [
            f for f in fundamental
            if f.has_fundamental_data and f.price > 5 and f.market_cap > 0
            and f.security_reference.is_primary_share
            and not f.security_reference.is_depositary_receipt
        ]
        rows.sort(key=lambda f: f.market_cap, reverse=True)
        chosen = [f.symbol for f in rows[:self.top_n]]
        self._trend.members = chosen
        self.log(f"select {self.time:%Y-%m-%d} " + " ".join(s.value for s in chosen))
        return chosen

    def on_order_event(self, event):
        if event.status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            value = abs(event.fill_quantity * event.fill_price)
            self.traded += value / self.portfolio.total_portfolio_value
            self.log(f"fill {self.time:%Y-%m-%d} {event.symbol.value} "
                     f"{event.fill_quantity:+.0f} @ {event.fill_price:.4f}")

    def _record(self):
        if self.is_warming_up:
            return
        self.plot("shadow", f"e{self.closes % 5}", self.portfolio.total_portfolio_value)
        self.plot("shadow", "fees", self.portfolio.total_fees / self.start_value)
        self.plot("shadow", "turnover", self.traded)
        self.closes += 1
        if self.portfolio.invested:
            self.invested_closes += 1

    def on_end_of_algorithm(self):
        self.log(f"end closes={self.closes} invested={self.invested_closes} "
                 f"universe={self.universe_mode} final={self.portfolio.total_portfolio_value:.2f}")
