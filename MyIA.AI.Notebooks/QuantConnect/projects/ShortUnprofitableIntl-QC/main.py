#region imports
from AlgorithmImports import *

from datetime import datetime
#endregion
# Vente à découvert des grandes sociétés étrangères peu rentables, couverte
# par SPY — mesure pré-enregistrée sur #24228.
# Source : article de recherche QuantConnect n° 21634, « Shorting unprofitable
# international stocks against the S&P 500 » (2026). La règle reprend l'idée du facteur de
# rentabilité (Hou, Xue et Zhang, RFS 2015 ; Fama et French, JFE 2015), mais
# hors des États-Unis et sur la seule jambe courte.
# Règle : SPY à 50 % ; vente à découvert, à poids égaux, des sociétés non
# américaines cotées aux États-Unis, hors SPY, de plus de 10 milliards de
# dollars de capitalisation, dont la rentabilité des capitaux propres est
# sous la médiane du groupe. Sélection et rééquilibrage chaque jour.
#
# Version 2 (#18923) : contrat du rejeu en ombre. La première version lisait
# `start_date` et `end_date` avec des valeurs par défaut et ne traçait que la
# valeur du portefeuille, à l'ouverture de chaque séance : un passage d'ombre
# était refusé faute de `fees` et de `turnover`, et la valeur d'ouverture
# n'était pas celle de la clôture que demande le contrat. La règle de trading
# ne change pas.

MODES = ("strategy", "all", "half", "spy", "6040")


class ShortUnprofitableIntlAlgorithm(QCAlgorithm):

    def initialize(self):
        # Modes (#24228) : `strategy` (défaut) applique la règle de l'article ;
        # `all` vend à découvert toutes les sociétés éligibles, sans le
        # découpage à la médiane (diagnostic du filtre) ; `half` détient SPY à
        # 50 % sans jambe courte (diagnostic de la jambe courte) ; `spy` (SPY
        # détenu) et `6040` (SPY 60 %, BND 40 %) sont les références du verdict.
        self._mode = self.get_parameter("mode", "strategy").lower()
        if self._mode not in MODES:
            raise ValueError(f"unknown mode parameter: {self._mode} ({' | '.join(MODES)})")

        # Dates sans valeur par défaut (contrat d'ombre #18923) : un backtest
        # lancé sans elles échoue au lieu de tourner sur une période implicite.
        # La fenêtre du verdict de #24228 est 2009-10-01 -> 2026-07-31 ; une fin
        # explicite évite aussi que la coupure d'environ 90 jours de certains
        # nœuds de backtest la raccourcisse en silence.
        start = self.get_parameter("start")
        end = self.get_parameter("end")
        if not start or not end:
            raise ValueError("parameters start and end are required (ISO dates)")
        self.set_start_date(datetime.strptime(start, "%Y-%m-%d"))
        self.set_end_date(datetime.strptime(end, "%Y-%m-%d"))
        self.set_cash(100000)
        self._start_value = 100000.0
        self._traded = 0.0  # rotation cumulée, en fraction du portefeuille
        # Pas de modèle de courtage explicite : l'article n'en montre pas. Tous
        # les modes partagent le modèle par défaut de Lean.

        self._minimum_market_cap = float(self.get_parameter("min_market_cap", "10000000000"))
        # Correction de données (#24228) : le 2014-02-18, LBTYB est rempli à
        # 51 329,82 au lieu d'environ 51, et ce seul prix porte 94 % de la valeur
        # finale de `strategy`. Le titre est retiré de l'univers éligible ;
        # `exclude=` (vide) rejoue la série d'origine.
        self._excluded = {s.strip().upper() for s in self.get_parameter("exclude", "LBTYB").split(",") if s.strip()}
        self._spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self._bnd = self.add_equity("BND", Resolution.DAILY).symbol if self._mode == "6040" else None

        self._invalid_orders = 0
        # Compteurs du nombre de lignes courtes par rééquilibrage (hors
        # préchauffage) : contrôle de propriété du découpage à la médiane.
        self._short_days = 0
        self._short_total = 0
        self._short_min = None
        self._short_max = 0
        self._short_empty_days = 0

        self._universe = None
        if self._mode in ("strategy", "all"):
            # Code de l'article : univers des constituants de SPY (enregistrés,
            # jamais abonnés) et univers fondamental filtré.
            self._etf_constituents = []
            self.add_universe(self.universe.etf(self._spy), self._record_etf_constituents)
            self.universe_settings.resolution = Resolution.DAILY
            self._universe = self.add_universe(self._select_assets)

        # Rééquilibrage à 8 h ET, avant l'ouverture : les ordres au marché
        # passés marché fermé sont remplis à l'ouverture. La stratégie et ses
        # deux diagnostics se rééquilibrent chaque jour, comme l'article ; les
        # deux références, le premier jour de bourse du mois.
        date_rule = (
            self.date_rules.month_start(self._spy)
            if self._mode in ("spy", "6040")
            else self.date_rules.every_day(self._spy)
        )
        self.schedule.on(date_rule, self.time_rules.at(8, 0), self._rebalance)
        self.set_warm_up(timedelta(90))

        # Trace journalière `shadow` (contrat #18923) : à la clôture de chaque
        # séance de SPY, hors préchauffage, la valeur du portefeuille (séries
        # e0..e4 à tour de rôle), les frais cumulés et la rotation cumulée.
        # Tous les modes la prennent au même instant.
        self._closes = 0

    def _record_etf_constituents(self, constituents):
        self._etf_constituents = [c.symbol for c in constituents]
        return []

    def _select_assets(self, fundamental):
        if not self._etf_constituents:
            return []
        stocks = [
            f for f in fundamental
            if f.market_cap > self._minimum_market_cap
            and f.symbol.value not in self._excluded
            and not np.isnan(self._return_on_equity(f))
        ]
        return_on_equity = pd.Series({f.symbol: self._return_on_equity(f) for f in stocks})
        non_us_stocks = [
            f.symbol for f in stocks
            if f.symbol not in self._etf_constituents and f.company_reference.country_id != "USA"
        ]
        if self._mode == "all":
            return non_us_stocks
        non_us_profitability = return_on_equity[non_us_stocks]
        return list(non_us_profitability[non_us_profitability < non_us_profitability.median()].index)

    def _return_on_equity(self, f):
        equity = f.financial_statements.balance_sheet.stockholders_equity.value
        return f.financial_statements.income_statement.net_income.twelve_months / equity if equity > 0 else np.nan

    def _rebalance(self):
        # Les ordres passés pendant le préchauffage sont refusés par Lean.
        if self.is_warming_up:
            return
        if self._mode == "spy":
            self.set_holdings([PortfolioTarget(self._spy, 1.0)], True)
            return
        if self._mode == "6040":
            self.set_holdings([PortfolioTarget(self._spy, 0.6), PortfolioTarget(self._bnd, 0.4)], True)
            return
        targets = [PortfolioTarget(self._spy, 0.5)]
        if self._mode in ("strategy", "all"):
            # Garde ajoutée : tant que l'univers n'a rien sélectionné, la
            # stratégie ne vend rien à découvert.
            selected = list(self._universe.selected or [])
            self._count_shorts(len(selected))
            targets += [PortfolioTarget(symbol, -0.5 / len(selected)) for symbol in selected]
        self.set_holdings(targets, True)

    def _count_shorts(self, n):
        self._short_days += 1
        self._short_total += n
        self._short_min = n if self._short_min is None else min(self._short_min, n)
        self._short_max = max(self._short_max, n)
        if n == 0:
            self._short_empty_days += 1

    def on_data(self, data):
        # Une clôture par séance, à sa date : la barre journalière de SPY.
        if self.is_warming_up or not data.bars.contains_key(self._spy):
            return
        self.plot("shadow", f"e{self._closes % 5}", self.portfolio.total_portfolio_value)
        self.plot("shadow", "fees", float(self.portfolio.total_fees) / self._start_value)
        self.plot("shadow", "turnover", self._traded)
        self._closes += 1

    def on_order_event(self, order_event):
        if order_event.status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            self._traded += (abs(float(order_event.fill_quantity) * float(order_event.fill_price))
                             / float(self.portfolio.total_portfolio_value))
        if order_event.status == OrderStatus.INVALID:
            self._invalid_orders += 1
            self.set_runtime_statistic("invalid_orders", str(self._invalid_orders))

    def on_end_of_algorithm(self):
        self.set_runtime_statistic("invalid_orders", str(self._invalid_orders))
        if self._short_days:
            self.set_runtime_statistic("shorts_mean", f"{self._short_total / self._short_days:.2f}")
            self.set_runtime_statistic("shorts_min", str(self._short_min))
            self.set_runtime_statistic("shorts_max", str(self._short_max))
            self.set_runtime_statistic("shorts_empty_days", str(self._short_empty_days))
