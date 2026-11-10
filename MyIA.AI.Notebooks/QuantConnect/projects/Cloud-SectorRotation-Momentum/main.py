# region imports
from AlgorithmImports import *
# endregion


class SectorRotationMomentum(QCAlgorithm):
    """
    v4 — Momentum-Weighted Multi-Asset Trend Following.

    Universe: 5 diversified ETFs (QQQ, SPY, EFA, GLD, IWM).
    Signal: Price > SMA200 AND 6-month momentum > 0 (dual filter).
    Allocation: Momentum-weighted (proportional to ROC score).
    Defensive: If no asset qualifies, hold SHY.
    Rebalance: Monthly (21 trading days).
    """

    def initialize(self):
        # Mesure contre references detenues (#21371, protocole de #21329) :
        # `strategy` (defaut) garde la decision du code ; `spy` (SPY detenu) et
        # `6040` (SPY 60 %, BND 40 %) sont les deux references.
        self._mode = self.get_parameter("mode", "strategy").lower()
        if self._mode not in ("strategy", "spy", "6040"):
            raise ValueError(
                f"parametre mode inconnu : {self._mode} (strategy | spy | 6040)"
            )

        # Aligned baseline period 2018-2025 (#1630). Original start was 2014;
        # standardized to 2018-01-01 for cross-strategy comparison.
        # Les parametres start_date et end_date (%Y%m%d) ouvrent la mesure hors
        # echantillon ; sans eux, la fenetre reste celle-ci.
        start_date_param = self._parse_date_param("start_date")
        end_date_param = self._parse_date_param("end_date")
        if start_date_param is not None:
            self.set_start_date(start_date_param)
        else:
            self.set_start_date(2018, 1, 1)
        if end_date_param is not None:
            self.set_end_date(end_date_param)
        else:
            self.set_end_date(2025, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(
            BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN
        )

        if self._mode == "strategy":
            self._initialize_strategy()
        else:
            self._initialize_reference()

        self.set_benchmark("SPY")
        self.set_warm_up(200, Resolution.DAILY)

        # Trace journaliere `shadow` (contrat #18923) : valeur du portefeuille a
        # l'ouverture de chaque seance de SPY, repartie sur e0..e4. Les trois
        # modes la prennent au meme instant, sur la cloture de la veille.
        self._closes = 0
        self._trace_symbol = Symbol.create("SPY", SecurityType.EQUITY, Market.USA)
        self.schedule.on(
            self.date_rules.every_day(self._trace_symbol),
            self.time_rules.after_market_open(self._trace_symbol, 0),
            self._trace,
        )

    def _initialize_strategy(self):
        # Universe: equity growth, broad, intl, gold, small cap
        self.tickers = ["QQQ", "SPY", "EFA", "GLD", "IWM"]
        self.sma_dict = {}
        self.symbols = {}

        for ticker in self.tickers:
            symbol = self.add_equity(ticker, Resolution.DAILY).symbol
            self.symbols[ticker] = symbol
            self.sma_dict[ticker] = self.sma(symbol, 200, Resolution.DAILY)

        self.shy = self.add_equity("SHY", Resolution.DAILY).symbol

        self.momentum_lookback = 126
        self.rebalance_days = 21
        self.days_since_rebalance = 0

    def _initialize_reference(self):
        self.settings.seed_initial_prices = True
        self._ref_spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self._ref_bnd = (
            self.add_equity("BND", Resolution.DAILY).symbol
            if self._mode == "6040"
            else None
        )
        self.schedule.on(
            self.date_rules.month_start(self._ref_spy),
            self.time_rules.after_market_open(self._ref_spy, 1),
            self._rebalance_reference,
        )

    def _rebalance_reference(self):
        if self.is_warming_up:
            return
        if self._ref_bnd is None:
            self.set_holdings([PortfolioTarget(self._ref_spy, 1.0)])
        else:
            self.set_holdings([
                PortfolioTarget(self._ref_spy, 0.6),
                PortfolioTarget(self._ref_bnd, 0.4),
            ])

    def _parse_date_param(self, name):
        raw = self.get_parameter(name)
        if raw is None or str(raw).strip() == "":
            return None
        return datetime.strptime(str(raw).strip(), "%Y%m%d")

    def _trace(self):
        if self.is_warming_up:
            return
        self.plot("shadow", f"e{self._closes % 5}", self.portfolio.total_portfolio_value)
        self._closes += 1

    def on_data(self, data):
        if self.is_warming_up or self._mode != "strategy":
            return

        # En journalier, Lean livre les avis de dividende et de division dans une
        # tranche datee de minuit, sans barre de cotation (#20264). Sans ce garde,
        # elle avancait le compteur et pouvait porter le reequilibrage : aucun titre
        # n'y a de donnee, la liste qualifiee est vide et _go_defensive() liquidait.
        if not any(data.bars.contains_key(sym) for sym in self.symbols.values()):
            return

        self.days_since_rebalance += 1
        if self.days_since_rebalance < self.rebalance_days:
            return
        self.days_since_rebalance = 0

        qualified = {}
        for ticker in self.tickers:
            symbol = Symbol.create(ticker, SecurityType.EQUITY, Market.USA)
            if symbol not in data or data[symbol] is None:
                continue

            price = self.securities[symbol].price
            sma_val = self.sma_dict[ticker].current.value

            if price <= sma_val:
                continue

            # Sur une demi-seance (cloture a 13:00, New York), history() rend environ
            # 105 barres pour 126 demandees (mesure #20286) : la garde de longueur
            # ecartait alors les cinq titres et _go_defensive() passait tout en SHY.
            # Demander le double et garder les 126 dernieres ; une seance pleine
            # rend les memes 126 barres qu'avant.
            history = self.history([symbol], 2 * self.momentum_lookback, Resolution.DAILY)
            if history is None or history.empty:
                continue
            try:
                closes = history.loc[symbol, "close"].iloc[-self.momentum_lookback:]
            except KeyError:
                continue
            if len(closes) < self.momentum_lookback:
                continue
            momentum = (closes.iloc[-1] / closes.iloc[0]) - 1.0
            if momentum > 0:
                qualified[ticker] = momentum

        if not qualified:
            self._go_defensive()
            return

        # Momentum-weighted allocation
        total_momentum = sum(qualified.values())
        weights = {t: m / total_momentum for t, m in qualified.items()}

        for ticker in self.tickers:
            symbol = Symbol.create(ticker, SecurityType.EQUITY, Market.USA)
            if symbol in self.portfolio and self.portfolio[symbol].invested:
                if ticker not in weights:
                    self.liquidate(symbol)

        if self.shy in self.portfolio and self.portfolio[self.shy].invested:
            self.liquidate(self.shy)

        for ticker, weight in weights.items():
            symbol = Symbol.create(ticker, SecurityType.EQUITY, Market.USA)
            self.set_holdings(symbol, weight)

        top = max(weights, key=weights.get)
        self.log(
            f"REBALANCE: {len(qualified)} assets | "
            f"Top: {top} ({weights[top]:.1%}) | "
            f"Total mom: {total_momentum:.2%}"
        )

    def _go_defensive(self):
        for ticker in self.tickers:
            symbol = Symbol.create(ticker, SecurityType.EQUITY, Market.USA)
            if symbol in self.portfolio and self.portfolio[symbol].invested:
                self.liquidate(symbol)
        if self.shy in self.portfolio and not self.portfolio[self.shy].invested:
            self.set_holdings(self.shy, 1.0)
        self.log("REBALANCE: No trend -> SHY")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(
            f"MOM-WEIGHTED TREND v4: Final=${final:,.2f}, "
            f"Return={(final - 100000) / 100000:.2%}"
        )
