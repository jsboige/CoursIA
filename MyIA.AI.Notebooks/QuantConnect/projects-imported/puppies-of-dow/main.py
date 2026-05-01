#region imports
from AlgorithmImports import *
#endregion
# Puppies of the Dow
# Source: QC Strategy Library
# Concept: Select top 5 lowest-priced stocks from the 10 highest-yielding Dow components.
# Uses ETF("DIA") universe for fundamental screening, annual rebalance at year start.
# Imported from QC Cloud Project ID: 29687759


class PuppiesOfTheDow(QCAlgorithm):

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100_000)

        self._portfolio_size = 5

        self.universe_settings.schedule.on(
            self.date_rules.year_start("SPY"),
        )
        self.settings.seed_initial_prices = True

        self._universe = self.add_universe(
            self.universe.etf("DIA"), self._select,
        )

        self.schedule.on(
            self.date_rules.year_start("SPY"),
            self.time_rules.at(8, 0),
            self._rebalance,
        )

        self.set_warm_up(timedelta(365))

    def _select(self, fundamentals: List[Fundamental]) -> List[Symbol]:
        dow_fundamentals = [
            f for f in fundamentals
            if f.price > 5 and f.valuation_ratios.total_yield > 0
        ]

        # Dogs of the Dow: top 10 by dividend yield
        dogs = sorted(
            dow_fundamentals,
            key=lambda x: x.valuation_ratios.total_yield,
        )[-10:]

        # Puppies: top 5 lowest-priced among the Dogs
        puppies = sorted(dogs, key=lambda x: x.price)[:self._portfolio_size]

        return [p.symbol for p in puppies]

    def _rebalance(self):
        if self.is_warming_up:
            return

        targets = [
            PortfolioTarget(s, 1 / self._portfolio_size)
            for s in self._universe.selected
            if self.securities.contains_key(s)
        ]
        if not targets:
            return
        self.set_holdings(targets, True)

    def on_warmup_finished(self):
        self._rebalance()
