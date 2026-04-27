from AlgorithmImports import *
# https://www.quantconnect.com/strategies/211
# Puppies of the Dow Value-Income Tilt
# OOS 1Y Sharpe 1.99, 5Y CAGR 10.16%, 5Y Drawdown 22.90%, 65% Win Rate
# Systematic value/income tilt using Dow 30: rank by dividend yield,
# select 10 highest yielding (Dogs of the Dow), then 5 lowest priced (Puppies)
# Equal weighted, annual rebalance
# Source: QC Strategy Library #211, cloned 2026-04-05, QC Project ID: 29687759


class PuppiesOfTheDow(QCAlgorithm):

    def initialize(self):
        self.set_start_date(self.end_date - timedelta(12*365))
        self.set_cash(100_000)
        self._portfolio_size = 5
        self.universe_settings.schedule.on(self.date_rules.year_start("SPY"))
        self.settings.seed_initial_prices = True
        # Add universe using DIA ETF constituents (Dow 30)
        self._universe = self.add_universe(self.universe.etf("DIA"), self._select)
        self.schedule.on(
            self.date_rules.year_start("SPY"),
            self.time_rules.at(8,0),
            self._rebalance
        )
        self.set_warm_up(timedelta(365))

    def _select(self, fundamentals: List[Fundamental]) -> List[Symbol]:
        # Filter for valid price and dividend yield
        dow_fundamentals = [f for f in fundamentals if f.price > 5 and f.valuation_ratios.total_yield > 0]
        # Dogs of the Dow: top 10 highest dividend yielders from the Dow 30
        dogs = sorted(dow_fundamentals, key=lambda x: x.valuation_ratios.total_yield)[-10:]
        # Puppies: the 5 lowest-priced stocks from the Dogs
        puppies = sorted(dogs, key=lambda x: x.price)[:self._portfolio_size]
        return [p.symbol for p in puppies]

    def _rebalance(self):
        if self.is_warming_up:
            return
        # Create equal-weight portfolio targets from selected universe symbols
        targets = [PortfolioTarget(s, 1 / self._portfolio_size) for s in self._universe.selected]
        self.set_holdings(targets, True)

    def on_warmup_finished(self):
        self._rebalance()
