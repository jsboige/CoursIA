# region imports
from AlgorithmImports import *
# endregion


class AllWeatherPortfolio(QCAlgorithm):
    """
    All-Weather Portfolio Strategy v2.1

    Research-driven Gold Heavy allocation (no DBC).
    GLD 20% replaces DBC 7.5% + extra GLD. No SMA overlay
    (tested: SMA reduces vol too much, killing excess return).

    Backtest results:
    v1.0: Sharpe 0.25, CAGR 5.9%, MaxDD 23.5% (Dalio static, DBC)
    v2.0: Sharpe 0.264, CAGR 5.8%, MaxDD 17.6% (Gold Heavy + SMA50%)
    v2.1: Sharpe 0.365, CAGR 7.2%, MaxDD 24.1%, Net +116.6% (BEST)
    v2.2: Sharpe 0.325, CAGR 6.5%, MaxDD 20.4% (SMA25%, worse)

    Key insight: DBC was a performance drag, GLD provides better
    inflation hedge with less contango decay.

    Ref: Dalio (2017), research.ipynb
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)

        # Gold Heavy allocation (no DBC, more GLD)
        self.target_allocations = {
            "SPY": 0.30,   # 30% Actions US
            "TLT": 0.35,   # 35% Obligations long-terme
            "IEF": 0.15,   # 15% Obligations intermediaires
            "GLD": 0.20,   # 20% Or
        }

        self.symbols = {}
        for ticker in self.target_allocations.keys():
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = equity.symbol

        # Parameters
        self.rebalance_threshold = 0.05
        self.last_rebalance_month = -1

        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self._check_rebalance
        )

        self.set_benchmark("SPY")

    def _check_rebalance(self):
        current_month = self.time.month
        # Quarterly rebalancing (Jan, Apr, Jul, Oct)
        if current_month in [1, 4, 7, 10]:
            if self.last_rebalance_month != current_month:
                self._rebalance()
                return
        # Drift-based rebalancing
        if self._check_drift():
            self._rebalance()

    def _check_drift(self):
        total_value = self.portfolio.total_portfolio_value
        if total_value == 0:
            return False
        for ticker, target in self.target_allocations.items():
            symbol = self.symbols[ticker]
            current = self.portfolio[symbol].holdings_value / total_value
            if abs(current - target) > self.rebalance_threshold:
                return True
        return False

    def _rebalance(self):
        self.last_rebalance_month = self.time.month
        for ticker, weight in self.target_allocations.items():
            self.set_holdings(self.symbols[ticker], weight)

    def on_data(self, data):
        if not self.portfolio.invested:
            self._rebalance()

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"AW v2.1: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
