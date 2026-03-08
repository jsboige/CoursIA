# region imports
from AlgorithmImports import *
# endregion


class AllWeatherPortfolio(QCAlgorithm):
    """
    All-Weather Portfolio Strategy v4.0

    Key change from v3.0: Eliminate TLT entirely.
    Research (research.ipynb H5): TLT is monotonically negative for Sharpe on 2015-2026.
    Every +5pp TLT degrades Sharpe by ~0.005-0.010 due to the 2020-2023 Fed rate hike cycle
    (TLT lost ~40%). IEF (7-10yr duration) is far less sensitive to rate shocks.

    Allocation v4.0:
      SPY 30%  - Actions US (unchanged)
      TLT  0%  - Long bonds: eliminated (was 20%)
      IEF 40%  - Intermediate bonds (was 20%: +20pp absorbs TLT allocation)
      GLD 20%  - Or (unchanged, proven inflation hedge)
      XLP 10%  - Consumer Staples (defensive equity, dividends)

    Research findings (H5-H8, research.ipynb):
    - H5 CONFIRMED: TLT sweep 0-40% shows monotone Sharpe decline with TLT%
    - H6 PARTIAL: TIPS substitution marginal benefit (<0.03 Sharpe) vs complexity
    - H7 REJECTED: Vol targeting ineffective without leverage on low-vol AllWeather
    - H8 HONEST: MaxDD < SPY, Alpha > 0, Sharpe below SPY (pedagogically valid)

    Integrity check: improvement is NOT beta loading.
    - Beta stable ~0.30 (same as v3.0)
    - IEF has near-zero correlation with SPY (~0.0), unlike TLT (slightly negative)
    - Alpha > 0: diversification signal is real, persists in flat markets

    Backtest results:
    v1.0: Sharpe 0.250, CAGR 5.9%,  MaxDD 23.5% (Dalio static, DBC)
    v2.0: Sharpe 0.264, CAGR 5.8%,  MaxDD 17.6% (Gold Heavy + SMA50%)
    v2.1: Sharpe 0.365, CAGR 7.2%,  MaxDD 24.1% (Gold Heavy, no SMA)
    v2.2: Sharpe 0.325, CAGR 6.5%,  MaxDD 20.4% (SMA25%, worse)
    v3.0: Sharpe 0.482, CAGR 8.2%,  MaxDD 20.7%, Net +140.3%
    v4.0: TBD (research projects Sharpe ~0.51-0.54)

    Ref: Dalio (2017), research.ipynb (H5 sweep confirms TLT elimination)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)

        # v4.0: TLT eliminated, IEF raised to 40% (absorbs TLT duration risk)
        self.target_allocations = {
            "SPY": 0.30,   # 30% Actions US
            "IEF": 0.40,   # 40% Obligations intermediaires (was 20%: +20pp, replaces TLT)
            "GLD": 0.20,   # 20% Or (inchange)
            "XLP": 0.10,   # 10% Consumer Staples (defensif, dividendes, faible beta)
        }

        self.symbols = {}
        for ticker in self.target_allocations.keys():
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = equity.symbol

        # Tighter drift threshold: 3% (was 5%) for more responsive rebalancing
        self.rebalance_threshold = 0.03
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
        self.log(f"AW v4.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
