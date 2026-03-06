# region imports
from AlgorithmImports import *
# endregion


class AllWeatherPortfolio(QCAlgorithm):
    """
    All-Weather Portfolio Strategy v3.0

    Key change from v2.1: Reduce long-bond (TLT) exposure.
    TLT lost ~40% in 2020-2023 (Fed rate hike cycle), dragging the portfolio.
    Redistribute toward IEF (shorter duration, less rate-sensitive) and XLP
    (Consumer Staples: defensive equity, dividend yield, low bond correlation).

    Allocation v3.0:
      SPY 30%  - Actions US (unchanged)
      TLT 20%  - Long bonds (was 35%: -15pp to reduce rate risk)
      IEF 20%  - Intermediate bonds (was 15%: +5pp, more stable)
      GLD 20%  - Or (unchanged, proven inflation hedge)
      XLP 10%  - Consumer Staples (defensive equity, dividends)

    Rationale:
    - Total bond exposure: 40% (was 50%). Reduces duration risk.
    - XLP: Sharpe > SPY in bear markets, dividend yield ~3%, low beta.
    - Drift-based rebalancing at 3% threshold (was 5%): more responsive.
    - No SMA overlay (v2.1 proof: SMA adds friction without Sharpe gain in QC).

    Backtest results:
    v1.0: Sharpe 0.250, CAGR 5.9%,  MaxDD 23.5% (Dalio static, DBC)
    v2.0: Sharpe 0.264, CAGR 5.8%,  MaxDD 17.6% (Gold Heavy + SMA50%)
    v2.1: Sharpe 0.365, CAGR 7.2%,  MaxDD 24.1% (Gold Heavy, no SMA)
    v2.2: Sharpe 0.325, CAGR 6.5%,  MaxDD 20.4% (SMA25%, worse)
    v3.0: Sharpe 0.482, CAGR 8.2%,  MaxDD 20.7%, Net +140.3% (BEST)

    Ref: Dalio (2017), research.ipynb
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)

        # Reduced-duration bond allocation with defensive equity (XLP)
        self.target_allocations = {
            "SPY": 0.30,   # 30% Actions US
            "TLT": 0.20,   # 20% Obligations long-terme (reduit de 35% pour limiter le risque de duration)
            "IEF": 0.20,   # 20% Obligations intermediaires (renforce de 15%)
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
        self.log(f"AW v3.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
