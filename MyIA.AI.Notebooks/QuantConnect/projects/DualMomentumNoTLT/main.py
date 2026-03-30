from AlgorithmImports import *
import numpy as np

class DualMomentumNoTLT(QCAlgorithm):
    """
    Dual Momentum No TLT v1.0

    Multi-asset momentum rotation without long-duration bonds.

    Rules:
    - Universe: SPY, QQQ, IEF, GLD, XLP
    - Monthly rebalance
    - Absolute momentum: 12M return > 0
    - Relative momentum: top 2 by 12M return
    - Cash if nothing passes absolute filter

    Key insight: TLT lost ~40% during 2020-2023 rate hikes.
    Using IEF (intermediate bonds), GLD, XLP as alternatives.

    Reference: Antonacci (2012), lessons from AllWeather optimization
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)

        self.tickers = ["SPY", "QQQ", "IEF", "GLD", "XLP"]
        self.symbols = {}
        for ticker in self.tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = equity.symbol

        self.set_benchmark("SPY")
        self.lookback = 252  # 12 months
        self.num_holdings = 2
        self.rebalance_month = -1

        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        self.set_warm_up(self.lookback + 10, Resolution.DAILY)

    def on_data(self, data):
        if self.is_warming_up:
            return

        # Monthly rebalance
        if self.time.month == self.rebalance_month:
            return
        self.rebalance_month = self.time.month

        # Compute 12M momentum for each asset
        scores = {}
        for ticker in self.tickers:
            symbol = self.symbols[ticker]
            history = self.history(symbol, self.lookback + 5, Resolution.DAILY)
            if len(history) < self.lookback:
                continue

            closes = history['close']
            mom_12m = (closes.iloc[-1] / closes.iloc[-self.lookback]) - 1
            scores[ticker] = mom_12m

        if not scores:
            return

        # Absolute momentum filter: only positive
        passing = {t: s for t, s in scores.items() if s > 0}

        if not passing:
            # All negative: go to cash
            if self.portfolio.invested:
                self.liquidate()
                self.log("ALL CASH: No positive 12M momentum")
            return

        # Relative momentum: top N
        sorted_assets = sorted(passing.items(), key=lambda x: x[1], reverse=True)
        selected = [t for t, s in sorted_assets[:self.num_holdings]]
        weight = 1.0 / len(selected)

        # Liquidate non-selected
        for ticker, symbol in self.symbols.items():
            if ticker not in selected and self.portfolio[symbol].invested:
                self.liquidate(symbol)

        # Set positions
        for ticker in selected:
            self.set_holdings(self.symbols[ticker], weight)

        scores_str = ", ".join(f"{t}:{s:.1%}" for t, s in sorted_assets)
        self.log(f"REBAL: Selected={selected}, [{scores_str}]")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"DUAL MOM NoTLT: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
