# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class ForexCarryTradeStrategy(QCAlgorithm):
    """
    Forex Momentum Strategy v3.2

    Research-driven FX momentum on 4 diversified pairs.
    Long-only top-2 momentum pairs. Leveraged positions for FX scale.
    Short-term momentum (21j) weighted 70%, medium-term (126j) weighted 30%.
    Positive momentum filter: only trade when best pair has positive momentum.

    v3.1 was profitable (+1.41%) but low vol (0.8%). Scaling positions
    to capture the positive edge with appropriate FX leverage.

    Ref: Menkhoff et al. (2012), Asness et al. (2013)
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_cash(100000)

        # 4 diversified FX pairs (Europe, Commodity, Asia, Americas)
        self.pair_names = ["EURUSD", "AUDUSD", "USDJPY", "USDCAD"]
        self.forex_symbols = {}
        for pair in self.pair_names:
            forex = self.add_forex(pair, Resolution.DAILY)
            self.forex_symbols[pair] = forex.symbol

        # Momentum parameters (from research notebook)
        self.lookback_short = 21    # 1 month (weight 70%)
        self.lookback_long = 126    # 6 months (weight 30%)
        self.weight_short = 0.7
        self.weight_long = 0.3
        self.num_long = 2           # Long-only, top 2 pairs
        self.position_size = 0.50   # 50% per pair = 100% total (standard FX leverage)
        self.rebalance_month = -1

        self.set_benchmark("SPY")
        self.set_warm_up(self.lookback_long + 10, Resolution.DAILY)

    def on_data(self, data):
        if self.is_warming_up:
            return

        # Monthly rebalance
        if self.time.month == self.rebalance_month:
            return
        self.rebalance_month = self.time.month

        # Compute composite momentum scores
        scores = {}
        for pair in self.pair_names:
            symbol = self.forex_symbols[pair]
            history = self.history(symbol, self.lookback_long, Resolution.DAILY)
            if len(history) < self.lookback_long:
                continue

            try:
                closes = history['close']
                current = closes.iloc[-1]

                # Short-term momentum (21 days)
                mom_short = (current / closes.iloc[-self.lookback_short]) - 1
                # Medium-term momentum (126 days)
                mom_long = (current / closes.iloc[0]) - 1

                # Invert for USD/XXX pairs (up = USD strong = currency weak)
                if pair.startswith("USD"):
                    mom_short = -mom_short
                    mom_long = -mom_long

                score = mom_short * self.weight_short + mom_long * self.weight_long
                scores[pair] = score
            except:
                continue

        if len(scores) < self.num_long:
            return

        # Sort by score, take top N
        sorted_pairs = sorted(scores.items(), key=lambda x: x[1], reverse=True)
        long_pairs = [p for p, s in sorted_pairs[:self.num_long]]

        # Only go long if top momentum is positive
        top_score = sorted_pairs[0][1]
        if top_score < 0:
            if self.portfolio.invested:
                self.liquidate()
                self.log(f"ALL CASH: No positive momentum (best={top_score:.4f})")
            return

        # Liquidate non-selected positions
        for pair, symbol in self.forex_symbols.items():
            if pair not in long_pairs:
                if self.portfolio[symbol].invested:
                    self.liquidate(symbol)

        # Go long the best momentum pairs
        for pair in long_pairs:
            symbol = self.forex_symbols[pair]
            self.set_holdings(symbol, self.position_size)

        scores_str = ", ".join(f"{p}:{s:.4f}" for p, s in sorted_pairs)
        self.log(f"FX MOM v3.2: Long={long_pairs}, Scores=[{scores_str}]")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FOREX MOM v3.2: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
