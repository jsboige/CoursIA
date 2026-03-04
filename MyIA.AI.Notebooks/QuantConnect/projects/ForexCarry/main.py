# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class ForexCarryTradeStrategy(QCAlgorithm):
    """
    Forex Momentum Strategy v4.0 - SPY Parking + Core-Satellite

    Key innovation: SPY core (40%) with FX momentum satellites (30% each).
    When no positive FX momentum, full SPY parking (95%).
    This eliminates cash drag and captures equity returns during flat FX.

    History:
    v3.0: Sharpe -1.80 (7 pairs, long/short)
    v3.1: Sharpe +0.01 (4 pairs, long-only, 20% size)
    v3.2: Sharpe -0.654 (4 pairs, long-only, 50% size)
    v4.0: Sharpe +0.476, Net +133.6%, MaxDD 17.7% (SPY parking)
         Alpha +0.004, Beta 0.584, Win Rate 68%

    Ref: Menkhoff et al. (2012), Asness et al. (2013)
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_cash(100000)

        # SPY as core holding
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol

        # 4 diversified FX pairs (Europe, Commodity, Asia, Americas)
        self.pair_names = ["EURUSD", "AUDUSD", "USDJPY", "USDCAD"]
        self.forex_symbols = {}
        for pair in self.pair_names:
            forex = self.add_forex(pair, Resolution.DAILY)
            self.forex_symbols[pair] = forex.symbol

        # Momentum parameters
        self.lookback_short = 21    # 1 month (weight 70%)
        self.lookback_long = 126    # 6 months (weight 30%)
        self.weight_short = 0.7
        self.weight_long = 0.3
        self.num_long = 2           # Top 2 pairs
        self.fx_size = 0.30         # 30% per FX pair (satellite)
        self.spy_core = 0.40        # 40% SPY always (core)
        self.spy_full = 0.95        # 95% SPY when no FX opportunity
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

                mom_short = (current / closes.iloc[-self.lookback_short]) - 1
                mom_long = (current / closes.iloc[0]) - 1

                # Invert for USD/XXX pairs
                if pair.startswith("USD"):
                    mom_short = -mom_short
                    mom_long = -mom_long

                score = mom_short * self.weight_short + mom_long * self.weight_long
                scores[pair] = score
            except:
                continue

        if len(scores) < 2:
            return

        sorted_pairs = sorted(scores.items(), key=lambda x: x[1], reverse=True)
        top_score = sorted_pairs[0][1]

        # No positive momentum: full SPY parking
        if top_score < 0:
            for pair, symbol in self.forex_symbols.items():
                if self.portfolio[symbol].invested:
                    self.liquidate(symbol)
            self.set_holdings(self.spy, self.spy_full)
            self.log(f"ALL SPY: No positive FX momentum (best={top_score:.4f})")
            return

        # Positive momentum: core-satellite
        long_pairs = [p for p, s in sorted_pairs[:self.num_long] if s > 0]

        # Liquidate non-selected FX
        for pair, symbol in self.forex_symbols.items():
            if pair not in long_pairs and self.portfolio[symbol].invested:
                self.liquidate(symbol)

        # Set SPY core
        self.set_holdings(self.spy, self.spy_core)

        # Set FX satellites
        for pair in long_pairs:
            symbol = self.forex_symbols[pair]
            self.set_holdings(symbol, self.fx_size)

        scores_str = ", ".join(f"{p}:{s:.4f}" for p, s in sorted_pairs)
        self.log(f"FX v4.0: SPY={self.spy_core:.0%} + FX={long_pairs}, [{scores_str}]")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FOREX v4.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
