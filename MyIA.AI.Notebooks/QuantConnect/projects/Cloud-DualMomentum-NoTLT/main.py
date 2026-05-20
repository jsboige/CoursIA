# region imports
from AlgorithmImports import *
# endregion


class CloudDualMomentumNoTLT(QCAlgorithm):
    """
    Dual Momentum v1 — Original (with defensive bonds).

    Gary Antonacci's Dual Momentum approach.
    Universe: SPY, EFA (risky), BND (defensive).
    Monthly rebalance, 100% in best risky if absolute momentum > 0,
    else 100% BND.

    Parameter 'version' controls the variant:
    - v1: Original (SPY/EFA + BND defensive)
    - v2: NoTLT (SPY/QQQ/IEF/GLD/XLP, top 2)
    - v3: Enhanced (SPY/QQQ/EFA/GLD, top 3, momentum-weighted)
    """

    def initialize(self):
        self.set_start_date(2014, 1, 1)
        self.set_end_date(2025, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        version = self.get_parameter("version", "v1")

        if version == "v1":
            # Original: SPY vs EFA, BND defensive
            self.risky = ["SPY", "EFA"]
            self.defensive = "BND"
            self.num_holdings = 1
            self.lookback = 252
            self.mode = "single"
        elif version == "v2":
            # NoTLT: diversified, top 2 by 12m momentum
            self.risky = ["SPY", "QQQ", "IEF", "GLD", "XLP"]
            self.defensive = None
            self.num_holdings = 2
            self.lookback = 252
            self.mode = "multi"
        elif version == "v3":
            # Enhanced: 4 diversified, top 3, momentum-weighted
            self.risky = ["SPY", "QQQ", "EFA", "GLD"]
            self.defensive = "SHY"
            self.num_holdings = 3
            self.lookback = 252
            self.mode = "weighted"

        self.all_tickers = list(self.risky)
        if self.defensive:
            self.all_tickers.append(self.defensive)

        for ticker in self.all_tickers:
            self.add_equity(ticker, Resolution.DAILY)

        self.set_benchmark("SPY")
        self.rebalance_month = -1
        self.set_warm_up(self.lookback + 10, Resolution.DAILY)

    def on_data(self, data):
        if self.is_warming_up:
            return

        if self.time.month == self.rebalance_month:
            return
        self.rebalance_month = self.time.month

        scores = {}
        for ticker in self.risky:
            history = self.history(self.symbol(ticker), self.lookback + 5, Resolution.DAILY)
            if len(history) < self.lookback:
                continue
            closes = history['close']
            mom = (closes.iloc[-1] / closes.iloc[-self.lookback]) - 1
            scores[ticker] = mom

        if not scores:
            return

        # Absolute momentum filter
        passing = {t: s for t, s in scores.items() if s > 0}

        if not passing:
            if self.portfolio.invested:
                self.liquidate()
            if self.defensive:
                self.set_holdings(self.defensive, 1.0)
            self.log(f"ALL DEFENSIVE: No positive momentum, scores={scores}")
            return

        if self.mode == "single":
            # v1: 100% in best risky
            best = max(passing, key=passing.get)
            self.liquidate()
            self.set_holdings(best, 1.0)
            self.log(f"v1 REBAL: best={best}({passing[best]:.1%})")

        elif self.mode == "multi":
            # v2: Equal-weight top N
            sorted_assets = sorted(passing.items(), key=lambda x: x[1], reverse=True)
            selected = [t for t, s in sorted_assets[:self.num_holdings]]
            weight = 1.0 / len(selected)

            for ticker in self.all_tickers:
                if ticker not in selected and self.portfolio[self.symbol(ticker)].invested:
                    self.liquidate(self.symbol(ticker))

            for ticker in selected:
                self.set_holdings(self.symbol(ticker), weight)
            self.log(f"v2 REBAL: {selected} weight={weight:.1%}")

        elif self.mode == "weighted":
            # v3: Momentum-weighted top N
            sorted_assets = sorted(passing.items(), key=lambda x: x[1], reverse=True)
            selected_items = sorted_assets[:self.num_holdings]
            total_score = sum(s for _, s in selected_items)

            if total_score <= 0:
                self.liquidate()
                if self.defensive:
                    self.set_holdings(self.defensive, 1.0)
                return

            for ticker in self.all_tickers:
                if ticker not in [t for t, _ in selected_items]:
                    if self.portfolio[self.symbol(ticker)].invested:
                        self.liquidate(self.symbol(ticker))

            for ticker, score in selected_items:
                w = score / total_score
                self.set_holdings(self.symbol(ticker), w)
            self.log(f"v3 REBAL: {[(t, s/total_score) for t, s in selected_items]}")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"DUAL MOMENTUM: Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
