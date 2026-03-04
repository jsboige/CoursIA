# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class FactorETFRotation(QCAlgorithm):
    """
    Fama-French Factor ETF Rotation v2.0

    Research-driven improvements:
    - 12m simple lookback (not risk-adjusted composite)
    - USMV-only risk-off (no TLT - destroyed value in 2022)
    - Equal weight (simpler than risk parity, similar results)
    - Abs momentum filter (only positive-momentum factors)

    Backtest results:
    v1.0: Sharpe 0.365, CAGR 8.7%, MaxDD 31.1% (composite, TLT+USMV)
    v2.0: Sharpe 0.471, CAGR 11.7%, MaxDD 33.7%, Net +244.4% (BEST)

    Key insight: Removing TLT risk-off and simplifying momentum
    are the main drivers, same pattern as MomentumStrategy.

    Factor ETFs: VLUE, MTUM, SIZE, QUAL, USMV
    Ref: Fama & French (2015), Asness et al. (2013), research.ipynb
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)

        # Factor ETFs (iShares)
        self.factor_tickers = ["VLUE", "MTUM", "SIZE", "QUAL", "USMV"]

        self.symbols = {}
        for ticker in self.factor_tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = equity.symbol

        # Benchmark and regime filter
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.spy_sma = self.sma(self.spy, 200, Resolution.DAILY)

        # Parameters
        self.top_n = 3
        self.lookback = 252         # 12-month simple lookback
        self.rebalance_month = -1

        self.set_benchmark("SPY")
        self.set_warm_up(self.lookback + 30, Resolution.DAILY)

    def _momentum_score(self, symbol):
        """Calculate simple 12-month momentum."""
        history = self.history(symbol, self.lookback, Resolution.DAILY)
        if len(history) < self.lookback:
            return None

        current_price = history['close'].iloc[-1]
        past_price = history['close'].iloc[0]
        if past_price > 0:
            return (current_price / past_price) - 1
        return None

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not self.spy_sma.is_ready:
            return

        # Monthly rebalancing
        if self.time.month == self.rebalance_month:
            return
        self.rebalance_month = self.time.month

        # Calculate momentum for each factor
        scores = {}
        for ticker in self.factor_tickers:
            score = self._momentum_score(self.symbols[ticker])
            if score is not None:
                scores[ticker] = score

        if len(scores) < self.top_n:
            return

        # SMA200 regime filter
        spy_price = self.securities[self.spy].price
        risk_on = spy_price > self.spy_sma.current.value

        if risk_on:
            # Top N factors with positive momentum (equal weight)
            sorted_factors = sorted(scores.items(), key=lambda x: x[1], reverse=True)
            top_factors = [t for t, s in sorted_factors[:self.top_n] if s > 0]

            if len(top_factors) == 0:
                # All negative -> USMV only (defensive)
                self.liquidate()
                self.set_holdings(self.symbols["USMV"], 1.0)
                self.log(f"[RISK ON but all negative] -> USMV")
                return

            weight = 1.0 / len(top_factors)

            # Liquidate positions not in top
            for ticker in self.factor_tickers:
                if ticker not in top_factors and self.portfolio[self.symbols[ticker]].invested:
                    self.liquidate(self.symbols[ticker])

            for ticker in top_factors:
                self.set_holdings(self.symbols[ticker], weight)

            self.log(f"[RISK ON] Top {len(top_factors)}: {', '.join(top_factors)}")
        else:
            # Risk-off: 100% USMV (defensive, not TLT)
            for ticker in self.factor_tickers:
                if ticker != "USMV" and self.portfolio[self.symbols[ticker]].invested:
                    self.liquidate(self.symbols[ticker])
            self.set_holdings(self.symbols["USMV"], 1.0)
            self.log(f"[RISK OFF] SPY < SMA200 -> USMV")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FF v2.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
