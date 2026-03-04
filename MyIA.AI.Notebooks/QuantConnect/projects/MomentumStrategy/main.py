# region imports
from AlgorithmImports import *
# endregion


class SectorMomentumETFRotation(QCAlgorithm):
    """
    Sector ETF Momentum Rotation Strategy v2.1

    Research-driven improvements:
    - 12m simple lookback (research Sharpe 0.612) vs composite (0.490)
    - XLP+XLU defensive risk-off >> TLT (TLT lost in 2022 rate hikes)
    - Abs momentum filter (only sectors with positive 12m return)
    - Top 3 sectors, monthly rebalance, equal-weight

    Backtest results:
    v1.0: Sharpe 0.216, CAGR 6.5%, MaxDD 29.9% (composite, TLT risk-off)
    v2.0: Sharpe 0.149, CAGR 5.3%, MaxDD 33.7% (12m, cash risk-off)
    v2.1: Sharpe 0.411, CAGR 10.8%, MaxDD 30.1%, Net +214.7% (BEST)
    v2.2: Sharpe 0.414, CAGR 10.9%, MaxDD 31.9% (composite, similar)

    Key insight: XLP+XLU risk-off was the main driver (0.216 -> 0.411),
    not the lookback change. TLT was destroying value in rate-hike periods.

    ETFs sectoriels: XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC
    Ref: Jegadeesh & Titman (1993), Faber (2007), research.ipynb
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)

        # 11 sector ETFs (S&P 500 GICS sectors)
        self.sector_tickers = [
            "XLK",   # Technology
            "XLF",   # Financials
            "XLE",   # Energy
            "XLV",   # Healthcare
            "XLI",   # Industrials
            "XLY",   # Consumer Discretionary
            "XLP",   # Consumer Staples
            "XLU",   # Utilities
            "XLB",   # Materials
            "XLRE",  # Real Estate
            "XLC",   # Communication Services
        ]

        self.symbols = {}
        for ticker in self.sector_tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = equity.symbol

        # SPY for regime filter
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.spy_sma = self.sma(self.spy, 200, Resolution.DAILY)

        # Parameters
        self.top_n = 3              # Number of sectors to hold
        self.lookback = 252         # 12-month simple lookback
        self.rebalance_month = -1

        self.set_benchmark("SPY")
        self.set_warm_up(self.lookback + 30, Resolution.DAILY)

    def _momentum_score(self, symbol):
        """Calculate simple 12-month momentum (total return)."""
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

        # Calculate momentum for all sectors
        scores = {}
        for ticker, symbol in self.symbols.items():
            score = self._momentum_score(symbol)
            if score is not None:
                scores[ticker] = score

        if len(scores) < self.top_n:
            return

        # SMA200 regime filter
        spy_price = self.securities[self.spy].price
        risk_on = spy_price > self.spy_sma.current.value

        if risk_on:
            # Select top N sectors with positive momentum (abs momentum filter)
            sorted_sectors = sorted(scores.items(), key=lambda x: x[1], reverse=True)
            top_sectors = [t for t, s in sorted_sectors[:self.top_n] if s > 0]

            if len(top_sectors) == 0:
                # All sectors negative momentum -> defensive (XLP + XLU)
                self.liquidate()
                self.set_holdings(self.symbols["XLP"], 0.5)
                self.set_holdings(self.symbols["XLU"], 0.5)
                self.log(f"[RISK ON but all negative] -> XLP+XLU defensive")
                return

            weight = 1.0 / len(top_sectors)

            # Liquidate positions not in top
            for ticker, symbol in self.symbols.items():
                if ticker not in top_sectors and self.portfolio[symbol].invested:
                    self.liquidate(symbol)

            for ticker in top_sectors:
                self.set_holdings(self.symbols[ticker], weight)

            top_str = ", ".join([f"{t}={scores[t]:.3f}" for t in top_sectors])
            self.log(f"[RISK ON] Top {len(top_sectors)}: {top_str}")
        else:
            # Risk-off: rotate to defensive sectors (XLP + XLU)
            for ticker, symbol in self.symbols.items():
                if ticker not in ["XLP", "XLU"] and self.portfolio[symbol].invested:
                    self.liquidate(symbol)
            self.set_holdings(self.symbols["XLP"], 0.5)
            self.set_holdings(self.symbols["XLU"], 0.5)
            self.log(f"[RISK OFF] SPY={spy_price:.2f} < SMA200 -> XLP+XLU")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"MOMENTUM v2.1: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
