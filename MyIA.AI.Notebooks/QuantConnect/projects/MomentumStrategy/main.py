# region imports
from AlgorithmImports import *
# endregion


class SectorMomentumETFRotation(QCAlgorithm):
    """
    Sector ETF Momentum Rotation Strategy

    Selectionne les top 3 secteurs par momentum composite (1, 3, 6, 12 mois).
    Rebalance mensuellement avec equal-weight.
    Filtre SMA200 sur SPY pour regime risk-on/risk-off.

    ETFs sectoriels: XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC
    Ref: Mebane Faber (2007), "A Quantitative Approach to Tactical Asset Allocation"
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

        # Safe haven for risk-off
        self.tlt = self.add_equity("TLT", Resolution.DAILY).symbol

        # Parameters
        self.top_n = 3  # Number of sectors to hold
        self.lookback_windows = [21, 63, 126, 252]  # 1, 3, 6, 12 months
        self.lookback_weights = [0.4, 0.2, 0.2, 0.2]  # Weight recent more
        self.max_lookback = max(self.lookback_windows)
        self.rebalance_month = -1

        self.set_benchmark("SPY")
        self.set_warm_up(timedelta(self.max_lookback + 30))

    def _composite_momentum(self, symbol):
        """Calculate weighted composite momentum across multiple lookbacks."""
        history = self.history(symbol, self.max_lookback, Resolution.DAILY)
        if len(history) < self.max_lookback:
            return None

        current_price = history['close'].iloc[-1]
        score = 0.0
        for window, weight in zip(self.lookback_windows, self.lookback_weights):
            past_price = history['close'].iloc[-window]
            if past_price > 0:
                momentum = (current_price / past_price) - 1
                score += weight * momentum
        return score

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
            score = self._composite_momentum(symbol)
            if score is not None:
                scores[ticker] = score

        if len(scores) < self.top_n:
            return

        # SMA200 regime filter
        spy_price = self.securities[self.spy].price
        risk_on = spy_price > self.spy_sma.current.value

        if risk_on:
            # Select top N sectors by momentum
            sorted_sectors = sorted(scores.items(), key=lambda x: x[1], reverse=True)
            top_sectors = [t for t, s in sorted_sectors[:self.top_n] if s > 0]

            if len(top_sectors) == 0:
                # All sectors negative, go defensive
                self.liquidate()
                self.set_holdings(self.tlt, 1.0)
                self.log(f"[RISK ON but all negative] -> TLT")
                return

            weight = 1.0 / len(top_sectors)

            # Liquidate positions not in top
            for ticker, symbol in self.symbols.items():
                if ticker not in top_sectors and self.portfolio[symbol].invested:
                    self.liquidate(symbol)
            if self.portfolio[self.tlt].invested:
                self.liquidate(self.tlt)

            for ticker in top_sectors:
                self.set_holdings(self.symbols[ticker], weight)

            top_str = ", ".join([f"{t}={scores[t]:.3f}" for t in top_sectors])
            self.log(f"[RISK ON] Top {len(top_sectors)}: {top_str}")
        else:
            # Risk-off: rotate to TLT
            for symbol in self.symbols.values():
                if self.portfolio[symbol].invested:
                    self.liquidate(symbol)
            self.set_holdings(self.tlt, 1.0)
            self.log(f"[RISK OFF] SPY={spy_price:.2f} < SMA200={self.spy_sma.current.value:.2f} -> TLT")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"SECTOR MOMENTUM ETF: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
