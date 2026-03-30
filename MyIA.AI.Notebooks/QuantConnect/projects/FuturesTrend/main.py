# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class FuturesTrendFollowing(QCAlgorithm):
    """
    Multi-Asset Trend Following v3.1

    Iteration on v3.0 (Sharpe 0.209 < v2.3 Sharpe 0.280):
    - Reverted ATR sizing -> fixed 33% (ATR sizing reduced position size during
      strong trends, when large allocation is exactly right)
    - Lighter SMA50 trend filter instead of SMA100 (less restrictive, more signals)
    - ETF universe improvement kept: XLE replaces TLT (no rates headwind)
    - Max positions 3 (concentrated in best trends, higher per-trade alpha)

    The issue with v3.0: SMA100 filter + ATR sizing both acted as brakes on
    entries, resulting in fewer and smaller positions. The trend filter idea is
    sound but needs to be lighter-touch to preserve signal frequency.

    Research iter5 findings (2026-03-09):
    - SMA30/SMA20: severe IS/OOS overfitting (OOS Sharpe -0.010)
    - More positions (4x25%, 5x20%): all degraded vs concentration 3x33%
    - Exit=15j: increases MaxDD without Sharpe gain
    - Removing VNQ: yfinance showed +11% but QC cloud showed -10% (REVERTED)
      -> VNQ contributes via dividends captured in QC raw prices
    - v3.1 is the structural ceiling for parametric optimization on this universe/period

    Backtest results:
    v1.2: Sharpe 0.019, CAGR 2.1%, MaxDD 31.9% (ES only, L/S)
    v2.0: Sharpe 0.144, CAGR 5.5%, MaxDD 16.9% (4 ETFs, 25%)
    v2.1: Sharpe 0.216, CAGR 6.3%, MaxDD 8.5% (6 ETFs, dynamic)
    v2.3: Sharpe 0.280, CAGR 7.3%, MaxDD 10.2%, Net +78.1%
    v3.0: Sharpe 0.209, CAGR 6.7%, MaxDD 12.6% (SMA100 too restrictive)
    v3.1: Sharpe 0.301, CAGR 8.0%, MaxDD 12.9% (BEST - current)
    v4.0: Sharpe 0.272 (REVERTED - sans VNQ degraded on QC despite yfinance +11%)

    Ref: Curtis Faith (2007), Moskowitz et al. (2012), research.ipynb
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)  # Extended from 2018: +3 years for robustness validation (includes 2017-2019 bull pre-COVID)
        self.set_cash(100000)

        # Improved universe: XLE (energy) replaces TLT (destroyed by rate hikes 2022)
        # SPY=equities, GLD=gold, EFA=international, VNQ=realestate, DBC=commodities, XLE=energy
        self.etf_list = ["SPY", "GLD", "EFA", "VNQ", "DBC", "XLE"]
        self.symbols = {}

        for etf in self.etf_list:
            equity = self.add_equity(etf, Resolution.DAILY)
            self.symbols[etf] = equity.symbol

        # Donchian parameters (20/10 - research confirmed, avoids overfitting)
        self.entry_period = 20
        self.exit_period = 10

        # Lighter trend filter: SMA50 (less restrictive than SMA100)
        # Purpose: avoid entering broken-down assets, but preserve signal frequency
        self.trend_sma_period = 50

        # Fixed weight per position (revert from ATR sizing which was too conservative)
        self.weight = 0.33
        self.max_positions = 3  # Concentrate in best 3 trends

        # Position tracking
        self.positions = {etf: 0 for etf in self.etf_list}

        # Warmup: need enough data for SMA50 + entry period
        warmup = max(self.trend_sma_period, self.entry_period) + 5
        self.set_warm_up(warmup, Resolution.DAILY)

        # Daily scan
        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self._daily_scan
        )

        self.set_benchmark("SPY")

    def _is_trending_up(self, symbol):
        """Check if price is above SMA50 (light trend filter)."""
        hist = self.history(symbol, self.trend_sma_period + 2, Resolution.DAILY)
        if hist.empty or len(hist) < self.trend_sma_period:
            return False

        closes = hist['close'].values
        sma = np.mean(closes[-self.trend_sma_period:])
        current_price = self.securities[symbol].price
        return current_price > sma

    def _daily_scan(self):
        if self.is_warming_up:
            return

        # Phase 1: Check exits (Donchian exit channel)
        for etf in self.etf_list:
            if self.positions[etf] == 0:
                continue

            symbol = self.symbols[etf]
            hist = self.history(symbol, self.exit_period + 1, Resolution.DAILY)
            if hist.empty or len(hist) < self.exit_period + 1:
                continue

            lows = hist['low'].values
            current_price = self.securities[symbol].price
            exit_low = np.min(lows[:-1])

            if current_price < exit_low:
                self.liquidate(symbol)
                self.positions[etf] = 0
                self.log(f"EXIT {etf} at {current_price:.2f} (Donchian low={exit_low:.2f})")

        # Phase 2: Check entries (Donchian breakout + light SMA50 trend filter)
        candidates = []
        for etf in self.etf_list:
            if self.positions[etf] == 1:
                continue

            symbol = self.symbols[etf]

            # Light trend filter: only enter assets trending above SMA50
            if not self._is_trending_up(symbol):
                continue

            hist = self.history(symbol, self.entry_period + 1, Resolution.DAILY)
            if hist.empty or len(hist) < self.entry_period + 1:
                continue

            highs = hist['high'].values
            current_price = self.securities[symbol].price
            entry_high = np.max(highs[:-1])

            if current_price > entry_high:
                # Momentum score: how far above the breakout level
                momentum = current_price / entry_high - 1
                candidates.append((etf, momentum))

        candidates.sort(key=lambda x: x[1], reverse=True)
        current_count = sum(self.positions.values())
        available = self.max_positions - current_count

        for etf, mom in candidates[:available]:
            symbol = self.symbols[etf]
            self.set_holdings(symbol, self.weight)
            self.positions[etf] = 1
            self.log(
                f"LONG {etf} at {self.securities[symbol].price:.2f}, "
                f"mom={mom:.3f}, weight={self.weight:.0%}"
            )

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        invested = sum(self.positions.values())
        self.log(
            f"TREND v3.1: Final=${final:,.2f}, "
            f"Return={(final-100000)/100000:.2%}, "
            f"Active positions={invested}"
        )
