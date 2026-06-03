# [ARCHIVED - Sharpe ceiling ~0.48, cf ARCHIVE.md]
# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class SectorMomentumETFRotation(QCAlgorithm):
    """
    Sector ETF Momentum Rotation Strategy v4.0 (CONFIRMED BEST)

    Skip-month vol-adjusted momentum + dual regime filter + stop-loss.

    Iteration history:
    v1.0: Sharpe 0.216, CAGR 6.5%, MaxDD 29.9%
    v2.1: Sharpe 0.411, CAGR 10.8%, MaxDD 30.1%
    v3.0: Sharpe 0.459, CAGR 11.5%, MaxDD 30.0%
    v4.0: Sharpe 0.472, CAGR 11.1%, MaxDD 25.8% (BEST)
    v5.0: Sharpe 0.398 REJECTED (proportional weights)
    v6.0: Sharpe 0.441 REJECTED (trailing stop cut winners)
    v6.1: Sharpe 0.460 REJECTED (TLT risk-off worse MaxDD)
    v6.2: Sharpe 0.395 REJECTED (target vol + SMA50 filter)

    Conclusion: Sharpe ceiling ~0.48 for sector ETF monthly rotation.
    Ref: Jegadeesh & Titman (1993), Faber (2007), Asness (2013)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)

        self.sector_tickers = [
            "XLK", "XLF", "XLE", "XLV", "XLI",
            "XLY", "XLP", "XLU", "XLB", "XLRE", "XLC",
        ]

        self.symbols = {}
        for ticker in self.sector_tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = equity.symbol

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.spy_sma200 = self.sma(self.spy, 200, Resolution.DAILY)
        self.spy_sma20 = self.sma(self.spy, 20, Resolution.DAILY)

        self.top_n = 4
        self.lookback = 252
        self.skip_days = 21
        self.vol_window = 63
        self.stop_loss_pct = -0.10
        self.rebalance_month = -1
        self.entry_prices = {}

        self.set_benchmark("SPY")
        self.set_warm_up(self.lookback + 30, Resolution.DAILY)

    def _momentum_score(self, symbol):
        history = self.history(symbol, self.lookback + 5, Resolution.DAILY)
        if len(history) < self.lookback:
            return None

        closes = history['close']
        current_price = closes.iloc[-self.skip_days]
        past_price = closes.iloc[0]
        if past_price <= 0 or current_price <= 0:
            return None

        raw_momentum = (current_price / past_price) - 1

        recent_closes = closes.iloc[-self.vol_window:]
        if len(recent_closes) < 20:
            return None

        daily_returns = recent_closes.pct_change().dropna()
        vol = daily_returns.std()
        if vol <= 0:
            return None

        vol_adj_score = raw_momentum / vol
        return vol_adj_score, raw_momentum

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not self.spy_sma200.is_ready or not self.spy_sma20.is_ready:
            return

        # Daily stop-loss check
        for ticker, entry_price in list(self.entry_prices.items()):
            symbol = self.symbols.get(ticker)
            if symbol is None:
                continue
            if not self.portfolio[symbol].invested:
                del self.entry_prices[ticker]
                continue
            current_price = self.securities[symbol].price
            if current_price > 0 and entry_price > 0:
                pct_change = (current_price / entry_price) - 1
                if pct_change < self.stop_loss_pct:
                    self.liquidate(symbol)
                    del self.entry_prices[ticker]
                    self.log(f"[STOP-LOSS] {ticker}: {pct_change:.1%} from entry {entry_price:.2f}")

        # Monthly rebalancing
        if self.time.month == self.rebalance_month:
            return
        self.rebalance_month = self.time.month

        scores = {}
        raw_scores = {}
        for ticker, symbol in self.symbols.items():
            result = self._momentum_score(symbol)
            if result is not None:
                vol_adj, raw_mom = result
                scores[ticker] = vol_adj
                raw_scores[ticker] = raw_mom

        if len(scores) < self.top_n:
            return

        # Dual regime filter: risk-off only if SPY below BOTH SMA200 AND SMA20
        spy_price = self.securities[self.spy].price
        below_sma200 = spy_price < self.spy_sma200.current.value
        below_sma20 = spy_price < self.spy_sma20.current.value
        risk_off = below_sma200 and below_sma20

        if not risk_off:
            sorted_sectors = sorted(scores.items(), key=lambda x: x[1], reverse=True)
            top_sectors = [t for t, s in sorted_sectors[:self.top_n]
                           if raw_scores.get(t, 0) > 0]

            if len(top_sectors) == 0:
                self.liquidate()
                self.set_holdings(self.symbols["XLP"], 0.5)
                self.set_holdings(self.symbols["XLU"], 0.5)
                self.log("[ALL NEG MOM] -> XLP+XLU defensive")
                return

            weight = 1.0 / len(top_sectors)

            for ticker, symbol in self.symbols.items():
                if ticker not in top_sectors and self.portfolio[symbol].invested:
                    self.liquidate(symbol)
                    self.entry_prices.pop(ticker, None)

            for ticker in top_sectors:
                symbol = self.symbols[ticker]
                if not self.portfolio[symbol].invested:
                    self.entry_prices[ticker] = self.securities[symbol].price
                self.set_holdings(symbol, weight)

            top_str = ", ".join(top_sectors)
            self.log(f"[RISK ON] Top {len(top_sectors)}: {top_str}")
        else:
            for ticker, symbol in self.symbols.items():
                if ticker not in ["XLP", "XLU"] and self.portfolio[symbol].invested:
                    self.liquidate(symbol)
                    self.entry_prices.pop(ticker, None)
            for def_ticker in ["XLP", "XLU"]:
                def_symbol = self.symbols[def_ticker]
                if not self.portfolio[def_symbol].invested:
                    self.entry_prices[def_ticker] = self.securities[def_symbol].price
            self.set_holdings(self.symbols["XLP"], 0.5)
            self.set_holdings(self.symbols["XLU"], 0.5)
            self.log(f"[RISK OFF] SPY={spy_price:.2f} < SMA200+SMA20")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"MOMENTUM v4.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
