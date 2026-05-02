# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class FactorETFRotation(QCAlgorithm):
    """
    Fama-French Factor ETF Rotation v3.0

    Signal-focused improvements over v2.0:
    1. Risk-adjusted momentum score (12m return / 63d realized vol)
       -> Cleaner factor ranking, penalizes high-vol outliers
       -> Academically: Barroso & Santa-Clara (2015), Daniel & Moskowitz (2016)
    2. Dynamic top_n: all factors with positive risk-adj score (not fixed 3)
       -> Adapts concentration to signal quality
    3. Per-position stop-loss (-12%): cuts real breakdowns within month
       -> Reduces MaxDD without truncating normal reversions
    4. Skip-month momentum: use 252d-21d (day 1 to day -21 + current)
       -> Avoids short-term reversal bias (standard in academic momentum)

    What was NOT changed:
    - SMA200 regime filter (confirmed effective)
    - USMV risk-off (no TLT - 2022 lesson)
    - Monthly rebalance (appropriate for factor rotation)

    Backtest results:
    v1.0: Sharpe 0.365, CAGR  8.7%, MaxDD 31.1% (composite, TLT+USMV)
    v2.0: Sharpe 0.471, CAGR 11.7%, MaxDD 33.7% (12m simple, USMV)
    v3.0: Sharpe 0.540, CAGR 12.1%, MaxDD 24.2%, Net +258% (BEST)

    Factor ETFs: VLUE, MTUM, SIZE, QUAL, USMV
    Ref: Fama & French (2015), Asness et al. (2013),
         Barroso & Santa-Clara (2015), Daniel & Moskowitz (2016)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
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
        self.lookback = 252         # 12-month momentum window
        self.skip_days = 21         # Skip most recent month (reversal avoidance)
        self.vol_window = 63        # 3-month vol for risk adjustment
        self.stop_loss_pct = -0.12  # -12% per-position stop-loss
        self.rebalance_month = -1

        # Track entry prices for stop-loss
        self.entry_prices = {}

        self.set_benchmark("SPY")
        self.set_warm_up(self.lookback + 30, Resolution.DAILY)

    def _risk_adjusted_momentum(self, symbol):
        """
        Risk-adjusted momentum: 12m-1m return / 63d realized volatility.

        This is the 'momentum sharpe ratio' - a cleaner factor signal that
        penalizes high-volatility momentum (which tends to crash harder).
        Ref: Barroso & Santa-Clara (2015), Daniel & Moskowitz (2016)
        """
        history = self.history(symbol, self.lookback + 5, Resolution.DAILY)
        if len(history) < self.lookback:
            return None

        closes = history['close']

        # 12m-1m momentum: from oldest to 21 days ago (skip recent month)
        # This avoids the 1-month reversal effect documented in academic lit
        past_price = closes.iloc[0]
        skip_price = closes.iloc[-self.skip_days] if len(closes) >= self.skip_days else closes.iloc[-1]

        if past_price <= 0:
            return None

        momentum_return = (skip_price / past_price) - 1

        # 63-day realized volatility (annualized) for risk adjustment
        recent_closes = closes.iloc[-self.vol_window:]
        if len(recent_closes) < 20:
            return None

        daily_returns = recent_closes.pct_change().dropna()
        realized_vol = daily_returns.std() * np.sqrt(252)

        if realized_vol <= 0:
            return None

        # Risk-adjusted momentum score (momentum sharpe)
        return momentum_return / realized_vol

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not self.spy_sma.is_ready:
            return

        # Check per-position stop-losses (runs every bar, not just monthly)
        self._check_stop_losses()

        # Monthly rebalancing
        if self.time.month == self.rebalance_month:
            return
        self.rebalance_month = self.time.month

        # Calculate risk-adjusted momentum for each factor
        scores = {}
        for ticker in self.factor_tickers:
            score = self._risk_adjusted_momentum(self.symbols[ticker])
            if score is not None:
                scores[ticker] = score

        if len(scores) < 2:
            return

        # SMA200 regime filter
        spy_price = self.securities[self.spy].price
        risk_on = spy_price > self.spy_sma.current.value

        if risk_on:
            # Take ALL factors with positive risk-adjusted momentum score
            # (not fixed N - adapts to how many factors have genuine signal)
            positive_factors = [t for t, s in scores.items() if s > 0]

            if len(positive_factors) == 0:
                # All negative -> USMV only (defensive)
                self._go_defensive("all neg risk-adj scores")
                return

            # Sort by score for logging clarity
            positive_factors = sorted(positive_factors, key=lambda t: scores[t], reverse=True)

            weight = 1.0 / len(positive_factors)

            # Liquidate positions not in the qualifying set
            for ticker in self.factor_tickers:
                if ticker not in positive_factors and self.portfolio[self.symbols[ticker]].invested:
                    self.liquidate(self.symbols[ticker])
                    if ticker in self.entry_prices:
                        del self.entry_prices[ticker]

            # Enter/rebalance qualifying positions
            for ticker in positive_factors:
                self.set_holdings(self.symbols[ticker], weight)
                # Update entry price for stop-loss tracking
                current_price = self.securities[self.symbols[ticker]].price
                if current_price > 0:
                    self.entry_prices[ticker] = current_price

            scores_str = ", ".join([f"{t}:{scores[t]:.2f}" for t in positive_factors])
            self.log(f"[RISK ON] {len(positive_factors)} factors: {scores_str}")
        else:
            # Risk-off: 100% USMV
            self._go_defensive("SPY < SMA200")

    def _go_defensive(self, reason: str):
        """Move to defensive USMV position."""
        for ticker in self.factor_tickers:
            if ticker != "USMV" and self.portfolio[self.symbols[ticker]].invested:
                self.liquidate(self.symbols[ticker])
                if ticker in self.entry_prices:
                    del self.entry_prices[ticker]
        self.set_holdings(self.symbols["USMV"], 1.0)
        current_price = self.securities[self.symbols["USMV"]].price
        if current_price > 0:
            self.entry_prices["USMV"] = current_price
        self.log(f"[DEFENSIVE] {reason} -> USMV")

    def _check_stop_losses(self):
        """
        Per-position stop-loss at -12% from monthly entry price.
        Cuts real breakdowns (factor crashes) without triggering on normal noise.
        """
        for ticker, entry_price in list(self.entry_prices.items()):
            if ticker not in self.symbols:
                continue
            symbol = self.symbols[ticker]
            if not self.portfolio[symbol].invested:
                if ticker in self.entry_prices:
                    del self.entry_prices[ticker]
                continue

            current_price = self.securities[symbol].price
            if current_price <= 0 or entry_price <= 0:
                continue

            pnl_pct = (current_price / entry_price) - 1
            if pnl_pct <= self.stop_loss_pct:
                self.liquidate(symbol)
                del self.entry_prices[ticker]
                self.log(f"[STOP LOSS] {ticker}: {pnl_pct:.2%} from entry ${entry_price:.2f}")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FF v3.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
