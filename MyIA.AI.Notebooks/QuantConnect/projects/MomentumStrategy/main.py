# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class SectorMomentumETFRotation(QCAlgorithm):
    """
    Sector ETF Momentum Rotation Strategy v3.0

    Signal-focused improvements over v2.1:
    1. Volatility-adjusted momentum score (momentum / 63d vol):
       - Ranks sectors by risk-adjusted return, not raw return
       - Reduces whipsaws: high-vol sectors need higher raw return to qualify
       - Source: Asness et al. (2013) "Value and Momentum Everywhere"
    2. Skip-month (12m-1m): measure momentum from day 252 to day 21
       - Avoids short-term reversal contamination (Jegadeesh 1990)
       - Standard in academic momentum literature
    3. Top 4 sectors instead of 3:
       - Better diversification (36% selection rate vs 27%)
       - Still concentrated enough to capture momentum premium
    4. Secondary SMA20 filter on SPY:
       - Reduces false risk-off signals in volatile but uptrending markets
       - Both SMA200 AND SMA20 must be violated to trigger risk-off

    Backtest results:
    v1.0: Sharpe 0.216, CAGR 6.5%, MaxDD 29.9% (composite, TLT risk-off)
    v2.0: Sharpe 0.149, CAGR 5.3%, MaxDD 33.7% (12m, cash risk-off)
    v2.1: Sharpe 0.411, CAGR 10.8%, MaxDD 30.1%, Net +214.7% (BEST prev)
    v2.2: Sharpe 0.414, CAGR 10.9%, MaxDD 31.9% (composite, similar)
    v3.0: Sharpe 0.459, CAGR 11.5%, MaxDD 30.0%, Net +237.0% (vol-adj, skip-month, top4, SMA20)

    ETFs sectoriels: XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC
    Ref: Jegadeesh & Titman (1993), Faber (2007), Asness (2013), research.ipynb
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
        self.spy_sma200 = self.sma(self.spy, 200, Resolution.DAILY)
        self.spy_sma20 = self.sma(self.spy, 20, Resolution.DAILY)

        # Parameters
        self.top_n = 4              # Number of sectors to hold (top 4 of 11)
        self.lookback = 252         # 12-month total lookback
        self.skip_days = 21         # Skip last 1 month (avoid short-term reversal)
        self.vol_window = 63        # 3-month window for volatility normalization
        self.rebalance_month = -1

        self.set_benchmark("SPY")
        self.set_warm_up(self.lookback + 30, Resolution.DAILY)

    def _momentum_score(self, symbol):
        """
        Volatility-adjusted skip-month momentum score.

        Score = (12m-1m momentum) / (3m realized volatility)

        Skip-month: avoid short-term reversal bias (Jegadeesh 1990)
        Vol-adjusted: reward consistent momentum, penalize high-vol noise
        """
        history = self.history(symbol, self.lookback + 5, Resolution.DAILY)
        if len(history) < self.lookback:
            return None

        closes = history['close']

        # Skip-month momentum: from day[0] to day[-skip_days]
        # Current = iloc[-skip_days], Past = iloc[0]
        current_price = closes.iloc[-self.skip_days]
        past_price = closes.iloc[0]

        if past_price <= 0 or current_price <= 0:
            return None

        raw_momentum = (current_price / past_price) - 1

        # 3-month volatility (annualized daily returns std)
        recent_closes = closes.iloc[-self.vol_window:]
        if len(recent_closes) < 20:
            return None

        daily_returns = recent_closes.pct_change().dropna()
        vol = daily_returns.std()

        if vol <= 0:
            return None

        # Risk-adjusted momentum score
        vol_adj_score = raw_momentum / vol

        return vol_adj_score, raw_momentum  # Return both for logging/filtering

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not self.spy_sma200.is_ready or not self.spy_sma20.is_ready:
            return

        # Monthly rebalancing
        if self.time.month == self.rebalance_month:
            return
        self.rebalance_month = self.time.month

        # Calculate momentum for all sectors
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

        # Regime filter: risk-off only if SPY below BOTH SMA200 AND SMA20
        # This reduces false risk-off signals in volatile but uptrending markets
        spy_price = self.securities[self.spy].price
        below_sma200 = spy_price < self.spy_sma200.current.value
        below_sma20 = spy_price < self.spy_sma20.current.value
        risk_off = below_sma200 and below_sma20

        if not risk_off:
            # RISK ON: select top N sectors with positive raw momentum
            # Sort by vol-adjusted score, but require positive raw momentum
            sorted_sectors = sorted(scores.items(), key=lambda x: x[1], reverse=True)
            top_sectors = [t for t, s in sorted_sectors[:self.top_n]
                           if raw_scores.get(t, 0) > 0]

            if len(top_sectors) == 0:
                # All sectors have negative raw momentum -> defensive
                self.liquidate()
                self.set_holdings(self.symbols["XLP"], 0.5)
                self.set_holdings(self.symbols["XLU"], 0.5)
                self.log(f"[ALL NEG MOM] -> XLP+XLU defensive")
                return

            weight = 1.0 / len(top_sectors)

            # Liquidate positions not in top
            for ticker, symbol in self.symbols.items():
                if ticker not in top_sectors and self.portfolio[symbol].invested:
                    self.liquidate(symbol)

            for ticker in top_sectors:
                self.set_holdings(self.symbols[ticker], weight)

            top_str = ", ".join([f"{t}(vol-adj={scores[t]:.2f}, raw={raw_scores[t]:.3f})"
                                  for t in top_sectors])
            self.log(f"[RISK ON] Top {len(top_sectors)}: {top_str}")
        else:
            # Risk-off: rotate to defensive sectors (XLP + XLU)
            for ticker, symbol in self.symbols.items():
                if ticker not in ["XLP", "XLU"] and self.portfolio[symbol].invested:
                    self.liquidate(symbol)
            self.set_holdings(self.symbols["XLP"], 0.5)
            self.set_holdings(self.symbols["XLU"], 0.5)
            self.log(f"[RISK OFF] SPY={spy_price:.2f} < SMA200({self.spy_sma200.current.value:.2f}) & SMA20({self.spy_sma20.current.value:.2f})")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"MOMENTUM v3.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
