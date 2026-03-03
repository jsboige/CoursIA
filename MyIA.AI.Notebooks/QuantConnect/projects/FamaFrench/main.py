# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class FactorETFRotation(QCAlgorithm):
    """
    Fama-French Inspired Factor ETF Rotation

    Utilise des ETFs factoriels pour capturer les primes de risque Fama-French:
    - VLUE: Value factor (Book-to-Market eleve)
    - MTUM: Momentum factor (Performance recente)
    - SIZE: Size factor (Small caps premium)
    - QUAL: Quality factor (Profitability)
    - USMV: Min Volatility factor (Low beta)

    Allocation mensuelle basee sur momentum 3 mois des facteurs.
    Filtre SMA200 SPY pour regime risk-on/risk-off.

    Ref: Fama & French (2015), Asness et al. (2013)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)

        # Factor ETFs (iShares)
        self.factor_etfs = {
            "VLUE": "Value",      # iShares MSCI USA Value Factor
            "MTUM": "Momentum",   # iShares MSCI USA Momentum Factor
            "SIZE": "Size",       # iShares MSCI USA Size Factor
            "QUAL": "Quality",    # iShares MSCI USA Quality Factor
            "USMV": "MinVol",     # iShares MSCI USA Min Vol Factor
        }

        self.symbols = {}
        for ticker in self.factor_etfs:
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = equity.symbol

        # Benchmark and regime filter
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.spy_sma = self.sma(self.spy, 200, Resolution.DAILY)

        # Safe haven
        self.tlt = self.add_equity("TLT", Resolution.DAILY).symbol

        # Parameters
        self.top_n = 3  # Number of factors to hold
        self.lookback_short = 63  # 3 months momentum
        self.lookback_long = 252  # 12 months momentum
        self.vol_lookback = 60  # Volatility window
        self.rebalance_month = -1

        self.set_benchmark("SPY")
        self.set_warm_up(timedelta(self.lookback_long + 30))

    def _risk_adjusted_momentum(self, symbol):
        """Calculate risk-adjusted momentum (Sharpe-like score)."""
        history = self.history(symbol, self.lookback_long, Resolution.DAILY)
        if len(history) < self.lookback_long:
            return None

        returns = history['close'].pct_change().dropna()
        if len(returns) < self.lookback_short:
            return None

        # Short-term momentum (3 months)
        recent_return = (history['close'].iloc[-1] / history['close'].iloc[-self.lookback_short]) - 1

        # Long-term momentum (12 months)
        long_return = (history['close'].iloc[-1] / history['close'].iloc[0]) - 1

        # Volatility (annualized)
        vol = returns.tail(self.vol_lookback).std() * np.sqrt(252)
        if vol <= 0:
            return None

        # Composite: 60% short-term + 40% long-term, risk-adjusted
        composite_return = 0.6 * recent_return + 0.4 * long_return
        risk_adj_score = composite_return / vol

        return risk_adj_score

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not self.spy_sma.is_ready:
            return

        # Monthly rebalancing
        if self.time.month == self.rebalance_month:
            return
        self.rebalance_month = self.time.month

        # Calculate risk-adjusted momentum for each factor
        scores = {}
        for ticker, symbol in self.symbols.items():
            score = self._risk_adjusted_momentum(symbol)
            if score is not None:
                scores[ticker] = score

        if len(scores) < self.top_n:
            return

        # SMA200 regime filter
        spy_price = self.securities[self.spy].price
        risk_on = spy_price > self.spy_sma.current.value

        if risk_on:
            # Risk Parity weighting among top factors
            sorted_factors = sorted(scores.items(), key=lambda x: x[1], reverse=True)
            top_factors = [t for t, s in sorted_factors[:self.top_n]]

            # Calculate volatility-inverse weights
            vols = {}
            for ticker in top_factors:
                history = self.history(self.symbols[ticker], self.vol_lookback, Resolution.DAILY)
                if len(history) >= self.vol_lookback:
                    returns = history['close'].pct_change().dropna()
                    vol = returns.std() * np.sqrt(252)
                    if vol > 0:
                        vols[ticker] = vol

            if len(vols) == 0:
                return

            inv_vols = {t: 1.0 / v for t, v in vols.items()}
            total_inv = sum(inv_vols.values())
            weights = {t: iv / total_inv for t, iv in inv_vols.items()}

            # Liquidate positions not in top
            for ticker, symbol in self.symbols.items():
                if ticker not in weights and self.portfolio[symbol].invested:
                    self.liquidate(symbol)
            if self.portfolio[self.tlt].invested:
                self.liquidate(self.tlt)

            for ticker, weight in weights.items():
                self.set_holdings(self.symbols[ticker], weight)

            factor_str = ", ".join([f"{t}({self.factor_etfs[t]})={scores[t]:.2f}" for t in weights])
            self.log(f"[RISK ON] Factors: {factor_str}")
        else:
            # Risk-off: 70% TLT + 30% USMV (defensive)
            for ticker, symbol in self.symbols.items():
                if ticker != "USMV" and self.portfolio[symbol].invested:
                    self.liquidate(symbol)
            self.set_holdings(self.tlt, 0.70)
            self.set_holdings(self.symbols["USMV"], 0.30)
            self.log(f"[RISK OFF] SPY < SMA200 -> 70% TLT + 30% USMV")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FACTOR ETF: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
