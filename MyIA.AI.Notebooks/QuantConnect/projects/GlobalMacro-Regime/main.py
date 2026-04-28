# region imports
from AlgorithmImports import *
# endregion


class GlobalMacroRegime(QCAlgorithm):
    """
    Global Macro Regime v3: Rank-based Risk Parity + Regime Switch (BEST)
    =====================================================================
    Best variant: Sharpe 0.607, CAGR 11.62%, MaxDD 23.6%

    Bull regime: rank-based risk parity across trending assets.
    Bear regime: risk parity across BND, TLT, GLD.
    Regime signal: SPY > SMA200 AND SPY 6m return > 0.

    Iteration results:
    v1: Sharpe 0.499, CAGR 9.87%, MaxDD 18.0% (equal defensive)
    v2: Sharpe 0.583, CAGR 11.55%, MaxDD 21.6% (RP defensive + 6m filter)
    v3: Sharpe 0.607, CAGR 11.62%, MaxDD 23.6% (rank * inv_vol in risky) <-- BEST
    v4: Sharpe 0.604, CAGR 11.61%, MaxDD 23.6% (12m regime - no improvement)
    v5: Sharpe 0.582, CAGR 10.89%, MaxDD 23.7% (BND cushion - worse)
    v6: Sharpe 0.581, CAGR 11.20%, MaxDD 22.6% (max 25% cap - marginal)

    Reference: Bridgewater Risk Parity, Antonacci (2014)
    """

    RISKY_TICKERS = ["SPY", "EFA", "EEM", "TLT", "GLD", "DBC"]
    DEFENSIVE_TICKERS = ["BND", "TLT", "GLD"]
    ALL_TICKERS = ["SPY", "EFA", "EEM", "TLT", "GLD", "DBC", "BND"]
    MOM_12M = 252
    MOM_6M = 126
    MIN_TRENDING = 2

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100_000)
        self.set_benchmark("SPY")

        self.symbols = {}
        self.sma_ind = {}
        self.std_ind = {}
        for ticker in self.RISKY_TICKERS:
            security = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = security.symbol
            self.sma_ind[ticker] = self.sma(security.symbol, 200, Resolution.DAILY)
            self.std_ind[ticker] = self.STD(security.symbol, 60, Resolution.DAILY)

        for ticker in ["BND"]:
            if ticker not in self.symbols:
                security = self.add_equity(ticker, Resolution.DAILY)
                self.symbols[ticker] = security.symbol

        self.spy_sym = self.symbols["SPY"]
        self.spy_sma = self.sma(self.spy_sym, 200, Resolution.DAILY)

        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance,
        )

        self.set_warm_up(timedelta(days=300))

    def _is_bull_regime(self):
        if not self.spy_sma.is_ready:
            return True
        spy_price = self.securities[self.spy_sym].close
        if spy_price <= self.spy_sma.current.value:
            return False
        hist = self.history(self.spy_sym, self.MOM_6M + 5, Resolution.DAILY)
        if len(hist) < self.MOM_6M * 0.8:
            return True
        ret_6m = hist["close"].iloc[-1] / hist["close"].iloc[-self.MOM_6M] - 1
        return ret_6m > 0

    def _get_inv_vol(self, ticker):
        sym = self.symbols[ticker]
        std_ind = self.std_ind.get(ticker)
        if std_ind and std_ind.is_ready and std_ind.current.value > 0:
            price = self.securities[sym].price
            if price > 0:
                return price / std_ind.current.value
        return 1.0

    def _risk_parity_weights(self, tickers):
        inv_vols = {t: self._get_inv_vol(t) for t in tickers}
        total = sum(inv_vols.values())
        if total > 0:
            return {t: v / total for t, v in inv_vols.items()}
        return {t: 1.0 / len(tickers) for t in tickers}

    def rebalance(self):
        if self.is_warming_up:
            return

        bull = self._is_bull_regime()
        targets = {}

        if bull:
            trending = {}
            for ticker in self.RISKY_TICKERS:
                ind = self.sma_ind.get(ticker)
                if not ind or not ind.is_ready:
                    continue
                sym = self.symbols[ticker]
                close = self.securities[sym].close
                if close <= ind.current.value:
                    continue
                hist_6m = self.history(sym, self.MOM_6M + 5, Resolution.DAILY)
                if len(hist_6m) < self.MOM_6M * 0.8:
                    continue
                ret_6m = hist_6m["close"].iloc[-1] / hist_6m["close"].iloc[-self.MOM_6M] - 1
                if ret_6m <= 0:
                    continue
                hist_12m = self.history(sym, self.MOM_12M + 5, Resolution.DAILY)
                if len(hist_12m) < self.MOM_12M * 0.8:
                    ret_12m = ret_6m
                else:
                    ret_12m = hist_12m["close"].iloc[-1] / hist_12m["close"].iloc[-self.MOM_12M] - 1
                trending[ticker] = ret_12m

            sorted_trending = sorted(trending.items(), key=lambda x: x[1], reverse=True)
            if len(sorted_trending) >= self.MIN_TRENDING:
                n = len(sorted_trending)
                raw_weights = []
                for i, (ticker, _) in enumerate(sorted_trending):
                    rank_score = (n - i) / n
                    inv_vol = self._get_inv_vol(ticker)
                    raw_weights.append((ticker, rank_score * inv_vol))
                total = sum(w for _, w in raw_weights)
                for ticker, w in raw_weights:
                    targets[ticker] = w / total
            else:
                targets = self._risk_parity_weights(self.DEFENSIVE_TICKERS)
        else:
            targets = self._risk_parity_weights(self.DEFENSIVE_TICKERS)

        regime = "BULL" if bull else "BEAR"
        tgt_str = ", ".join(f"{t}:{w:.1%}" for t, w in sorted(targets.items()))
        self.log(f"{regime} | {tgt_str}")

        for ticker in self.ALL_TICKERS:
            sym = self.symbols[ticker]
            if ticker in targets:
                self.set_holdings(sym, targets[ticker])
            elif self.portfolio[sym].invested:
                self.liquidate(sym)

    def on_data(self, data: Slice):
        pass
