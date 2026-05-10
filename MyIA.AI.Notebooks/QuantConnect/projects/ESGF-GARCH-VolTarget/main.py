# region imports
from AlgorithmImports import *
# endregion
import numpy as np
from collections import deque


class ESGFGARCHVolTarget(QCAlgorithm):
    """GARCH(1,1) volatility targeting on a multi-asset portfolio.

    Forecasts next-day variance using a rolling GARCH(1,1) model fitted
    via variance-targeting MLE, then sizes each position inversely
    proportional to its forecasted volatility so that each asset
    contributes equally to portfolio risk.

    No directional prediction -- pure risk budgeting. Uses SMA200 trend
    filter for direction (long only, no shorts).

    Assets: SPY, EFA, EEM, TLT, GLD, DBC (AQR-style multi-asset).
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2025, 1, 1)
        self.set_cash(100000)

        self.set_brokerage_model(
            BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN
        )

        # Multi-asset universe
        self.tickers = ["SPY", "EFA", "EEM", "TLT", "GLD", "DBC"]
        self.symbols = {}
        for ticker in self.tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = equity.symbol

        self.set_benchmark(self.symbols["SPY"])

        # GARCH state per asset
        self.garch_params = {t: (1e-5, 0.10, 0.85) for t in self.tickers}
        self.cond_var = {t: None for t in self.tickers}
        self.last_fit_day = {t: -100 for t in self.tickers}
        self.train_window = 500
        self.refit_freq = 22

        # Vol target: 10% annualized per asset slot
        self.vol_target_ann = 0.10

        # SMA200 for trend direction (use sma_ind to avoid shadowing self.SMA())
        self.sma_ind = {}
        for ticker, sym in self.symbols.items():
            self.sma_ind[ticker] = self.SMA(sym, 200, Resolution.DAILY)

        # Rolling return history
        self.returns = {
            t: deque(maxlen=self.train_window + 50) for t in self.tickers
        }

        self.day_count = 0

        # Rebalance weekly (Monday)
        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.after_market_open(self.symbols["SPY"], 30),
            self.rebalance,
        )

        self.set_warm_up(250, Resolution.DAILY)

    def on_data(self, data: Slice):
        for ticker, sym in self.symbols.items():
            if not data.ContainsKey(sym):
                continue
            bar = data[sym]
            if bar is None:
                continue
            hist = self.history(sym, 2, Resolution.DAILY)
            if hist is not None and len(hist) >= 2:
                prev = float(hist["close"].iloc[-2])
                curr = float(bar.close)
                if prev > 0:
                    self.returns[ticker].append(np.log(curr / prev))
        self.day_count += 1

    def rebalance(self):
        if self.is_warming_up:
            return

        weights = {}
        for ticker in self.tickers:
            sym = self.symbols[ticker]
            if len(self.returns[ticker]) < self.train_window:
                continue
            if not self.sma_ind[ticker].IsReady:
                continue

            var_forecast = self._garch_forecast(ticker)
            if var_forecast is None or var_forecast <= 0:
                continue

            vol_ann = np.sqrt(var_forecast * 252)

            # Direction via SMA200
            price = float(self.securities[sym].price)
            direction = 1.0 if price > float(self.sma_ind[ticker].Current.Value) else 0.0

            # Inverse-vol sizing
            if vol_ann > 0.01:
                w = (self.vol_target_ann / vol_ann) * direction
                w = min(w, 0.30)
            else:
                w = 0.0
            weights[ticker] = w

        total = sum(weights.values())
        if total > 1.0:
            weights = {t: w / total for t, w in weights.items()}

        for ticker in self.tickers:
            sym = self.symbols[ticker]
            w = weights.get(ticker, 0.0)
            if w > 0.001:
                self.set_holdings(sym, w)
            else:
                self.liquidate(sym)

    def _garch_forecast(self, ticker):
        rets = np.array(self.returns[ticker])[-self.train_window:]
        n = len(rets)
        if n < self.train_window:
            return None

        should_refit = (self.day_count - self.last_fit_day[ticker]) >= self.refit_freq

        if should_refit or self.cond_var[ticker] is None:
            params = self._fit_garch_vt(rets)
            if params is not None:
                self.garch_params[ticker] = params
                self.last_fit_day[ticker] = self.day_count
            omega, alpha, beta = self.garch_params[ticker]
            var_series = self._cond_var_series(rets, omega, alpha, beta)
            if var_series is None:
                return None
            self.cond_var[ticker] = float(var_series[-1])
        else:
            omega, alpha, beta = self.garch_params[ticker]
            last_r = float(rets[-1])
            self.cond_var[ticker] = omega + alpha * last_r ** 2 + beta * self.cond_var[ticker]

        omega, alpha, beta = self.garch_params[ticker]
        return omega + alpha * float(rets[-1]) ** 2 + beta * self.cond_var[ticker]

    def _fit_garch_vt(self, rets):
        sigma2 = float(np.var(rets))
        best_ll = -1e30
        best = None
        for alpha in np.arange(0.05, 0.25, 0.05):
            for beta in np.arange(0.75, 0.95, 0.05):
                if alpha + beta >= 0.999:
                    continue
                omega = sigma2 * (1.0 - alpha - beta)
                if omega <= 0:
                    continue
                ll = self._garch_loglik(rets, omega, alpha, beta)
                if ll > best_ll:
                    best_ll = ll
                    best = (omega, alpha, beta)
        return best

    def _garch_loglik(self, rets, omega, alpha, beta):
        n = len(rets)
        v = float(np.var(rets[:min(50, n)]))
        ll = 0.0
        for i in range(n):
            v = omega + alpha * rets[i] ** 2 + beta * v
            if v <= 1e-15:
                return -1e30
            ll += -0.5 * (np.log(2 * np.pi) + np.log(v) + rets[i] ** 2 / v)
        return ll

    def _cond_var_series(self, rets, omega, alpha, beta):
        n = len(rets)
        var = np.empty(n)
        var[0] = float(np.var(rets[:min(50, n)]))
        for i in range(1, n):
            var[i] = omega + alpha * rets[i - 1] ** 2 + beta * var[i - 1]
            if var[i] < 0:
                return None
        return var
