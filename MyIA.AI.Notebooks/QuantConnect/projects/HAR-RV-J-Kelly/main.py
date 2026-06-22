# region imports
from AlgorithmImports import *
# endregion
import numpy as np
from collections import deque


class HarrvjKellyAlgorithm(QCAlgorithm):
    """HAR-RV-J / HAR Classic Kelly strategy on crypto assets.

    Extends HAR (Corsi 2009) with optional jump component from
    Huang-Tauchen bipower variation (Andersen, Bollerslev & Diebold 2007).

    RV_t = BPV_t + J_t,  where J_t = max(RV_t - (pi/2)*BPV_t, 0)

    Set parameter use_jumps=1 for HAR-RV-J (6 features),
    use_jumps=0 for HAR Classic (3 features).

    Kelly 1/4 fraction for position sizing.
    Assets: BTCUSDT, ETHUSDT, LTCUSDT, BCHUSDT (crypto, Binance).
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_end_date(2025, 6, 1)
        self.set_cash(100000)
        self.set_account_currency("USDT")
        self.set_brokerage_model(BrokerageName.BINANCE, AccountType.CASH)

        # Parameter: 1 = HAR-RV-J (6 features), 0 = HAR Classic (3 features)
        self.use_jumps = self.get_parameter("use_jumps", "1") == "1"

        # Crypto tickers (Binance-provided)
        self.tickers = ["BTCUSDT", "ETHUSDT", "LTCUSDT", "BCHUSDT"]
        self.symbols = {}
        for ticker in self.tickers:
            crypto = self.add_crypto(ticker, Resolution.DAILY, Market.BINANCE)
            self.symbols[ticker] = crypto.symbol

        # Model parameters
        self.train_window = 500
        self.refit_freq = 22
        self.kelly_fraction = 0.25
        self.forecast_horizon = 5

        # Per-asset state
        self.daily_rv = {t: deque(maxlen=self.train_window + 50) for t in self.tickers}
        self.daily_bpv = {t: deque(maxlen=self.train_window + 50) for t in self.tickers}
        self.daily_jumps = {t: deque(maxlen=self.train_window + 50) for t in self.tickers}
        self.daily_ret = {t: deque(maxlen=50) for t in self.tickers}
        self.coefs = {t: None for t in self.tickers}
        self.last_fit_day = {t: -100 for t in self.tickers}

        self.day_count = 0

        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.at(0, 0),
            self.rebalance,
        )

        self.set_warm_up(250, Resolution.DAILY)

    def on_data(self, data: Slice):
        for ticker, sym in self.symbols.items():
            if not data.bars.contains_key(sym):
                continue
            bar = data[sym]
            if bar is None:
                continue

            hist = self.history(sym, 2, Resolution.DAILY)
            if hist is not None and len(hist) >= 2:
                prev = float(hist["close"].iloc[-2])
                curr = float(bar.close)
                if prev > 0:
                    r = np.log(curr / prev)
                    rv = r ** 2

                    rets = list(self.daily_ret[ticker])
                    if len(rets) >= 1:
                        bpv = (np.pi / 2) * abs(r) * abs(rets[-1])
                    else:
                        bpv = rv

                    jump = max(rv - bpv, 0)

                    self.daily_rv[ticker].append(rv)
                    self.daily_bpv[ticker].append(bpv)
                    self.daily_jumps[ticker].append(jump)
                    self.daily_ret[ticker].append(r)

        self.day_count += 1

    def rebalance(self):
        if self.is_warming_up:
            return

        weights = {}
        for ticker in self.tickers:
            sym = self.symbols[ticker]
            if len(self.daily_rv[ticker]) < self.train_window:
                continue

            var_forecast = self._forecast(ticker)
            if var_forecast is None or var_forecast <= 0:
                continue

            vol_ann = np.sqrt(var_forecast * 252 / self.forecast_horizon)

            rets = list(self.daily_ret[ticker])
            if len(rets) < 5:
                continue
            mom_5d = sum(rets[-5:])
            direction = 1.0 if mom_5d > 0 else 0.0

            mu_daily = np.mean(rets[-20:]) if len(rets) >= 20 else 0.0
            mu_ann = mu_daily * 252
            var_ann = vol_ann ** 2

            if var_ann > 1e-8:
                kelly_full = mu_ann / var_ann
                kelly_adj = max(0, kelly_full * self.kelly_fraction)
                w = min(kelly_adj, 0.30) * direction
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

    def _forecast(self, ticker):
        """Unified forecast: HAR-RV-J or HAR Classic based on parameter."""
        rv = np.array(self.daily_rv[ticker])
        n = len(rv)
        if n < self.train_window:
            return None
        rv = rv[-self.train_window:]

        jumps = np.array(self.daily_jumps[ticker])[-self.train_window:] if self.use_jumps else None

        should_refit = (self.day_count - self.last_fit_day[ticker]) >= self.refit_freq
        if should_refit or self.coefs[ticker] is None:
            coefs = self._fit(rv, jumps)
            if coefs is not None:
                self.coefs[ticker] = coefs
                self.last_fit_day[ticker] = self.day_count

        if self.coefs[ticker] is None:
            return None

        log_rv = np.log(np.maximum(rv, 1e-12))
        rv_d = log_rv[-1]
        rv_w = float(np.mean(log_rv[-5:])) if len(log_rv) >= 5 else rv_d
        rv_m = float(np.mean(log_rv[-22:])) if len(log_rv) >= 22 else rv_w

        c = self.coefs[ticker]
        if self.use_jumps:
            j_d = jumps[-1]
            j_w = float(np.mean(jumps[-5:])) if len(jumps) >= 5 else j_d
            j_m = float(np.mean(jumps[-22:])) if len(jumps) >= 22 else j_w
            log_rv_pred = c[0] + c[1]*rv_d + c[2]*rv_w + c[3]*rv_m + c[4]*j_d + c[5]*j_w + c[6]*j_m
        else:
            log_rv_pred = c[0] + c[1]*rv_d + c[2]*rv_w + c[3]*rv_m

        # Iterated h-step forecast
        hist_rv = list(log_rv)
        hist_j = list(jumps) if jumps is not None else None
        for _ in range(self.forecast_horizon - 1):
            tail_rv = hist_rv[-22:]
            d = tail_rv[-1]
            w = float(np.mean(tail_rv[-5:]))
            m = float(np.mean(tail_rv))
            if self.use_jumps and hist_j is not None:
                tail_j = hist_j[-22:]
                jd = tail_j[-1]
                jw = float(np.mean(tail_j[-5:]))
                jm = float(np.mean(tail_j))
                pred = c[0] + c[1]*d + c[2]*w + c[3]*m + c[4]*jd + c[5]*jw + c[6]*jm
                hist_j.append(jm)
            else:
                pred = c[0] + c[1]*d + c[2]*w + c[3]*m
            hist_rv.append(pred)

        avg_log_rv = float(np.mean(hist_rv[len(log_rv):]))
        return np.exp(avg_log_rv)

    def _fit(self, rv, jumps):
        """OLS fit: HAR-RV-J(6 features) or HAR Classic(3 features)."""
        log_rv = np.log(np.maximum(rv, 1e-12))
        n = len(log_rv)
        if n < 50:
            return None

        y = []
        X = []
        for i in range(22, n - 1):
            y.append(log_rv[i + 1])
            rv_d = log_rv[i]
            rv_w = float(np.mean(log_rv[max(0, i - 4):i + 1]))
            rv_m = float(np.mean(log_rv[max(0, i - 21):i + 1]))
            if self.use_jumps and jumps is not None:
                j_d = jumps[i]
                j_w = float(np.mean(jumps[max(0, i - 4):i + 1]))
                j_m = float(np.mean(jumps[max(0, i - 21):i + 1]))
                X.append([1.0, rv_d, rv_w, rv_m, j_d, j_w, j_m])
            else:
                X.append([1.0, rv_d, rv_w, rv_m])

        if len(y) < 30:
            return None

        X = np.array(X)
        y = np.array(y)
        try:
            coefs, _, _, _ = np.linalg.lstsq(X, y, rcond=None)
            return tuple(coefs)
        except Exception:
            return None
