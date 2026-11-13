# region imports
from AlgorithmImports import *
# endregion
import numpy as np
from collections import deque


class VolEnsembleConservativeAlgorithm(QCAlgorithm):
    """Ensemble GARCH + HAR vol forecast with conservative position sizing.

    Combines GARCH(1,1) and HAR(1,5,22) volatility forecasts as an
    ensemble (max of the two = conservative), then sizes positions
    using inverse-vol targeting at half the normal allocation.

    Adds a trend regime filter:
      - Bull regime (SPY > SMA200): full allocation
      - Bear regime (SPY < SMA200): reduce to 50% allocation

    This is the most conservative of the 3 volatility strategies.
    Assets: SPY, EFA, EEM, TLT, GLD, DBC.

    Mesure de ligue (#26322, gabarit #22828) : le parametre `mode` ajoute
    les references detenues et les diagnostics sans toucher la decision de
    la strategie. Valeurs : strategy (defaut, code actuel), spy, 6040,
    ew6 (univers equipondere, diagnostic), noregime (sans le filtre SMA200,
    diagnostic).
    """

    def initialize(self):
        self.mode = (self.get_parameter("mode") or "strategy").lower()
        if self.mode not in ("strategy", "spy", "6040", "ew6", "noregime"):
            raise ValueError(f"mode inconnu : {self.mode}")

        start_date = self.get_parameter("start_date") or "2018-01-01"
        end_date = self.get_parameter("end_date") or "2025-01-01"
        sy, sm, sd = (int(v) for v in start_date.split("-"))
        ey, em, ed = (int(v) for v in end_date.split("-"))
        self.set_start_date(sy, sm, sd)
        self.set_end_date(ey, em, ed)
        self.set_cash(100000)

        self.set_brokerage_model(
            BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN
        )

        self.tickers = ["SPY", "EFA", "EEM", "TLT", "GLD", "DBC"]
        self.symbols = {}
        if self.mode == "spy":
            subscribed = ["SPY"]
        elif self.mode == "6040":
            subscribed = ["SPY", "BND"]
        else:
            subscribed = list(self.tickers)
        for ticker in subscribed:
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = equity.symbol

        self.set_benchmark(self.symbols["SPY"])

        # GARCH state
        self.garch_params = {t: (1e-5, 0.10, 0.85) for t in self.tickers}
        self.cond_var = {t: None for t in self.tickers}

        # HAR state
        self.har_coefs = {t: None for t in self.tickers}

        # Shared
        self.train_window = 500
        self.refit_freq = 22
        self.last_fit_day = {t: -100 for t in self.tickers}
        self.returns = {t: deque(maxlen=self.train_window + 50) for t in self.tickers}
        self.daily_rv = {t: deque(maxlen=self.train_window + 50) for t in self.tickers}

        # Conservative sizing: half vol target
        self.vol_target_ann = 0.08

        # Regime filter: SMA200 on SPY
        self.spy_sma_ind = self.SMA(self.symbols["SPY"], 200, Resolution.DAILY)
        # Per-asset momentum SMA50
        self.sma50_ind = {}
        for ticker, sym in self.symbols.items():
            self.sma50_ind[ticker] = self.SMA(sym, 50, Resolution.DAILY)

        self.day_count = 0

        self._regime_filter = self.mode != "noregime"
        self._closes = 0

        # Rebalance weekly
        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.after_market_open(self.symbols["SPY"], 30),
            self.rebalance,
        )

        # Trace journaliere `shadow` (contrat #18923) : valeur du portefeuille a
        # l'ouverture de chaque seance de SPY, repartie sur e0..e4. Tous les modes
        # la prennent au meme instant.
        self.schedule.on(
            self.date_rules.every_day(self.symbols["SPY"]),
            self.time_rules.after_market_open(self.symbols["SPY"], 0),
            self._trace,
        )

        if self.mode in ("strategy", "noregime"):
            self.set_warm_up(250, Resolution.DAILY)

    def _trace(self):
        self.plot("shadow", f"e{self._closes % 5}", self.portfolio.total_portfolio_value)
        self._closes += 1

    def _rebalance_reference(self):
        if self.mode == "spy":
            self.set_holdings([PortfolioTarget(self.symbols["SPY"], 1.0)])
        elif self.mode == "6040":
            self.set_holdings([
                PortfolioTarget(self.symbols["SPY"], 0.6),
                PortfolioTarget(self.symbols["BND"], 0.4),
            ])
        else:
            weight = 1.0 / len(self.tickers)
            self.set_holdings([
                PortfolioTarget(self.symbols[ticker], weight)
                for ticker in self.tickers
            ])

    def on_data(self, data: Slice):
        for ticker, sym in self.symbols.items():
            # Mode 6040 : BND est abonne mais hors de self.tickers (univers de
            # la strategie) ; les dictionnaires d'etat ne portent que les
            # tickers de l'univers. En mode strategy/noregime/ew6, abonnes =
            # universe et ce garde ne change rien.
            if ticker not in self.returns:
                continue
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
                    r = np.log(curr / prev)
                    self.returns[ticker].append(r)
                    self.daily_rv[ticker].append(r ** 2)
        self.day_count += 1

    def rebalance(self):
        if self.mode in ("spy", "6040", "ew6"):
            self._rebalance_reference()
            return
        if self.is_warming_up:
            return
        if not self.spy_sma_ind.IsReady:
            return

        # Regime filter (desactive en mode noregime)
        spy_price = float(self.securities[self.symbols["SPY"]].price)
        spy_sma_val = float(self.spy_sma_ind.Current.Value)
        if self._regime_filter:
            regime_mult = 1.0 if spy_price > spy_sma_val else 0.5
        else:
            regime_mult = 1.0

        weights = {}
        for ticker in self.tickers:
            sym = self.symbols[ticker]
            if len(self.returns[ticker]) < self.train_window:
                continue
            if not self.sma50_ind[ticker].IsReady:
                continue

            garch_var = self._garch_forecast(ticker)
            har_var = self._har_forecast(ticker)

            var_forecast = None
            if garch_var is not None and har_var is not None:
                var_forecast = max(garch_var, har_var)
            elif garch_var is not None:
                var_forecast = garch_var
            elif har_var is not None:
                var_forecast = har_var

            if var_forecast is None or var_forecast <= 0:
                continue

            vol_ann = np.sqrt(var_forecast * 252)

            # Direction: price > SMA50
            price = float(self.securities[sym].price)
            direction = 1.0 if price > float(self.sma50_ind[ticker].Current.Value) else 0.0

            if vol_ann > 0.01:
                w = (self.vol_target_ann / vol_ann) * direction * regime_mult
                w = min(w, 0.25)
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

    # ---- GARCH(1,1) ----
    def _garch_forecast(self, ticker):
        rets = np.array(self.returns[ticker])[-self.train_window:]
        if len(rets) < self.train_window:
            return None

        should_refit = (self.day_count - self.last_fit_day[ticker]) >= self.refit_freq

        if should_refit or self.cond_var[ticker] is None:
            params = self._fit_garch_vt(rets)
            if params is not None:
                self.garch_params[ticker] = params
                self.last_fit_day[ticker] = self.day_count
            omega, alpha, beta = self.garch_params[ticker]
            var_s = self._cond_var_series(rets, omega, alpha, beta)
            if var_s is None:
                return None
            self.cond_var[ticker] = float(var_s[-1])
        else:
            omega, alpha, beta = self.garch_params[ticker]
            self.cond_var[ticker] = omega + alpha * float(rets[-1]) ** 2 + beta * self.cond_var[ticker]

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
                ll = self._garch_ll(rets, omega, alpha, beta)
                if ll > best_ll:
                    best_ll = ll
                    best = (omega, alpha, beta)
        return best

    def _garch_ll(self, rets, omega, alpha, beta):
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

    # ---- HAR(1,5,22) ----
    def _har_forecast(self, ticker):
        rv = np.array(self.daily_rv[ticker])[-self.train_window:]
        if len(rv) < self.train_window:
            return None

        should_refit = (self.day_count - self.last_fit_day[ticker]) >= self.refit_freq
        if should_refit or self.har_coefs[ticker] is None:
            coefs = self._fit_har(rv)
            if coefs is not None:
                self.har_coefs[ticker] = coefs

        if self.har_coefs[ticker] is None:
            return None

        log_rv = np.log(np.maximum(rv, 1e-12))
        rv_d = log_rv[-1]
        rv_w = float(np.mean(log_rv[-5:])) if len(log_rv) >= 5 else rv_d
        rv_m = float(np.mean(log_rv[-22:])) if len(log_rv) >= 22 else rv_w

        b0, bd, bw, bm = self.har_coefs[ticker]
        return np.exp(b0 + bd * rv_d + bw * rv_w + bm * rv_m)

    def _fit_har(self, rv):
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
            X.append([1.0, rv_d, rv_w, rv_m])
        if len(y) < 30:
            return None
        try:
            coefs, _, _, _ = np.linalg.lstsq(np.array(X), np.array(y), rcond=None)
            return tuple(coefs)
        except Exception:
            return None
