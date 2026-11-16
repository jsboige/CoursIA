# region imports
from AlgorithmImports import *
# endregion
import numpy as np
from collections import deque

from risk_kernel import RiskKernel, check_mode

# Noyau de risque deterministe (#24698), parametre `kernel` : off (defaut, code
# inchange) | cap90 | kernel_nocb | kernel. Le noyau vit dans risk_kernel.py,
# copie identique de projects/RiskKernel/risk_kernel.py.

# League de reference (#26329), parametre `mode` : `strategy` (defaut) = HAR-RV
# Kelly intact ; `spy` / `6040` / `ew6` / `naivevol` = portefeuilles references
# mesures sur le MEME historique, cote a cote, par les organes de la league.
LEAGUE_MODES = ("strategy", "spy", "6040", "ew6", "naivevol")


class HarrvKellyAlgorithm(QCAlgorithm):
    """HAR-RV Kelly 1/4 strategy on a multi-asset portfolio.

    Uses the Heterogeneous Autoregressive (HAR) model of Corsi (2009)
    to forecast 5-day realized variance from daily RV, then applies
    Kelly criterion at 1/4 fraction for position sizing.

    HAR(log RV_{t+5}) = b0 + b_d*log(RV_t) + b_w*mean(log RV_{t-5:t})
                      + b_m*mean(log RV_{t-22:t})

    OLS coefficients refit every 22 days on a rolling 500-day window.
    Direction via 5-day momentum (return sign).

    Assets: SPY, EFA, EEM, TLT, GLD, DBC.

    Optional deterministic risk kernel (#24698), parameter `kernel`:
    `cap90` caps gross exposure at 0.90; `kernel_nocb` adds a stop 2 ATR(14)
    below the order price on each line (a stopped line stays flat until the
    next Monday rebalance); `kernel` adds a circuit breaker (after a session
    at -3 % or worse, liquidate at the next open, re-enter the session after).
    `off` (default) leaves the strategy unchanged.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2025, 1, 1)
        self.set_cash(100000)

        self.set_brokerage_model(
            BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN
        )

        # League de reference (#26329) : `mode` selectionne la strategie ou un
        # portefeuille reference mesure sur le meme historique.
        self.mode = self.get_parameter("mode", "strategy")
        if self.mode not in LEAGUE_MODES:
            raise ValueError(f"unknown mode {self.mode}")

        self.tickers = ["SPY", "EFA", "EEM", "TLT", "GLD", "DBC"]
        if self.mode == "6040":
            # Le 60/40 classique tient 40 % en obligations agregat (AGG) :
            # 7e actif, ajoute seulement pour ce mode de reference.
            self.tickers.append("AGG")
        self.symbols = {}
        for ticker in self.tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = equity.symbol

        self.set_benchmark(self.symbols["SPY"])

        # HAR parameters
        self.train_window = 500
        self.refit_freq = 22
        self.kelly_fraction = 0.25
        self.forecast_horizon = 5

        # Per-asset state
        self.daily_rv = {t: deque(maxlen=self.train_window + 50) for t in self.tickers}
        self.daily_ret = {t: deque(maxlen=50) for t in self.tickers}
        self.har_coefs = {t: None for t in self.tickers}
        self.last_fit_day = {t: -100 for t in self.tickers}

        self.day_count = 0

        # Rebalance weekly
        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.after_market_open(self.symbols["SPY"], 30),
            self.rebalance,
        )

        self.set_warm_up(250, Resolution.DAILY)

        # --- Noyau de risque deterministe (#24698) ---------------------------
        self.kernel = self.get_parameter("kernel", "off")
        check_mode(self.kernel)
        # Un noyau de risque n'a de sens que sur la strategie. Sur un mode de
        # reference, le coupe-circuit liquiderait le portefeuille de reference et
        # la re-entree lirait des cibles vides : la reference resterait a plat
        # jusqu'au lundi suivant. On refuse la combinaison des que les deux sont
        # actives.
        if self.mode != "strategy" and self.kernel != "off":
            raise ValueError(
                f"mode={self.mode!r} est un portefeuille de reference : le "
                f"noyau de risque (kernel={self.kernel!r}) le liquiderait et "
                "le laisserait a plat. Mettre kernel='off' (ou mode='strategy')."
            )
        self.shadow_bars = 0
        # Construit apres `rebalance` : le lundi, le rebalancement passe d'abord.
        self.risk = RiskKernel(self, self.kernel,
                               {t: self.symbols[t] for t in self.tickers},
                               self.symbols["SPY"])

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
                    r = np.log(curr / prev)
                    self.daily_rv[ticker].append(r ** 2)
                    self.daily_ret[ticker].append(r)
        self.day_count += 1
        if not self.is_warming_up and data.bars.contains_key(self.symbols["SPY"]):
            # Trace en ombre (#18923) : une cloture par seance, seance k dans e{k % 5}.
            self.plot("shadow", f"e{self.shadow_bars % 5}",
                      self.portfolio.total_portfolio_value)
            self.shadow_bars += 1
            self.risk.on_close()

    def rebalance(self):
        if self.is_warming_up:
            return

        if self.mode != "strategy":
            self._rebalance_reference()
            return

        weights = {}
        for ticker in self.tickers:
            sym = self.symbols[ticker]
            if len(self.daily_rv[ticker]) < self.train_window:
                continue

            var_forecast = self._har_forecast(ticker)
            if var_forecast is None or var_forecast <= 0:
                continue

            vol_ann = np.sqrt(var_forecast * 252 / self.forecast_horizon)

            # Direction via 5-day momentum
            rets = list(self.daily_ret[ticker])
            if len(rets) < 5:
                continue
            mom_5d = sum(rets[-5:])
            direction = 1.0 if mom_5d > 0 else 0.0

            # Kelly sizing: f = mu / sigma^2, scaled by fraction
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

        weights = self.risk.cap(weights)
        if self.risk.rebalance(weights):
            # Le lundi rouvre les lignes stoppees la semaine precedente.
            return

        for ticker in self.tickers:
            sym = self.symbols[ticker]
            w = weights.get(ticker, 0.0)
            if w > 0.001:
                self.set_holdings(sym, w)
            else:
                self.liquidate(sym)

    # --- League de reference (#26329) ----------------------------------------

    def _rebalance_reference(self):
        """Portefeuilles references de la league : memes donnees et meme
        calendrier que la strategie, sans la logique HAR-RV Kelly. Mesure cote
        a cote sur le meme historique pour le verdict BEATS / NO BEATS."""
        if self.mode == "spy":
            targets = {"SPY": 1.0}
        elif self.mode == "6040":
            targets = {"SPY": 0.60, "AGG": 0.40}
        elif self.mode == "ew6":
            base = [t for t in self.tickers if t != "AGG"]
            targets = {t: 1.0 / len(base) for t in base}
        elif self.mode == "naivevol":
            targets = self._naive_vol_weights()
        else:
            targets = {}

        for ticker in self.tickers:
            sym = self.symbols[ticker]
            w = targets.get(ticker, 0.0)
            if w > 0.001:
                self.set_holdings(sym, w)
            else:
                self.liquidate(sym)

    def _naive_vol_weights(self):
        """Pondération inverse-volatilité naive : w_i ∝ 1/σ_i sur les 6 actifs,
        σ_i = écart-type des logs-retours des 20 derniers jours (collectés dans
        `daily_rv`). Référence de volatilité simple, cote a cote de la strategy."""
        inv = {}
        for ticker in self.tickers:
            if ticker == "AGG":
                continue
            rv = list(self.daily_rv[ticker])[-20:]
            if len(rv) < 5:
                continue
            var = sum(rv) / len(rv)
            vol = np.sqrt(max(var, 1e-12))
            inv[ticker] = 1.0 / vol
        total = sum(inv.values())
        if total <= 0:
            return {}
        return {t: w / total for t, w in inv.items()}

    def _har_forecast(self, ticker):
        rv = np.array(self.daily_rv[ticker])
        n = len(rv)
        if n < self.train_window:
            return None
        rv = rv[-self.train_window:]

        should_refit = (self.day_count - self.last_fit_day[ticker]) >= self.refit_freq

        if should_refit or self.har_coefs[ticker] is None:
            coefs = self._fit_har(rv)
            if coefs is not None:
                self.har_coefs[ticker] = coefs
                self.last_fit_day[ticker] = self.day_count

        if self.har_coefs[ticker] is None:
            return None

        log_rv = np.log(np.maximum(rv, 1e-12))
        rv_d = log_rv[-1]
        rv_w = float(np.mean(log_rv[-5:])) if len(log_rv) >= 5 else rv_d
        rv_m = float(np.mean(log_rv[-22:])) if len(log_rv) >= 22 else rv_w

        b0, bd, bw, bm = self.har_coefs[ticker]
        log_rv_pred = b0 + bd * rv_d + bw * rv_w + bm * rv_m

        hist = list(log_rv)
        for _ in range(self.forecast_horizon - 1):
            tail = hist[-22:]
            d = tail[-1]
            w = float(np.mean(tail[-5:]))
            m = float(np.mean(tail))
            pred = b0 + bd * d + bw * w + bm * m
            hist.append(pred)

        avg_log_rv = float(np.mean(hist[len(log_rv):]))
        return np.exp(avg_log_rv)

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

        X = np.array(X)
        y = np.array(y)
        try:
            coefs, _, _, _ = np.linalg.lstsq(X, y, rcond=None)
            return tuple(coefs)
        except Exception:
            return None

    def on_order_event(self, order_event):
        self.risk.on_order_event(order_event)

    def on_end_of_algorithm(self):
        self.set_runtime_statistic("Mode", self.mode)
        for name, value in self.risk.statistics().items():
            self.set_runtime_statistic(name, value)
