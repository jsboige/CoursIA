# region imports
from AlgorithmImports import *
# endregion
import numpy as np
from collections import deque
from datetime import date

# Noyau de risque deterministe (#24698), parametre `kernel` : (plafond, stop, coupe-circuit).
# `off` (defaut) laisse le code inchange.
KERNEL_MODES = {"off": (False, False, False), "cap90": (True, False, False),
                "kernel_nocb": (True, True, False), "kernel": (True, True, True)}
KERNEL_EXPOSURE_CAP = 0.90    # exposition brute maximale, sans levier
KERNEL_STOP_ATR = 2.0         # stop a 2 ATR(14) sous le prix de l'ordre, ligne par ligne
KERNEL_CB_THRESHOLD = -0.03   # coupe-circuit apres une seance a -3 % ou pire

# Mesure ligue (#26329, protocole #21594) : parametre `mode`.
# `strategy` (defaut) = code inchange (chemin d'origine, ordre pour ordre) ;
# `naivevol` = meme code, prevision HAR remplacee par exp(moyenne des log RV des
# 22 dernieres seances) ; `spy` / `6040` / `ew6` = references detenues,
# reequilibrees le meme lundi. Passe continue 2015-01-01 -> 2026-07-01 :
# chart `shadow` (e0..e4) pour les seances d'avant 2025-01-01 (fenetre F1),
# chart `shadow2` (e0..e4) pour les suivantes (fenetre F2), chaque compteur
# repartant de e0. Le noyau `kernel` ne s'applique qu'au chemin strategie.
MODES = ("strategy", "naivevol", "spy", "6040", "ew6")
F1_END = date(2025, 1, 1)


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

    Measurement modes (#26329): `mode=naivevol` swaps the HAR forecast for
    exp(mean of last 22 log RV); `mode=spy|6040|ew6` are held references
    rebalanced on the same Mondays (6040 adds BND to the universe).
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 7, 1)
        self.set_cash(100000)

        self.set_brokerage_model(
            BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN
        )

        self.tickers = ["SPY", "EFA", "EEM", "TLT", "GLD", "DBC"]
        self.symbols = {}
        for ticker in self.tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.symbols[ticker] = equity.symbol
        if self.get_parameter("mode", "strategy") == "6040":
            self.symbols["BND"] = self.add_equity("BND", Resolution.DAILY).symbol

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

        # --- Mesure ligue (#26329) -------------------------------------------
        self.mode = self.get_parameter("mode", "strategy")
        if self.mode not in MODES:
            raise ValueError(f"unknown mode {self.mode}")
        self.shadow_bars = 0
        self.shadow2_bars = 0
        # Proprietes publiees avec le verdict (protocole #26329).
        self.n_rebalances = 0          # lundis passes avec au moins un poids
        self.n_renormalized = 0        # reequilibrages renormalises (total > 1)
        self.n_weights = 0             # poids non nuls emis
        self.n_capped = 0              # poids bornes a 0,30 avant renormalisation
        self.first_rebalance = None    # date du premier reequilibrage effectif
        self.n_fills = 0               # ordres remplis (mode strategie)
        self.fill_lag_sum = 0.0        # somme envoye -> remplacement, secondes

        # --- Noyau de risque deterministe (#24698) ---------------------------
        self.kernel = self.get_parameter("kernel", "off")
        if self.kernel not in KERNEL_MODES:
            raise ValueError(f"unknown kernel {self.kernel}")
        self.use_cap, self.use_stop, self.use_cb = KERNEL_MODES[self.kernel]
        self.k_targets = {}
        self.k_stopped = {t: False for t in self.tickers}
        self.k_stop_ticket = {t: None for t in self.tickers}
        self.k_stop_level = {t: None for t in self.tickers}
        self.k_cb_pending = False
        self.k_reentry = False
        self.k_prev_value = None
        self.k_stops = 0
        self.k_cuts = 0
        self.k_invalid = 0
        self.k_exposure_max = 0.0
        self.k_sessions = 0
        self.k_flat_sessions = 0
        if self.use_stop:
            self.k_atr = {t: self.atr(self.symbols[t], 14, MovingAverageType.SIMPLE,
                                      Resolution.DAILY) for t in self.tickers}
        if self.use_cb:
            # Enregistre apres `rebalance` : le lundi, le rebalancement passe d'abord.
            self.schedule.on(
                self.date_rules.every_day(self.symbols["SPY"]),
                self.time_rules.after_market_open(self.symbols["SPY"], 30),
                self._kernel_daily,
            )

    def on_data(self, data: Slice):
        for ticker, sym in self.symbols.items():
            if ticker == "BND":
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
                    self.daily_rv[ticker].append(r ** 2)
                    self.daily_ret[ticker].append(r)
        self.day_count += 1
        if not self.is_warming_up and data.bars.contains_key(self.symbols["SPY"]):
            # Trace en ombre (#18923) : une cloture par seance, seance k dans e{k % 5}.
            # Fenetres F1/F2 (#26329) : shadow avant 2025-01-01, shadow2 ensuite.
            if self.time.date() < F1_END:
                self.plot("shadow", f"e{self.shadow_bars % 5}",
                          self.portfolio.total_portfolio_value)
                self.shadow_bars += 1
            else:
                self.plot("shadow2", f"e{self.shadow2_bars % 5}",
                          self.portfolio.total_portfolio_value)
                self.shadow2_bars += 1
            self._kernel_close()

    def rebalance(self):
        # --- References detenues (#26329) : reequilibrees le meme lundi, ------
        # sans porte d'estimation : detenues des le premier lundi trace.
        if self.mode == "spy":
            weights = {"SPY": 1.0}
        elif self.mode == "6040":
            weights = {"SPY": 0.6, "BND": 0.4}
        elif self.mode == "ew6":
            weights = {t: 1.0 / 6.0 for t in self.tickers}
        else:
            weights = None

        if weights is not None:
            for ticker, w in weights.items():
                self.set_holdings(self.symbols[ticker], w)
            return

        if self.is_warming_up:
            return

        weights = {}
        for ticker in self.tickers:
            sym = self.symbols[ticker]
            if len(self.daily_rv[ticker]) < self.train_window:
                continue

            if self.mode == "naivevol":
                rv = np.array(self.daily_rv[ticker])
                var_forecast = float(np.exp(np.mean(
                    np.log(np.maximum(rv[-22:], 1e-12))))) if len(rv) >= 22 else None
            else:
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
                if kelly_adj > 0.30 and direction > 0:
                    self.n_capped += 1
                if w > 0:
                    self.n_weights += 1
            else:
                w = 0.0
            weights[ticker] = w

        total = sum(weights.values())
        if weights:
            self.n_rebalances += 1
            if self.first_rebalance is None:
                self.first_rebalance = self.time.date()
            if total > 1.0:
                self.n_renormalized += 1
        if total > 1.0:
            weights = {t: w / total for t, w in weights.items()}

        if self.use_cap:
            gross = sum(weights.values())
            if gross > KERNEL_EXPOSURE_CAP:
                weights = {t: w * KERNEL_EXPOSURE_CAP / gross for t, w in weights.items()}

        if self.use_stop or self.use_cb:
            # Le lundi rouvre les lignes stoppees la semaine precedente.
            self.k_stopped = {t: False for t in self.tickers}
            self.k_targets = weights
            if self.k_cb_pending or self.k_reentry:
                return
            self._kernel_enter(weights)
            return

        for ticker in self.tickers:
            sym = self.symbols[ticker]
            w = weights.get(ticker, 0.0)
            if w > 0.001:
                self.set_holdings(sym, w)
            else:
                self.liquidate(sym)

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

    # --- Noyau de risque deterministe (#24698) -------------------------------

    def _kernel_close(self):
        """Cloture de la seance : exposition relevee, puis coupe-circuit a -3 %."""
        value = self.portfolio.total_portfolio_value
        held = sum(abs(self.portfolio[s].holdings_value) for s in self.symbols.values())
        self.k_sessions += 1
        if held <= 0:
            self.k_flat_sessions += 1
        if value > 0:
            self.k_exposure_max = max(self.k_exposure_max, held / value)
        if (self.use_cb and held > 0 and not self.k_cb_pending
                and self.k_prev_value is not None
                and value / self.k_prev_value - 1 <= KERNEL_CB_THRESHOLD):
            for ticker, sym in self.symbols.items():
                self._kernel_cancel_stop(ticker)
                quantity = self.portfolio[sym].quantity
                if quantity != 0:
                    self.market_on_open_order(sym, -quantity, tag="coupe-circuit")
            self.k_cb_pending = True
            self.k_cuts += 1
        self.k_prev_value = value

    def _kernel_daily(self):
        """30 min apres l'ouverture : seance a plat apres une coupure, puis re-entree."""
        if self.is_warming_up:
            return
        if self.k_cb_pending:
            self.k_cb_pending = False
            self.k_reentry = True
            return
        if self.k_reentry:
            self.k_reentry = False
            if self.k_targets:
                self._kernel_enter(self.k_targets)

    def _kernel_enter(self, weights):
        for ticker in self.tickers:
            sym = self.symbols[ticker]
            w = 0.0 if self.k_stopped[ticker] else weights.get(ticker, 0.0)
            if w > 0.001:
                if self.use_stop:
                    self._kernel_cancel_stop(ticker)
                    atr = self.k_atr[ticker]
                    self.k_stop_level[ticker] = (
                        self.securities[sym].price - KERNEL_STOP_ATR * atr.current.value
                        if atr.is_ready else None)
                self.set_holdings(sym, w, tag="rebalancement")
                self._kernel_place_stop(ticker)
            else:
                self._kernel_cancel_stop(ticker)
                self.liquidate(sym)

    def _kernel_live_stop(self, ticker):
        ticket = self.k_stop_ticket[ticker]
        if ticket is None:
            return None
        if ticket.status in (OrderStatus.FILLED, OrderStatus.CANCELED, OrderStatus.INVALID):
            self.k_stop_ticket[ticker] = None
            return None
        return ticket

    def _kernel_place_stop(self, ticker):
        """Stop de la ligne a sa quantite courante (cree, ou mis a jour)."""
        sym = self.symbols[ticker]
        quantity = self.portfolio[sym].quantity
        level = self.k_stop_level[ticker]
        if not self.use_stop or quantity <= 0 or level is None or level <= 0:
            self._kernel_cancel_stop(ticker)
            return
        ticket = self._kernel_live_stop(ticker)
        if ticket is not None:
            if ticket.quantity != -quantity:
                fields = UpdateOrderFields()
                fields.quantity = -quantity
                ticket.update(fields)
            return
        self.k_stop_ticket[ticker] = self.stop_market_order(sym, -quantity, level, tag="stop")

    def _kernel_cancel_stop(self, ticker):
        ticket = self._kernel_live_stop(ticker)
        if ticket is not None:
            ticket.cancel()
        self.k_stop_ticket[ticker] = None

    def on_order_event(self, order_event):
        # Propriete #20264 : delai envoye -> remplacement (observation pure,
        # gardee : un attribut absent de l'API n'arrete jamais le run).
        if order_event.status == OrderStatus.FILLED:
            try:
                order = self.transactions.get_order_by_id(order_event.order_id)
                lag = (order_event.utc_time - order.time).total_seconds()
                if lag >= 0:
                    self.n_fills += 1
                    self.fill_lag_sum += lag
            except AttributeError:
                pass
        if self.kernel == "off":
            return
        if order_event.status == OrderStatus.INVALID:
            self.k_invalid += 1
            return
        if order_event.status != OrderStatus.FILLED:
            return
        ticker = order_event.symbol.value
        if ticker not in self.k_stopped:
            return
        order = self.transactions.get_order_by_id(order_event.order_id)
        if order.type == OrderType.STOP_MARKET:
            self.k_stopped[ticker] = True
            self.k_stops += 1
            self.k_stop_ticket[ticker] = None
        elif order.tag == "rebalancement":
            self._kernel_place_stop(ticker)

    def on_end_of_algorithm(self):
        self.set_runtime_statistic("Mode", self.mode)
        self.set_runtime_statistic("Noyau", self.kernel)
        self.set_runtime_statistic("Stops", str(self.k_stops))
        self.set_runtime_statistic("Coupures", str(self.k_cuts))
        self.set_runtime_statistic("Ordres invalides", str(self.k_invalid))
        self.set_runtime_statistic("Exposition max", f"{self.k_exposure_max:.4f}")
        self.set_runtime_statistic(
            "Seances a plat", f"{self.k_flat_sessions}/{self.k_sessions}")
        if self.n_rebalances:
            self.set_runtime_statistic(
                "Poids bornes 0,30", f"{self.n_capped}/{self.n_weights}")
            self.set_runtime_statistic(
                "Renormalisations", f"{self.n_renormalized}/{self.n_rebalances}")
            self.set_runtime_statistic(
                "Premier reequilibrage", str(self.first_rebalance))
        if self.n_fills:
            self.set_runtime_statistic(
                "Remplissage moyen (s)", f"{self.fill_lag_sum / self.n_fills:.1f}")
