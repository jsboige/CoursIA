# region imports
from AlgorithmImports import *
# endregion
import numpy as np
from collections import deque


class GarchVolTargetAlgorithm(QCAlgorithm):
    """GARCH(1,1) volatility targeting on a multi-asset portfolio.

    Forecasts next-day variance using a rolling GARCH(1,1) model fitted
    via variance-targeting MLE, then sizes each position inversely
    proportional to its forecasted volatility so that each asset
    contributes equally to portfolio risk.

    No directional prediction -- pure risk budgeting. Uses SMA200 trend
    filter for direction (long only, no shorts).

    Assets: SPY, EFA, EEM, TLT, GLD, DBC (AQR-style multi-asset).
    Backtest: 2018-01-01 -> 2025-01-01 par defaut (parametres start_date / end_date, %Y%m%d)

    Parametre mode (#21778) :
    - strategy (defaut) : la strategie ci-dessus ;
    - spy : SPY detenu ;
    - 6040 : SPY 60 %, BND 40 % ;
    - rv21 : la strategie, avec pour seule difference la variance des 21 derniers
      rendements journaliers a la place de la prevision GARCH.
    Les references spy et 6040 se reequilibrent au debut de chaque mois, une minute apres
    l'ouverture ; dans ces deux modes, rebalance() sort aussitot. Trace journaliere "shadow"
    (e0..e4, #18923) : valeur du portefeuille a l'ouverture de chaque seance de SPY.
    """

    def initialize(self):
        self._mode = self.get_parameter("mode", "strategy").lower()
        if self._mode not in ("strategy", "spy", "6040", "rv21"):
            raise ValueError(f"unknown mode parameter: {self._mode} (strategy | spy | 6040 | rv21)")
        start_date_param = self._parse_date_param("start_date")
        end_date_param = self._parse_date_param("end_date")
        if start_date_param is not None:
            self.set_start_date(start_date_param)
        else:
            self.set_start_date(2018, 1, 1)
        if end_date_param is not None:
            self.set_end_date(end_date_param)
        else:
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
        # #21782 : nombre de rendements jamais recus, et nombre deja replies dans
        # cond_var. Les deux compteurs sont absolus : la fenetre glissante du deque
        # ne permet pas d'indexer un rendement de facon stable.
        self.return_count = {t: 0 for t in self.tickers}
        self.folded_count = {t: 0 for t in self.tickers}

        self.day_count = 0

        # Rebalance weekly (Monday)
        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.after_market_open(self.symbols["SPY"], 30),
            self.rebalance,
        )

        self.set_warm_up(250, Resolution.DAILY)

        # Mesure #21778 : references detenues et trace journaliere, hors decision de la strategie
        spy = self.symbols["SPY"]
        self._bnd = (self.add_equity("BND", Resolution.DAILY).symbol
                     if self._mode == "6040" else None)
        if self._mode in ("spy", "6040"):
            self.settings.seed_initial_prices = True
            self.schedule.on(
                self.date_rules.month_start(spy),
                self.time_rules.after_market_open(spy, 1),
                self._rebalance_reference,
            )
        self._closes = 0
        self.schedule.on(
            self.date_rules.every_day(spy),
            self.time_rules.after_market_open(spy, 0),
            self._trace,
        )

    def _parse_date_param(self, name):
        raw = self.get_parameter(name)
        if raw is None or str(raw).strip() == "":
            return None
        return datetime.strptime(str(raw).strip(), "%Y%m%d")

    def _rebalance_reference(self):
        if self.is_warming_up:
            return
        if self._mode == "spy":
            self.set_holdings([PortfolioTarget(self.symbols["SPY"], 1.0)])
        else:
            self.set_holdings([PortfolioTarget(self.symbols["SPY"], 0.6),
                               PortfolioTarget(self._bnd, 0.4)])

    def _trace(self):
        if self.is_warming_up:
            return
        self.plot("shadow", f"e{self._closes % 5}", self.portfolio.total_portfolio_value)
        self._closes += 1

    def on_data(self, data: Slice):
        for ticker, sym in self.symbols.items():
            if not data.ContainsKey(sym):
                continue
            bar = data[sym]
            if bar is None:
                continue
            log_return = self._daily_log_return(ticker, bar)
            if log_return is not None:
                self.returns[ticker].append(log_return)
                self.return_count[ticker] += 1
        self.day_count += 1

    def _daily_log_return(self, ticker, bar):
        """Rendement journalier dont la paire de clotures est verifiee (#21782).

        `history(sym, 2 * 3, DAILY)` inclut ou non la seance courante selon
        l'heure de l'appel, et rend moins de barres que demandees sur une
        demi-seance (#21471) : demander 3 avec une garde a 2 ne laissait qu'une
        barre de marge, sous le raccourcissement mesure (21). On demande le
        double puis on re-slice sur les 3 dernieres barres (motif #20286) :
        hors demi-seance la paire retenue est celle d'avant, la paire reste
        calculable sur demi-seance. Prendre `iloc[-2]` sans verifier peut
        former une paire a deux seances comptee comme un pas journalier, ou
        une paire desalignee avec `bar.close`. On aligne donc la paire sur
        `bar.end_time`, et on rejette un ecart calendaire qui trahit une
        suspension : mieux vaut aucun rendement qu'un faux pas de GARCH.
        """
        hist = self.history(self.symbols[ticker], 2 * 3, Resolution.DAILY)
        if hist is None or len(hist) < 2:
            return None
        hist = hist.iloc[-3:]
        closes = hist["close"]
        # Un historique LEAN porte parfois un MultiIndex (symbole, horodatage) :
        # `list(hist.index)` rend alors des tuples, pas des dates. On prend le
        # dernier niveau, qui est l'horodatage dans les deux formes.
        idx = hist.index
        levels = getattr(idx, "nlevels", 1)
        times = list(idx.get_level_values(-1) if levels > 1 else idx)
        if times[-1] >= bar.end_time:
            curr_close, curr_time = float(closes.iloc[-1]), times[-1]
            prev_close, prev_time = float(closes.iloc[-2]), times[-2]
        else:
            curr_close, curr_time = float(bar.close), bar.end_time
            prev_close, prev_time = float(closes.iloc[-1]), times[-1]
        # `nan <= 0` est faux : une cloture non finie traverserait le test de
        # positivite ci-dessous et entrerait dans la fenetre glissante, d'ou elle
        # ne ressortirait que 550 seances plus tard. Sur 2023-11 -> 2026-07 ce
        # garde-fou n'a rien rejete (mesure : 0 rejet non fini et 0 rejet non
        # positif sur 129 rebalances) ; il retient un cas que ces donnees ne
        # presentent pas, et ne change donc pas le resultat mesure.
        if not (np.isfinite(prev_close) and np.isfinite(curr_close)):
            return None
        if prev_close <= 0 or curr_close <= 0:
            return None
        gap = (curr_time - prev_time).days
        if gap <= 0 or gap > 4:
            return None
        log_return = float(np.log(curr_close / prev_close))
        if not np.isfinite(log_return):
            return None
        return log_return

    def rebalance(self):
        if self.is_warming_up or self._mode in ("spy", "6040"):
            return

        weights = {}
        for ticker in self.tickers:
            sym = self.symbols[ticker]
            if len(self.returns[ticker]) < self.train_window:
                continue
            if not self.sma_ind[ticker].IsReady:
                continue

            if self._mode == "rv21":
                var_forecast = float(np.var(np.array(self.returns[ticker])[-21:]))
            else:
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

        # Invariant de `cond_var` : c'est la prevision de variance du **prochain**
        # rendement non observe (v_{T+1} apres avoir observe r_T). Une prevision
        # s'applique donc une seule fois, et entre deux re-estimations la variance
        # avance d'un pas par rendement recu -- c'est le defaut corrige en #21782 :
        # l'ancien code repliait seulement le dernier rendement (deja compte dans la
        # prevision precedente) et ignorait les quatre autres.
        if should_refit or self.cond_var[ticker] is None:
            params = self._fit_garch_vt(rets)
            if params is not None:
                self.garch_params[ticker] = params
                self.last_fit_day[ticker] = self.day_count
            omega, alpha, beta = self.garch_params[ticker]
            var_series = self._cond_var_series(rets, omega, alpha, beta)
            if var_series is None:
                return None
            # var_series[-1] = v_T (variance du dernier rendement, qui ne l'incorpore
            # pas encore) : la prevision du lendemain est v_{T+1}.
            self.cond_var[ticker] = (
                omega + alpha * float(rets[-1]) ** 2 + beta * float(var_series[-1])
            )
            self.folded_count[ticker] = self.return_count[ticker]
            return self.cond_var[ticker] if np.isfinite(self.cond_var[ticker]) else None

        omega, alpha, beta = self.garch_params[ticker]
        pending = self.return_count[ticker] - self.folded_count[ticker]
        if pending > 0:
            new_returns = list(self.returns[ticker])[-pending:]
            for r in new_returns:
                self.cond_var[ticker] = (
                    omega + alpha * float(r) ** 2 + beta * self.cond_var[ticker]
                )
            self.folded_count[ticker] = self.return_count[ticker]
        if not np.isfinite(self.cond_var[ticker]):
            return None
        return self.cond_var[ticker]

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
