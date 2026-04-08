# region imports
from AlgorithmImports import *
import numpy as np
import pandas as pd
from scipy.optimize import minimize
# endregion


class BlackLittermanMomentum(QCAlgorithm):
    """
    Black-Litterman Portfolio with Multi-Window Momentum Views.

    Combines market equilibrium (CAPM implied returns) with momentum-based
    investor views using the Black-Litterman framework. Key innovations from
    ECE student projects (4 groups, Tour/Monteiro, ilhan/Farhan):

    - He & Litterman Omega calibration: view uncertainty proportional to
      asset covariance (no arbitrary diagonal)
    - Multi-window momentum views with sigmoid confidence: 1m/3m/6m/12m
      momentum signals, higher agreement = higher confidence
    - Sector concentration constraints: max 30% per sector
    - Ledoit-Wolf covariance estimation (shrinkage regularized)

    Source: ECE student project (4 groups, Gr01/Gr02/Gr03), adapted for
    ESGF pool. Issue #238 - Integrate ECE student concepts into QC strategies.

    Universe: 15 Large-Caps US (5 sectors, same as Portfolio-Optimization-ML)
    Benchmark: Portfolio-Optimization-ML (Sharpe 0.896)
    """

    UNIVERSE = {
        "AAPL": "Technology", "MSFT": "Technology", "NVDA": "Technology",
        "JPM": "Financials", "BAC": "Financials", "WFC": "Financials",
        "JNJ": "Healthcare", "UNH": "Healthcare", "PFE": "Healthcare",
        "AMZN": "Consumer", "TSLA": "Consumer", "MCD": "Consumer",
        "CAT": "Industrials", "HON": "Industrials", "UNP": "Industrials",
    }

    SECTOR_MAX = 0.30  # Max 30% per sector
    TAU = 0.05         # BL scaling parameter (He & Litterman)
    RISK_FREE = 0.02   # Risk-free rate approximation
    DELTA = 2.5        # Risk aversion coefficient

    # Momentum view windows (trading days)
    MOM_WINDOWS = [21, 63, 126, 252]  # 1m, 3m, 6m, 12m

    # Confidence sigmoid parameters
    SIGMOID_STEEPNESS = 5.0
    AGREEMENT_THRESHOLD = 0.5  # Minimum agreement to form a view

    # Portfolio constraints
    MIN_WEIGHT = 0.01
    MAX_WEIGHT = 0.20
    TARGET_VOL = 0.15

    COV_LOOKBACK = 60  # Days for covariance estimation

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 1, 1)
        self.set_cash(100_000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # Add universe
        self.symbols = []
        self.tickers = list(self.UNIVERSE.keys())
        self.sector_map = {}

        for ticker in self.tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.symbols.append(equity.symbol)
            self.sector_map[equity.symbol] = self.UNIVERSE[ticker]

        # Benchmark
        spy = self.add_equity("SPY", Resolution.DAILY)
        self.set_benchmark(spy.symbol)

        # Monthly rebalance
        self.schedule.on(
            self.date_rules.month_start("SPY", 1),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance
        )

        self.set_warmup(260, Resolution.DAILY)

    def _get_market_cap_weights(self):
        """
        Estimate market-cap proxy weights from price * avg volume.

        Used as the 'equilibrium' prior in Black-Litterman. In absence of
        actual market cap data in QC LEAN, we use price * volume as proxy.
        """
        history = self.history(self.symbols, 20, Resolution.DAILY)
        if history.empty:
            return None

        try:
            volumes = history["volume"].groupby(level=0).mean()
            closes = history["close"].groupby(level=0).last()
            caps = closes * volumes
            total = caps.sum()
            if total == 0:
                return None
            weights = caps / total
            return weights
        except Exception:
            return None

    def _estimate_covariance(self):
        """Ledoit-Wolf shrinkage covariance (pure numpy implementation)."""
        history = self.history(self.symbols, self.COV_LOOKBACK, Resolution.DAILY)
        if history.empty:
            return None

        try:
            prices = history["close"].unstack(level=0)
            returns = prices.pct_change().dropna()
            if len(returns) < 20:
                return None

            X = returns.values
            n, p = X.shape
            mean = X.mean(axis=0)
            Xc = X - mean

            # Sample covariance (annualized)
            sample_cov = (Xc.T @ Xc) / (n - 1) * 252

            # Ledoit-Wolf shrinkage target: scaled identity
            trace_s = np.trace(sample_cov)
            target = (trace_s / p) * np.eye(p)

            # Optimal shrinkage intensity (Ledoit-Wolf 2004 simplified)
            sum_sq_s = np.sum(sample_cov ** 2)
            sum_sq_target = np.sum(target ** 2)
            cross = np.sum(sample_cov * target)

            # Pi-hat: sum of asymptotic variances
            y2 = Xc ** 2
            phi_mat = (y2.T @ y2) / n - sample_cov ** 2
            pi_hat = np.sum(phi_mat)

            # Gamma-hat
            gamma = sum_sq_s + sum_sq_target - 2 * cross

            # Shrinkage intensity
            kappa = (pi_hat / gamma) if gamma > 0 else 1.0
            shrinkage = max(0, min(1, kappa / n))

            shrunk = shrinkage * target + (1 - shrinkage) * sample_cov

            return pd.DataFrame(
                shrunk, index=returns.columns, columns=returns.columns
            )
        except Exception:
            return None

    def _compute_momentum_views(self):
        """
        Multi-window momentum views with sigmoid confidence.

        For each asset, compute momentum over 1m/3m/6m/12m windows.
        Agreement = fraction of windows with same sign.
        Confidence = sigmoid(agreement) mapping to [0, 1].

        Returns:
            views: dict {symbol_id: (expected_return, confidence)}
        """
        views = {}
        longest = max(self.MOM_WINDOWS) + 5

        for symbol in self.symbols:
            history = self.history(symbol, longest, Resolution.DAILY)
            if history.empty or len(history) < max(self.MOM_WINDOWS):
                continue

            prices = history["close"].values
            mom_signals = []

            for window in self.MOM_WINDOWS:
                if len(prices) >= window:
                    ret = prices[-1] / prices[-window] - 1
                    annualized = ret * (252 / window)
                    mom_signals.append(annualized)
                else:
                    mom_signals.append(0.0)

            if not mom_signals:
                continue

            # Agreement: fraction of signals with same sign as median
            median_signal = np.median(mom_signals)
            signs = [np.sign(s) == np.sign(median_signal) for s in mom_signals]
            agreement = sum(signs) / len(signs)

            if agreement < self.AGREEMENT_THRESHOLD:
                continue  # Skip uncertain assets

            # Expected return: weighted average (more weight to shorter windows)
            weights = np.array([4, 3, 2, 1][:len(mom_signals)])
            weights = weights / weights.sum()
            expected_return = np.dot(weights, mom_signals)

            # Confidence via sigmoid
            x = agreement - 0.5  # Center at 0.5 agreement
            confidence = 1.0 / (1.0 + np.exp(-self.SIGMOID_STEEPNESS * x))

            views[symbol] = (expected_return, confidence)

        return views

    def _black_litterman(self, pi, sigma, views, market_weights):
        """
        Black-Litterman posterior expected returns.

        Uses He & Litterman (1999) Omega calibration:
            omega = diag(P @ (tau * Sigma) @ P') * scalar

        Parameters:
            pi: implied equilibrium returns (Series, indexed by symbol ID)
            sigma: covariance matrix (DataFrame)
            views: dict {symbol_id: (expected_return, confidence)}
            market_weights: Series of market cap weights

        Returns:
            posterior_returns: Series of BL posterior returns
        """
        n = len(pi)
        tau_sigma = self.TAU * sigma.values

        if not views:
            return pi

        # Build view matrices
        view_symbols = list(views.keys())
        k = len(view_symbols)
        p = np.zeros((k, n))
        q = np.zeros(k)
        omega_diag = np.zeros(k)

        pi_values = pi.values

        for i, sym_id in enumerate(view_symbols):
            # Find index in pi
            try:
                idx = list(pi.index).index(sym_id)
            except ValueError:
                continue

            p[i, idx] = 1.0  # Absolute view on single asset
            q[i] = views[sym_id][0]

            # He & Litterman Omega: proportional to covariance
            confidence = views[sym_id][1]
            omega_diag[i] = (p[i] @ tau_sigma @ p[i]) / max(confidence, 0.1)

        omega = np.diag(omega_diag)

        try:
            # BL posterior: mu_BL = [(tau*Sigma)^-1 + P'*Omega^-1*P]^-1
            #               * [(tau*Sigma)^-1 * pi + P'*Omega^-1*Q]
            tau_sigma_inv = np.linalg.inv(tau_sigma)
            omega_inv = np.linalg.inv(omega)

            m1 = tau_sigma_inv + p.T @ omega_inv @ p
            m2 = tau_sigma_inv @ pi_values + p.T @ omega_inv @ q

            posterior = np.linalg.solve(m1, m2)
            return pd.Series(posterior, index=pi.index)
        except np.linalg.LinAlgError:
            return pi

    def _implied_equilibrium_returns(self, market_weights, sigma):
        """
        Compute implied equilibrium returns from CAPM.

        pi = delta * Sigma * w_market

        Parameters:
            market_weights: Series of market cap proxy weights
            sigma: covariance matrix (DataFrame)

        Returns:
            pi: Series of implied returns
        """
        w = market_weights.reindex(sigma.index).fillna(1.0 / len(sigma))
        w = w.values

        pi = self.DELTA * sigma.values @ w
        return pd.Series(pi, index=sigma.index)

    def _optimize_portfolio(self, expected_returns, cov_matrix):
        """
        Mean-variance optimization with sector constraints.

        Maximize Sharpe ratio subject to:
        - Sum(weights) = 1
        - MIN_WEIGHT <= w_i <= MAX_WEIGHT
        - Sector allocation <= SECTOR_MAX
        """
        n = len(expected_returns)
        ids = list(expected_returns.index)

        # Symbol to index mapping for sector constraints
        # expected_returns.index contains Symbol objects (from cov matrix columns)
        sym_from_id = {}
        for s in self.symbols:
            sym_from_id[s] = s

        def negative_sharpe(w):
            ret = np.dot(w, expected_returns.values)
            vol = np.sqrt(w @ cov_matrix.values @ w)
            return -(ret - self.RISK_FREE) / vol if vol > 0 else 0

        constraints = [{"type": "eq", "fun": lambda w: np.sum(w) - 1.0}]

        # Sector constraints: sum of weights in each sector <= SECTOR_MAX
        sectors = {}
        for i, sym_id in enumerate(ids):
            symbol = sym_from_id.get(sym_id)
            if symbol is None:
                continue
            sector = self.sector_map.get(symbol, "Other")
            if sector not in sectors:
                sectors[sector] = []
            sectors[sector].append(i)

        for sector, indices in sectors.items():
            constraints.append({
                "type": "ineq",
                "fun": lambda w, idx=indices: self.SECTOR_MAX - sum(w[j] for j in idx)
            })

        bounds = [(self.MIN_WEIGHT, self.MAX_WEIGHT)] * n
        x0 = np.full(n, 1.0 / n)

        try:
            result = minimize(
                negative_sharpe, x0, method="SLSQP",
                bounds=bounds, constraints=constraints,
                options={"ftol": 1e-9, "maxiter": 500}
            )
            if result.success:
                return pd.Series(result.x, index=ids)
        except Exception:
            pass

        # Fallback: risk parity (inverse volatility)
        vols = np.sqrt(np.diag(cov_matrix.values))
        inv_vol = 1.0 / np.maximum(vols, 1e-8)
        weights = inv_vol / inv_vol.sum()
        return pd.Series(weights, index=ids)

    def _apply_vol_targeting(self, weights, cov_matrix):
        """Scale weights to target portfolio volatility."""
        w = weights.values
        port_vol = np.sqrt(w @ cov_matrix.values @ w)

        if port_vol > 0 and port_vol > self.TARGET_VOL:
            scale = self.TARGET_VOL / port_vol
            scaled = weights * scale
            # Cash remainder
            return scaled
        return weights

    def rebalance(self):
        """Monthly rebalance using Black-Litterman posterior."""
        if self.is_warming_up:
            return

        # 1. Estimate covariance
        cov = self._estimate_covariance()
        if cov is None:
            self.debug("BL: covariance estimation failed")
            return

        # 2. Market cap proxy weights
        mkt_weights = self._get_market_cap_weights()
        if mkt_weights is None:
            mkt_weights = pd.Series(
                [1.0 / len(self.symbols)] * len(self.symbols),
                index=self.symbols
            )

        # Reindex to match covariance matrix
        mkt_weights = mkt_weights.reindex(cov.index).fillna(1.0 / len(cov))

        # 3. Implied equilibrium returns
        pi = self._implied_equilibrium_returns(mkt_weights, cov)

        # 4. Multi-window momentum views
        views = self._compute_momentum_views()

        # 5. Black-Litterman posterior
        posterior = self._black_litterman(pi, cov, views, mkt_weights)

        # Reindex posterior to match cov matrix
        posterior = posterior.reindex(cov.index).fillna(0.0)

        # 6. Optimize with sector constraints
        optimal = self._optimize_portfolio(posterior, cov)

        # 7. Vol targeting
        scaled = self._apply_vol_targeting(optimal, cov)

        # 8. Execute
        self.liquidate()

        # scaled.index contains Symbol objects (from cov matrix columns)
        for symbol, weight in scaled.items():
            if weight > self.MIN_WEIGHT:
                self.set_holdings(symbol, float(weight))

        n_pos = sum(1 for w in scaled.values if w > self.MIN_WEIGHT)
        self.debug(f"BL rebalance: {n_pos} positions, {len(views)} momentum views")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        ret = (final - 100_000) / 100_000
        self.log(f"BlackLitterman-Momentum: Final=${final:,.0f}, Return={ret:.2%}")
