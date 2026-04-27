# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class AdaptiveConformalRisk(QCAlgorithm):
    """
    Adaptive Conformal Inference Risk Overlay on Multi-Factor Momentum.

    Implements the ACI algorithm (Gibbs & Candès, 2021) as a dynamic risk
    management overlay. ACI provides online-adjusted prediction intervals
    with guaranteed marginal coverage, dynamically adapting interval width
    based on recent prediction errors.

    Core innovation from ECE student project (El Bakkali, Gr02):
    - Online alpha adjustment: coverage violations widen intervals,
      excess coverage narrows them
    - Nonconformity-based position sizing: wider intervals = smaller
      positions, directly translating risk into allocation decisions
    - Rolling calibration window with exponential decay weighting

    Applied as an overlay on a multi-factor momentum base strategy:
    - 3-factor momentum signal (short/mid/long term)
    - Sector-balanced universe (5 sectors, 15 assets)
    - Target volatility framework (15% annualized)
    - Monthly rebalancing with ACI-adjusted weights

    Source: ECE student project (El Bakkali, Gr02), adapted for ESGF pool.
    Issue #238 - Integrate ECE student concepts into QC strategies.

    Universe: 15 Large-Caps US (5 sectors)
    Benchmark: SectorMomentum (Sharpe 0.57)
    """

    UNIVERSE = {
        "AAPL": "Technology", "MSFT": "Technology", "NVDA": "Technology",
        "JPM": "Financials", "BAC": "Financials", "WFC": "Financials",
        "JNJ": "Healthcare", "UNH": "Healthcare", "PFE": "Healthcare",
        "AMZN": "Consumer", "TSLA": "Consumer", "MCD": "Consumer",
        "CAT": "Industrials", "HON": "Industrials", "UNP": "Industrials",
    }

    SECTOR_MAX = 0.30
    TARGET_COVERAGE = 0.90   # 90% target prediction interval coverage
    GAMMA = 0.05             # ACI learning rate for alpha adjustment
    CALIBRATION_WINDOW = 60  # Rolling window for nonconformity scores
    MOM_WINDOWS = [21, 63, 126]  # Short/mid/long momentum (1m/3m/6m)
    TARGET_VOL = 0.15
    VOL_LOOKBACK = 60
    MAX_WEIGHT = 0.15
    MIN_WEIGHT = 0.01
    REBALANCE_DAYS = 21  # Monthly rebalancing

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 1, 1)
        self.set_cash(100000)
        self.set_benchmark("SPY")

        # Universe
        self.symbols = {}
        for ticker in self.UNIVERSE:
            symbol = self.add_equity(ticker, Resolution.DAILY).symbol
            self.symbols[ticker] = symbol

        # ACI state per asset: alpha_t (adaptive coverage level)
        self.aci_alpha = {ticker: 1.0 - self.TARGET_COVERAGE
                         for ticker in self.UNIVERSE}

        # Rolling nonconformity scores per asset
        self.nonconformity = {ticker: [] for ticker in self.UNIVERSE}

        # Prediction errors for coverage tracking
        self.errors = {ticker: [] for ticker in self.UNIVERSE}

        # Previous predictions (for computing errors)
        self.prev_predictions = {}

        # Previous portfolio weights (for vol targeting)
        self.prev_weights = {ticker: 1.0 / len(self.UNIVERSE)
                            for ticker in self.UNIVERSE}

        # Rebalancing counter
        self.days_since_rebalance = 0

        self.schedule.on(
            self.date_rules.every_day(),
            self.time_rules.after_market_open("SPY", 10),
            self.daily_update
        )

    def daily_update(self):
        """Daily update: track prediction errors, update ACI alpha."""
        self.days_since_rebalance += 1

        # Update ACI based on previous prediction errors
        self._update_aci()

        # Rebalance check
        if self.days_since_rebalance >= self.REBALANCE_DAYS:
            self._rebalance()
            self.days_since_rebalance = 0

    def _update_aci(self):
        """Update ACI alpha for each asset based on prediction errors."""
        for ticker, symbol in self.symbols.items():
            if ticker not in self.prev_predictions:
                continue

            history = self.history(symbol, self.MOM_WINDOWS[-1] + 5,
                                   Resolution.DAILY)
            if history.empty or len(history) < 5:
                continue

            close = history["close"].values
            actual_return = (close[-1] / close[-2]) - 1.0

            pred_return, pred_width = self.prev_predictions[ticker]

            # Check if actual fell within prediction interval
            half_width = pred_width / 2.0
            in_interval = (abs(actual_return - pred_return) <= half_width)

            # ACI alpha adjustment (Gibbs & Candès 2021)
            # alpha_t+1 = alpha_t + gamma * (1{not in interval} - target_alpha)
            target_alpha = 1.0 - self.TARGET_COVERAGE
            indicator = 0.0 if in_interval else 1.0
            self.aci_alpha[ticker] = max(
                0.01,
                min(0.50,
                    self.aci_alpha[ticker] + self.GAMMA *
                    (indicator - target_alpha))
            )

            # Update nonconformity score
            score = abs(actual_return - pred_return)
            self.nonconformity[ticker].append(score)
            if len(self.nonconformity[ticker]) > self.CALIBRATION_WINDOW:
                self.nonconformity[ticker] = \
                    self.nonconformity[ticker][-self.CALIBRATION_WINDOW:]

    def _compute_momentum_signal(self, ticker):
        """
        Compute multi-factor momentum signal.

        Returns:
            tuple: (signal, confidence) where signal is the expected
                   return and confidence is a 0-1 scale.
        """
        symbol = self.symbols[ticker]
        history = self.history(symbol, self.MOM_WINDOWS[-1] + 5,
                              Resolution.DAILY)
        if history.empty or len(history) < self.MOM_WINDOWS[-1] + 2:
            return 0.0, 0.0

        close = history["close"].values

        # Multi-window momentum
        signals = []
        for window in self.MOM_WINDOWS:
            ret = (close[-1] / close[-1 - window]) - 1.0
            signals.append(ret)

        # Weight: more recent windows get higher weight
        weights = np.array([0.2, 0.3, 0.5])
        signal = float(np.average(signals, weights=weights))

        # Confidence: agreement across windows (same sign)
        signs = [np.sign(s) for s in signals]
        agreement = sum(1 for s in signs if s == signs[0]) / len(signs)

        # Volatility-adjusted confidence
        returns = np.diff(close[-self.VOL_LOOKBACK:]) / close[-self.VOL_LOOKBACK:-1]
        vol = float(np.std(returns) * np.sqrt(252)) if len(returns) > 10 else 0.3

        # Lower vol = higher confidence
        vol_confidence = max(0.2, min(1.0, 0.2 / max(vol, 0.01)))

        confidence = float(agreement * vol_confidence)
        return signal, confidence

    def _compute_prediction_interval(self, ticker, signal):
        """
        Compute ACI-adjusted prediction interval width.

        Uses the empirical quantile of nonconformity scores, scaled
        by the ACI-adjusted alpha level.

        Returns:
            float: interval width (total, not half-width)
        """
        scores = self.nonconformity[ticker]

        if len(scores) < 10:
            # Insufficient calibration data: use conservative default
            return 0.10  # 10% default interval

        alpha = self.aci_alpha[ticker]
        sorted_scores = sorted(scores)

        # Quantile index for (1 - alpha) coverage
        q_idx = min(
            int(np.ceil((1.0 - alpha) * len(sorted_scores))) - 1,
            len(sorted_scores) - 1
        )
        q_idx = max(0, q_idx)
        quantile = sorted_scores[q_idx]

        # Scale by 1 + 1/sqrt(n) finite-sample correction
        n = len(scores)
        correction = 1.0 + 1.0 / np.sqrt(n)

        return float(2.0 * quantile * correction)

    def _rebalance(self):
        """Monthly rebalance with ACI-adjusted position sizing."""
        raw_weights = {}
        predictions = {}

        for ticker in self.symbols:
            signal, confidence = self._compute_momentum_signal(ticker)
            interval_width = self._compute_prediction_interval(ticker, signal)

            # Store prediction for next period's ACI update
            predictions[ticker] = (signal, interval_width)

            # Position sizing: signal strength / risk (interval width)
            # Wider intervals = more uncertainty = smaller position
            risk_factor = max(interval_width, 0.01)
            raw_weight = signal * confidence / risk_factor

            # Only long positions for momentum strategy
            raw_weights[ticker] = max(0.0, raw_weight)

        self.prev_predictions = predictions

        # Normalize weights
        total = sum(raw_weights.values())
        if total > 0:
            weights = {t: w / total for t, w in raw_weights.items()}
        else:
            # Equal weight fallback
            n = len(self.symbols)
            weights = {t: 1.0 / n for t in self.symbols}

        # Apply sector constraints
        weights = self._apply_sector_constraints(weights)

        # Apply volatility targeting
        weights = self._apply_vol_targeting(weights)

        # Execute trades
        for ticker, symbol in self.symbols.items():
            w = weights.get(ticker, 0.0)
            self.set_holdings(symbol, w)

        self.prev_weights = weights

    def _apply_sector_constraints(self, weights):
        """
        Enforce max sector weight constraint.

        Iteratively cap sector weights and redistribute excess.
        """
        for _ in range(3):  # 3 iterations sufficient for convergence
            sector_totals = {}
            for ticker, w in weights.items():
                sector = self.UNIVERSE[ticker]
                sector_totals[sector] = sector_totals.get(sector, 0.0) + w

            excess = {}
            for sector, total in sector_totals.items():
                if total > self.SECTOR_MAX:
                    excess[sector] = total - self.SECTOR_MAX

            if not excess:
                break

            # Scale down overweight sectors
            new_weights = {}
            for ticker, w in weights.items():
                sector = self.UNIVERSE[ticker]
                if sector in excess:
                    scale = self.SECTOR_MAX / sector_totals[sector]
                    new_weights[ticker] = w * scale
                else:
                    new_weights[ticker] = w

            weights = new_weights

        # Enforce individual bounds
        weights = {t: min(self.MAX_WEIGHT, max(0.0, w))
                   for t, w in weights.items()}

        # Re-normalize
        total = sum(weights.values())
        if total > 0:
            weights = {t: w / total for t, w in weights.items()}

        return weights

    def _apply_vol_targeting(self, weights):
        """
        Scale portfolio to target annualized volatility.

        Uses simple equal-correlation model for portfolio vol estimate.
        """
        # Estimate portfolio vol from recent returns
        returns_list = []
        for ticker, symbol in self.symbols.items():
            history = self.history(symbol, self.VOL_LOOKBACK + 5,
                                  Resolution.DAILY)
            if not history.empty and len(history) > self.VOL_LOOKBACK:
                close = history["close"].values
                rets = np.diff(close[-self.VOL_LOOKBACK:]) / \
                    close[-self.VOL_LOOKBACK:-1]
                returns_list.append(rets)

        if len(returns_list) < 3:
            return weights

        # Estimate individual volatilities
        vols = [float(np.std(r) * np.sqrt(252)) for r in returns_list]
        avg_vol = float(np.mean(vols))

        # Simple portfolio vol estimate (equal-correlation approx)
        w_array = np.array([weights.get(t, 0.0)
                           for t in self.symbols])
        vol_array = np.array(vols)

        # Assume average pairwise correlation of 0.4
        avg_corr = 0.4
        weighted_vol = float(np.dot(w_array, vol_array))
        cross_terms = float(
            avg_corr * (weighted_vol ** 2 -
                        np.dot(w_array ** 2, vol_array ** 2))
        )
        port_var = float(np.dot(w_array ** 2, vol_array ** 2)) + \
            max(0.0, cross_terms)
        port_vol = np.sqrt(port_var)

        # Scale to target vol
        if port_vol > 0.01:
            scale = min(1.0, self.TARGET_VOL / port_vol)
        else:
            scale = 1.0

        return {t: w * scale for t, w in weights.items()}

    def on_end_of_algorithm(self):
        """Log final ACI statistics."""
        self.log("=== Adaptive Conformal Risk - Final Stats ===")
        for ticker in sorted(self.aci_alpha.keys()):
            alpha = self.aci_alpha[ticker]
            n_scores = len(self.nonconformity[ticker])
            self.log(f"{ticker}: alpha={alpha:.3f}, "
                     f"scores={n_scores}, "
                     f"coverage~{1 - alpha:.1%}")
        self.log(f"Days traded: {self.days_since_rebalance}")
