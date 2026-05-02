# region imports
from AlgorithmImports import *
import numpy as np
from sklearn.linear_model import LinearRegression
from sklearn.preprocessing import StandardScaler
from sklearn.ensemble import GradientBoostingClassifier
# endregion


class CausalEventAlphaAlgorithm(QCAlgorithm):
    """
    Causal Event Alpha by Sector.

    Source: ECE student project (ErwanSi, Gr03 G.1), adapted for ESGF pool.
    Issue #238 - Integrate ECE student concepts into QC strategies.

    Estimates sector-specific earnings sensitivity (CATE proxy) using
    rolling regression of sector returns on earnings surprise factor.
    Sectors with high CATE get overweighted, low CATE underweighted.

    Simplified from student's Double ML (EconML) pipeline to work within
    QC LEAN constraints (no econml dependency).

    Key concepts:
    - CATE (Conditional Average Treatment Effect) by sector
    - Earnings surprise as treatment variable
    - Rolling OLS regression as simplified DML
    - Sector rotation based on causal sensitivity
    """

    # Sector ETFs with earnings sensitivity classification
    SECTOR_ETFS = {
        "XLK": "Technology",
        "XLF": "Financials",
        "XLV": "Healthcare",
        "XLE": "Energy",
        "XLY": "Consumer Discretionary",
        "XLP": "Consumer Staples",
        "XLU": "Utilities",
        "XLI": "Industrials",
    }

    # Parameters
    LOOKBACK_DAYS = 252          # 1-year training window
    FORWARD_DAYS = 10            # 10-day forward return prediction
    RETRAIN_MONTHS = 3           # Retrain quarterly
    SURPRISE_THRESHOLD = 0.02   # 2% earnings surprise = significant
    CATE_TOP_N = 3              # Number of high-CATE sectors to overweight
    CATE_BOTTOM_N = 2           # Number of low-CATE sectors to underweight
    MAX_POSITION_WEIGHT = 0.20  # Max weight per sector
    MIN_POSITION_WEIGHT = 0.03  # Min weight per sector
    BASE_WEIGHT = 0.125         # Equal weight baseline (1/8 sectors)
    SMA_PERIOD = 200            # Market regime SMA

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)

        # Add sector ETFs
        self.symbols = {}
        for ticker in self.SECTOR_ETFS:
            symbol = self.add_equity(ticker, Resolution.DAILY).Symbol
            self.symbols[ticker] = symbol

        # SPY for market regime and benchmark
        self._spy = self.add_equity("SPY", Resolution.DAILY).Symbol
        self.set_benchmark(self._spy)
        self._spy_sma = self.SMA(self._spy, self.SMA_PERIOD, Resolution.DAILY)

        # Model state
        self.sector_cate = {}     # Sector -> CATE estimate
        self.sector_models = {}   # Sector -> trained GB model
        self.sector_scalers = {}  # Sector -> fitted scaler
        self.last_train_date = None

        # Schedule: monthly rebalance
        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.rebalance
        )

        # Schedule: quarterly retraining
        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 60),
            self.try_train
        )

        self.set_warm_up(self.SMA_PERIOD + 20, Resolution.Daily)

    def try_train(self):
        """Train models quarterly."""
        if self.is_warming_up:
            return

        # Check if enough time since last train
        if (self.last_train_date is not None
                and (self.time - self.last_train_date).days < 80):
            return

        self.train_models()
        self.last_train_date = self.time

    # ----------------------------------------------------------------
    # CATE Estimation (Simplified DML via Rolling Regression)
    # ----------------------------------------------------------------

    def estimate_sector_cate(self, ticker):
        """
        Estimate CATE for a sector using rolling OLS.

        The student used Double ML (EconML) to estimate:
            CATE = E[Y | X, T=1] - E[Y | X, T=0]

        We approximate with rolling regression of sector returns
        on market returns and earnings surprise proxy:
            sector_return = alpha + beta * market + gamma * surprise + epsilon

        gamma approximates the causal effect of earnings on sector returns.
        """
        symbol = self.symbols[ticker]
        history = self.history(symbol, self.LOOKBACK_DAYS, Resolution.Daily)
        spy_history = self.history(self._spy, self.LOOKBACK_DAYS, Resolution.Daily)

        if history is None or len(history) < 100:
            return 0.0
        if spy_history is None or len(spy_history) < 100:
            return 0.0

        closes = history['close']
        spy_closes = spy_history['close']

        if len(closes) < 60 or len(spy_closes) < 60:
            return 0.0

        # Compute returns
        sector_returns = closes.pct_change().dropna()
        market_returns = spy_closes.pct_change().dropna()

        # Align indices
        common_idx = sector_returns.index.intersection(market_returns.index)
        if len(common_idx) < 60:
            return 0.0

        sector_ret = sector_returns.loc[common_idx].values
        market_ret = market_returns.loc[common_idx].values

        # Create earnings surprise proxy: large positive daily returns
        # that exceed market by significant margin (treatment = earnings event)
        surprise = (sector_ret - market_ret)
        treatment = (surprise > self.SURPRISE_THRESHOLD).astype(float)

        # Rolling CATE estimation: fit regression on treatment effect
        # Y = alpha + beta * market + gamma * treatment + epsilon
        X = np.column_stack([
            market_ret,
            treatment,
            np.abs(market_ret),  # Volatility interaction
        ])
        y = sector_ret

        try:
            reg = LinearRegression().fit(X, y)
            # gamma coefficient = causal effect of earnings surprise
            cate_estimate = reg.coef_[1]

            # Also compute R-squared to filter noisy sectors
            r_squared = reg.score(X, y)

            # Penalize CATE for low R-squared (unreliable estimate)
            confidence_penalty = min(1.0, max(0.0, r_squared / 0.1))
            cate_estimate *= confidence_penalty

            return float(cate_estimate)

        except Exception:
            return 0.0

    # ----------------------------------------------------------------
    # Sector ML Models
    # ----------------------------------------------------------------

    def train_sector_model(self, ticker):
        """Train a GB classifier for sector direction prediction."""
        symbol = self.symbols[ticker]
        spy_symbol = self._spy

        history = self.history(symbol, self.LOOKBACK_DAYS * 2, Resolution.Daily)
        spy_history = self.history(spy_symbol, self.LOOKBACK_DAYS * 2, Resolution.Daily)

        if history is None or len(history) < 200:
            return None, None

        closes = history['close']
        spy_closes = spy_history['close']

        if len(closes) < 200 or len(spy_closes) < 200:
            return None, None

        # Build features and targets
        returns = closes.pct_change().dropna()
        spy_returns = spy_closes.pct_change().dropna()

        common_idx = returns.index.intersection(spy_returns.index)
        if len(common_idx) < 150:
            return None, None

        returns = returns.loc[common_idx]
        spy_returns = spy_returns.loc[common_idx]

        # Features: rolling statistics
        features_list = []
        targets_list = []

        for i in range(50, len(returns) - self.FORWARD_DAYS):
            window = returns.iloc[i-50:i]
            spy_window = spy_returns.iloc[i-50:i]

            # 8 features
            feat = [
                window.mean(),                    # Mean return
                window.std(),                     # Volatility
                window.skew(),                    # Skewness
                window.kurtosis(),                # Tail risk
                returns.iloc[i] - spy_returns.iloc[i],  # Relative return
                spy_window.std(),                 # Market vol
                (window.mean() - spy_window.mean()),  # Alpha proxy
                window.iloc[-5:].std(),           # Recent vol
            ]

            # Target: positive forward return
            forward_return = returns.iloc[i+1:i+1+self.FORWARD_DAYS].sum()
            target = 1 if forward_return > 0 else 0

            if not any(np.isnan(f) for f in feat):
                features_list.append(feat)
                targets_list.append(target)

        if len(features_list) < 50:
            return None, None

        X = np.array(features_list)
        y = np.array(targets_list)

        scaler = StandardScaler()
        X_scaled = scaler.fit_transform(X)

        model = GradientBoostingClassifier(
            n_estimators=100,
            max_depth=4,
            learning_rate=0.08,
            min_samples_split=10,
            random_state=42
        )
        model.fit(X_scaled, y)

        return model, scaler

    def train_models(self):
        """Train CATE estimates and sector models for all sectors."""
        if self.is_warming_up:
            return

        self.debug("Training CATE estimates and sector models...")

        for ticker in self.SECTOR_ETFS:
            # Estimate CATE
            cate = self.estimate_sector_cate(ticker)
            self.sector_cate[ticker] = cate

            # Train sector prediction model
            model, scaler = self.train_sector_model(ticker)
            if model is not None:
                self.sector_models[ticker] = model
                self.sector_scalers[ticker] = scaler

        cate_str = ", ".join(
            f"{t}: {c:.4f}" for t, c in sorted(
                self.sector_cate.items(), key=lambda x: x[1], reverse=True
            )
        )
        self.debug(f"CATE estimates: {cate_str}")

    # ----------------------------------------------------------------
    # Prediction
    # ----------------------------------------------------------------

    def predict_sector(self, ticker):
        """Predict sector direction using trained model."""
        if ticker not in self.sector_models:
            return 0.5

        model = self.sector_models[ticker]
        scaler = self.sector_scalers[ticker]

        symbol = self.symbols[ticker]
        history = self.history(symbol, 60, Resolution.Daily)
        spy_history = self.history(self._spy, 60, Resolution.Daily)

        if history is None or len(history) < 50:
            return 0.5
        if spy_history is None or len(spy_history) < 50:
            return 0.5

        returns = history['close'].pct_change().dropna()
        spy_returns = spy_history['close'].pct_change().dropna()

        if len(returns) < 50:
            return 0.5

        window = returns.iloc[-50:]
        spy_window = spy_returns.iloc[-50:]

        feat = [
            window.mean(),
            window.std(),
            window.skew(),
            window.kurtosis(),
            returns.iloc[-1] - spy_returns.iloc[-1],
            spy_window.std(),
            (window.mean() - spy_window.mean()),
            window.iloc[-5:].std(),
        ]

        if any(np.isnan(f) for f in feat):
            return 0.5

        try:
            x = scaler.transform(np.array(feat).reshape(1, -1))
            proba = model.predict_proba(x)[0]
            # Probability of class 1 (positive return)
            class_list = list(model.classes_)
            if 1 in class_list:
                return float(proba[class_list.index(1)])
            return 0.5
        except Exception:
            return 0.5

    # ----------------------------------------------------------------
    # Rebalancing
    # ----------------------------------------------------------------

    def is_bear_market(self):
        """Check if SPY is below 200-day SMA."""
        if not self._spy_sma.is_ready:
            return False
        return self.securities[self._spy].price < self._spy_sma.current.value

    def rebalance(self):
        """
        Rebalance based on CATE-weighted sector rotation.

        High CATE sectors get overweight (they respond more to earnings).
        Low CATE sectors get underweight (they are less sensitive).
        Direction prediction (GB model) refines the allocation.
        """
        if self.is_warming_up:
            return

        # Ensure models are trained
        if not self.sector_cate:
            self.train_models()
            if not self.sector_cate:
                return

        bear_market = self.is_bear_market()

        # Score each sector: CATE * prediction probability
        sector_scores = {}
        for ticker in self.SECTOR_ETFS:
            cate = self.sector_cate.get(ticker, 0.0)
            pred_prob = self.predict_sector(ticker)

            # Combined score: CATE influence * direction confidence
            # In bear market, reduce CATE weight (less earnings effect)
            cate_weight = 0.3 if bear_market else 0.5
            pred_weight = 0.7 if bear_market else 0.5

            # Normalize CATE to [0, 1] range (CATE can be negative)
            cate_normalized = max(0.0, min(1.0, cate * 10 + 0.5))

            score = cate_weight * cate_normalized + pred_weight * pred_prob
            sector_scores[ticker] = score

        # Rank sectors by combined score
        ranked = sorted(
            sector_scores.items(), key=lambda x: x[1], reverse=True
        )

        # Allocate weights based on rank
        weights = {}
        tickers = [t for t, _ in ranked]

        if bear_market:
            # In bear: concentrate on top 3-4 sectors with defensive bias
            n_positions = min(4, len(tickers))
            selected = tickers[:n_positions]
            weight_per = 1.0 / n_positions
            for t in selected:
                weights[t] = weight_per
        else:
            # In bull: weight by score with CATE tilt
            # Top CATE sectors get overweight
            total_score = sum(
                max(0.01, s) for _, s in ranked
            )
            for ticker, score in ranked:
                raw_weight = max(0.01, score) / total_score
                # Apply CATE tilt: boost high-CATE sectors
                cate = self.sector_cate.get(ticker, 0.0)
                cate_boost = 1.0 + max(0.0, cate) * 2.0  # Up to 3x boost
                adjusted_weight = raw_weight * cate_boost
                weights[ticker] = adjusted_weight

            # Normalize
            total = sum(weights.values())
            if total > 0:
                weights = {t: w / total for t, w in weights.items()}

            # Clip weights to bounds
            weights = {
                t: max(self.MIN_POSITION_WEIGHT,
                       min(self.MAX_POSITION_WEIGHT, w))
                for t, w in weights.items()
            }
            # Re-normalize after clipping
            total = sum(weights.values())
            if total > 0:
                weights = {t: w / total for t, w in weights.items()}

        # Execute trades
        target_symbols = {self.symbols[t] for t in weights}

        for ticker in self.SECTOR_ETFS:
            symbol = self.symbols[ticker]
            if symbol not in target_symbols and self.portfolio[symbol].invested:
                self.liquidate(symbol)

        for ticker, weight in weights.items():
            self.set_holdings(self.symbols[ticker], weight)

        regime = "BEAR" if bear_market else "BULL"
        top3 = ranked[:3]
        self.debug(
            f"{regime} | Top: "
            f"{[(t, f'{s:.3f}') for t, s in top3]} | "
            f"Weights: {[(t, f'{w:.2f}') for t, w in list(weights.items())[:4]]}"
        )
