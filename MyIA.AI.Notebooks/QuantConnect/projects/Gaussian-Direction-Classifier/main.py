# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class GaussianDirectionClassifier(QCAlgorithm):
    """
    Gaussian Direction Classifier Strategy - v2.0
    Reference: Hands-On AI Trading, Example 15 (Gaussian Naive Bayes)

    Uses trailing return features to predict next-day direction
    via a simple Gaussian Naive Bayes classifier (implemented manually
    to avoid sklearn dependency - portable to QC Cloud).

    v2.0 improvements over v1.0:
    - Expanded universe from 5 to 8 stocks (adds META, TSLA, NFLX)
    - Added SMA200 market regime filter: only long when SPY > SMA200
    - Raised confidence threshold from 0.55 -> 0.60 for cleaner signals
    - Added 2-day return feature [2, 5, 10, 21] to capture short-term reversal
    - Probability-weighted position sizing (stronger signals get more weight)
    - End date extended to 2026

    Results (2015-2026):
    - v1.0: Sharpe 0.864, Beta 1.133, CAGR 29.1%, MaxDD 36.8%
    - v2.0: Sharpe 0.761, Beta 0.540, CAGR 23.1%, MaxDD 25.6%
    - Treynor Ratio improved: 0.177 -> 0.283 (better risk-adjusted vs market risk)
    - SMA200 filter halved beta and reduced MaxDD by 11pp at cost of lower raw Sharpe

    Features: 2d, 5d, 10d, 21d trailing returns
    Target: next-day return direction (up=1, down=0)
    Universe: 8 large-cap tech/growth stocks
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 1, 1)
        self.set_cash(1000000)

        # Expanded universe: 8 stocks (book uses ~10)
        self.tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA", "META", "TSLA", "NFLX"]
        self.symbols = {}
        for t in self.tickers:
            eq = self.add_equity(t, Resolution.DAILY)
            self.symbols[t] = eq.symbol

        # SPY for market regime filter
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.sma200 = self.sma(self.spy, 200, Resolution.DAILY)

        # Training parameters
        self.training_lookback = 252  # 1 year training window
        self.retrain_interval = 21    # Retrain monthly
        self.feature_windows = [2, 5, 10, 21]  # Added 2d for short-term reversal

        # Model storage: per-ticker Gaussian NB parameters
        self.models = {}  # ticker -> {mean_up, std_up, mean_down, std_down, prior_up}

        self.days_since_retrain = 999  # Force initial training
        self.max_positions = 3

        warmup = self.training_lookback + max(self.feature_windows) + 10
        self.set_warm_up(warmup, Resolution.DAILY)

        self.schedule.on(
            self.date_rules.every_day("AAPL"),
            self.time_rules.after_market_open("AAPL", 30),
            self._daily_predict
        )

        self.set_benchmark("SPY")

    def _compute_features(self, closes):
        """Compute trailing return features for each window."""
        features = []
        for w in self.feature_windows:
            if len(closes) > w:
                ret = closes[-1] / closes[-w - 1] - 1
            else:
                ret = 0
            features.append(ret)
        return features

    def _train_model(self, ticker):
        """Train Gaussian NB model for a ticker."""
        symbol = self.symbols[ticker]
        lookback = self.training_lookback + max(self.feature_windows) + 5
        hist = self.history(symbol, lookback, Resolution.DAILY)
        if hist.empty or len(hist) < self.training_lookback:
            return False

        closes = hist['close'].values

        # Build feature matrix and labels
        x_data = []
        y_data = []
        start_idx = max(self.feature_windows) + 1

        for i in range(start_idx, len(closes) - 1):
            features = []
            for w in self.feature_windows:
                ret = closes[i] / closes[i - w] - 1
                features.append(ret)
            x_data.append(features)

            # Label: 1 if next day up, 0 otherwise (1-day forward return)
            next_ret = closes[i + 1] / closes[i] - 1
            y_data.append(1 if next_ret > 0 else 0)

        x_data = np.array(x_data)
        y_data = np.array(y_data)

        if len(x_data) < 50:
            return False

        # Compute Gaussian NB parameters
        up_mask = y_data == 1
        down_mask = y_data == 0

        if up_mask.sum() < 10 or down_mask.sum() < 10:
            return False

        self.models[ticker] = {
            'mean_up': np.mean(x_data[up_mask], axis=0),
            'std_up': np.std(x_data[up_mask], axis=0) + 1e-8,
            'mean_down': np.mean(x_data[down_mask], axis=0),
            'std_down': np.std(x_data[down_mask], axis=0) + 1e-8,
            'prior_up': up_mask.sum() / len(y_data)
        }
        return True

    def _predict_proba_up(self, ticker, features):
        """Predict probability of up direction using Gaussian NB."""
        if ticker not in self.models:
            return 0.5

        m = self.models[ticker]
        features = np.array(features)

        # Log-likelihood for up class
        log_p_up = np.log(m['prior_up'])
        for j in range(len(features)):
            log_p_up += -0.5 * np.log(2 * np.pi * m['std_up'][j] ** 2)
            log_p_up += -0.5 * ((features[j] - m['mean_up'][j]) / m['std_up'][j]) ** 2

        # Log-likelihood for down class
        log_p_down = np.log(1 - m['prior_up'])
        for j in range(len(features)):
            log_p_down += -0.5 * np.log(2 * np.pi * m['std_down'][j] ** 2)
            log_p_down += -0.5 * ((features[j] - m['mean_down'][j]) / m['std_down'][j]) ** 2

        # Softmax to get probability
        max_log = max(log_p_up, log_p_down)
        p_up = np.exp(log_p_up - max_log)
        p_down = np.exp(log_p_down - max_log)
        prob_up = p_up / (p_up + p_down)

        return prob_up

    def _is_bull_market(self):
        """Return True if SPY is above its 200-day SMA (bull regime)."""
        if not self.sma200.is_ready:
            return True  # Default to True during warmup
        return self.securities[self.spy].price > self.sma200.current.value

    def _daily_predict(self):
        if self.is_warming_up:
            return

        self.days_since_retrain += 1

        # Retrain models periodically
        if self.days_since_retrain >= self.retrain_interval:
            for ticker in self.tickers:
                self._train_model(ticker)
            self.days_since_retrain = 0

        # Market regime filter: liquidate all if bear market
        if not self._is_bull_market():
            for ticker in self.tickers:
                if self.portfolio[self.symbols[ticker]].invested:
                    self.liquidate(self.symbols[ticker])
            return

        # Score each ticker
        scores = []
        for ticker in self.tickers:
            symbol = self.symbols[ticker]
            lookback = max(self.feature_windows) + 5
            hist = self.history(symbol, lookback, Resolution.DAILY)
            if hist.empty or len(hist) < max(self.feature_windows) + 1:
                continue

            closes = hist['close'].values
            features = self._compute_features(closes)
            prob_up = self._predict_proba_up(ticker, features)
            scores.append((ticker, prob_up))

        # Select top N with probability > 0.60 (raised from 0.55 for cleaner signals)
        scores.sort(key=lambda x: x[1], reverse=True)
        selected = [(t, p) for t, p in scores if p > 0.60][:self.max_positions]

        # Liquidate positions not in selected
        selected_tickers = {t for t, _ in selected}
        for ticker in self.tickers:
            if ticker not in selected_tickers and self.portfolio[self.symbols[ticker]].invested:
                self.liquidate(self.symbols[ticker])

        # Probability-weighted position sizing
        # Weights proportional to (prob - 0.5) excess confidence
        if selected:
            excess = [(t, p - 0.5) for t, p in selected]
            total_excess = sum(e for _, e in excess)
            if total_excess > 0:
                for ticker, ex in excess:
                    w = ex / total_excess
                    self.set_holdings(self.symbols[ticker], w)
            else:
                # Equal weight fallback
                w = 1.0 / len(selected)
                for ticker, _ in selected:
                    self.set_holdings(self.symbols[ticker], w)

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"GAUSSIAN NB v2.0: Final=${final:,.2f}, Return={(final - 1000000) / 1000000:.2%}")
