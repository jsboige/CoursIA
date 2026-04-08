#region imports
from AlgorithmImports import *

from statsmodels.tsa.regime_switching.markov_regression import MarkovRegression
import pandas as pd
# endregion
# Hands-On AI Trading - Ex04: Alpha by Hidden Markov Models
# Uses a Markov-switching dynamic regression model to detect 2 regimes
# (high/low volatility). Allocates to TLT during high-vol regimes and
# SPY during low-vol regimes.
# Source: HandsOnAITradingBook, Section 06, Example 04


class MarkovRegimeDetection(QCAlgorithm):
    """
    Regime Detection using Markov-Switching Dynamic Regression.

    This strategy demonstrates how to use a Markov-switching model to detect
    2 distinct market regimes: high volatility and low volatility.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 04

    How it works:
    1. Collect trailing daily returns of SPY
    2. Fit a Markov Regression model with 2 regimes (k_regimes=2)
    3. Each regime has its own variance (switching_variance=True)
    4. Use smoothed probabilities to determine current regime
    5. Low volatility regime -> SPY (80%), High volatility -> TLT (80%)
    6. GLD constant 10% hedge

    Parameters:
    - lookback_years: Number of years of data for model training (default: 3)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 1, 1)
        self.set_cash(100_000)

        # Risk assets (low volatility regime)
        self._spy = self.add_equity("SPY", Resolution.DAILY).symbol
        # Safe haven (high volatility regime)
        self._tlt = self.add_equity("TLT", Resolution.DAILY).symbol
        # Gold hedge (constant allocation)
        self._gld = self.add_equity("GLD", Resolution.DAILY).symbol

        # Model parameters
        self._lookback_period = timedelta(
            self.get_parameter('lookback_years', 3) * 365
        )
        self._gld_weight = 0.10
        self._equity_weight = 0.80  # Max allocation to SPY or TLT
        self._confirmation_threshold = 0.55

        # Anti-micro-rebalancing threshold
        self._rebalance_threshold = 0.05  # Skip trades when delta < 5%

        # Trailing daily returns series
        self._daily_returns = pd.Series()

        # Rate of change indicator for returns
        roc = self.roc(self._spy, 1, Resolution.DAILY)
        roc.updated += self._update_event_handler

        # Warm up with historical data
        history = self.history[TradeBar](
            self._spy, self._lookback_period + timedelta(7), Resolution.DAILY
        )
        for bar in history:
            roc.update(bar.end_time, bar.close)

        # Monthly rebalance schedule
        self.schedule.on(
            self.date_rules.month_start(self._spy),
            self.time_rules.after_market_open(self._spy, 30),
            self._trade
        )

        # Track previous regime to avoid unnecessary rebalancing
        self._previous_regime = None

    def _update_event_handler(self, indicator, indicator_data_point):
        """Update trailing returns series."""
        if not indicator.is_ready:
            return

        t = indicator_data_point.end_time
        self._daily_returns.loc[t] = indicator_data_point.value

        # Trim to lookback window
        self._daily_returns = self._daily_returns[
            t - self._daily_returns.index <= self._lookback_period
        ]

    def _trade(self):
        """
        Detect current regime and rebalance portfolio.

        Regime interpretation:
        - regime 0: Low volatility -> bullish environment -> SPY
        - regime 1: High volatility -> bearish environment -> TLT
        """
        if len(self._daily_returns) < 100:
            return

        try:
            # Create Markov-switching model
            model = MarkovRegression(
                self._daily_returns, k_regimes=2, switching_variance=True
            )

            # Fit model and get smoothed probabilities
            fitted_model = model.fit()
            smoothed_probs = fitted_model.smoothed_marginal_probabilities

            # Get probability of low volatility regime (regime 0)
            prob_low_vol = smoothed_probs.values[-1, 0]
            regime = smoothed_probs.values.argmax(axis=1)[-1]

            # Plot regime probability for visualization
            self.plot('Regime', 'Low Vol Probability', float(prob_low_vol))
            self.plot('Regime', 'Volatility Class', int(regime))

            # Confirmation filter: only rebalance when probability is confident
            max_prob = max(float(prob_low_vol), 1 - float(prob_low_vol))
            if max_prob < self._confirmation_threshold:
                return

            # Rebalance only when regime changes
            if regime != self._previous_regime:
                if regime == 0:
                    # Low volatility -> bullish -> SPY
                    spy_weight = self._equity_weight
                    tlt_weight = 0.0
                else:
                    # High volatility -> bearish -> TLT
                    spy_weight = 0.0
                    tlt_weight = self._equity_weight

                # Anti-micro-rebalancing check
                current_spy_weight = (
                    self.portfolio[self._spy].holdings_value
                    / self.portfolio.total_portfolio_value
                    if self.portfolio[self._spy].invested else 0.0
                )
                spy_delta = abs(spy_weight - current_spy_weight)
                if spy_delta < self._rebalance_threshold:
                    self._previous_regime = regime
                    return

                self.set_holdings([
                    PortfolioTarget(self._spy, spy_weight),
                    PortfolioTarget(self._tlt, tlt_weight),
                    PortfolioTarget(self._gld, self._gld_weight)
                ])

            self._previous_regime = regime

        except Exception:
            return

    def on_data(self, data):
        pass
