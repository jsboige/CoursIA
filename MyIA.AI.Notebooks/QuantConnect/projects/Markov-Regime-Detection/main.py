# region imports
from AlgorithmImports import *

from statsmodels.tsa.regime_switching.markov_regression import MarkovRegression
import pandas as pd
# endregion


class MarkovRegimeDetection(QCAlgorithm):
    """
    Regime Detection using Markov-Switching Dynamic Regression.

    This strategy demonstrates how to use a Markov-switching model to detect
    2 distinct market regimes: high volatility and low volatility.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 04

    Version 1.1 - Risk-Managed Allocation:
    - Probabilistic position sizing (uses smoothed probabilities)
    - Diversification with GLD (10% constant hedge)
    - Maximum 80% allocation to any single asset
    - Confirmation filter: only rebalance when probability > 55%

    How it works:
    1. Collect trailing daily returns of SPY
    2. Fit a Markov Regression model with 2 regimes (k_regimes=2)
    3. Each regime has its own variance (switching_variance=True)
    4. Use smoothed probabilities for proportional allocation
    5. SPY weight = prob_low_vol * 0.80, TLT weight = (1 - prob_low_vol) * 0.80
    6. GLD constant 10% hedge

    Parameters:
    - lookback_years: Number of years of data for model training (default: 3)
    - max_equity_weight: Maximum allocation to SPY (default: 0.80)
    - confirmation_threshold: Minimum probability to rebalance (default: 0.55)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 1, 1)
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
        self._max_equity_weight = self.get_parameter('max_equity_weight', 0.80)
        self._confirmation_threshold = self.get_parameter('confirmation_threshold', 0.55)
        self._gld_weight = 0.10  # Constant gold hedge
        self._previous_prob = 0.5  # Track probability for shift detection

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

        # Schedule daily regime check
        self.schedule.on(
            self.date_rules.every_day(self._spy),
            self.time_rules.after_market_open(self._spy, 30),
            self._trade
        )

        # Track previous regime to avoid unnecessary rebalancing
        self._previous_regime = None

        self.log("MarkovRegimeDetection v1.1 initialized: probabilistic allocation, GLD hedge, 55% confirmation")

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
        Detect current regime and rebalance portfolio using probabilistic allocation.

        Regime interpretation:
        - regime 0: Low volatility -> bullish environment -> SPY
        - regime 1: High volatility -> bearish environment -> TLT

        v1.1 improvements:
        - Probabilistic allocation: SPY weight = prob_low_vol * max_equity_weight
        - GLD constant 10% hedge
        - Confirmation filter: only rebalance when prob > threshold
        """
        if len(self._daily_returns) < 100:
            self.log("Not enough data for regime detection")
            return

        try:
            # Create Markov-switching model
            # k_regimes=2: high and low volatility
            # switching_variance=True: each regime has own variance
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
            self.plot('Regime', 'Low Vol Probability', prob_low_vol)
            self.plot('Regime', 'Volatility Class', regime)

            # Confirmation filter: only rebalance when probability is confident
            max_prob = max(prob_low_vol, 1 - prob_low_vol)
            if max_prob < self._confirmation_threshold:
                self.log(f"Regime uncertain (prob={max_prob:.2%}), holding current allocation")
                return

            # Rebalance only when regime changes or significant probability shift
            previous_prob = getattr(self, '_previous_prob', 0.5)
            prob_shift = abs(prob_low_vol - previous_prob)

            if regime != self._previous_regime or prob_shift > 0.15:
                regime_name = "HIGH_VOL" if regime == 1 else "LOW_VOL"
                self.log(f"Regime: {regime_name}, prob_low_vol={prob_low_vol:.2%}")

                # Probabilistic allocation (v1.1)
                # Risk budget: 90% total (10% GLD constant)
                risk_budget = 1.0 - self._gld_weight

                # SPY weight = probability of low vol * max equity weight
                spy_weight = prob_low_vol * self._max_equity_weight * risk_budget
                # TLT weight = probability of high vol * max equity weight
                tlt_weight = (1 - prob_low_vol) * self._max_equity_weight * risk_budget
                # GLD constant hedge
                gld_weight = self._gld_weight

                self.log(f"Allocation: SPY={spy_weight:.2%}, TLT={tlt_weight:.2%}, GLD={gld_weight:.2%}")

                self.set_holdings([
                    PortfolioTarget(self._spy, spy_weight),
                    PortfolioTarget(self._tlt, tlt_weight),
                    PortfolioTarget(self._gld, gld_weight)
                ])

            self._previous_regime = regime
            self._previous_prob = prob_low_vol

        except Exception as e:
            self.log(f"Model fitting error: {e}")

    def on_end_of_algorithm(self):
        final_value = self.portfolio.total_portfolio_value
        returns = (final_value - 100000) / 100000
        self.log(f"Markov Regime Detection v1.1: Final=${final_value:,.0f}, Return={returns:.2%}")
