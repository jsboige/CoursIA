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

    Version 1.1 improvements:
    - Anti-micro-rebalancing threshold: skip trades when position delta < 5%
    - Causal forward-filter: explicit look-ahead guard in regime detection
    - Extended end date to 2026

    Version 1.2 (#15534, consolidating research article #19465):
    - Optional Fear & Greed exposure overlay, gated by the parameter
      use_feargreed (default 0 = baseline behavior strictly unchanged)
    - The overlay fits the same MarkovRegression tool on the trailing
      FearGreedIndex history (k_regimes=2, the article's setting) and
      halves the SPY allocation when the SPY regime asks for SPY but the
      index regime sits in its greedy state (entries gated in greed, the
      article's filter rule, adapted to monthly rotation)
    - The greedy regime is identified by its fitted mean index level,
      never by a hardcoded regime number
    - start_year/end_year parameters (defaults preserve 2015-2026) enable
      IS/OOS and sub-period runs without code forks

    Version 1.0 - Binary Regime Switching:
    - Binary allocation: SPY in low volatility regime, TLT in high volatility
    - Monthly rebalance schedule
    - Constant GLD hedge (10%)
    - Confirmation filter: only switch when probability > 55%
    - Sharpe 0.408 on 2015-2024 backtest

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
        self.set_start_date(int(self.get_parameter('start_year', 2015)), 1, 1)
        self.set_end_date(int(self.get_parameter('end_year', 2026)), 1, 1)
        self.set_cash(100_000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

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

        # Fear & Greed overlay (#15534 / article #19465). Default OFF: the
        # baseline never subscribes to the dataset and its behavior is
        # byte-for-byte the v1.1 logic.
        self._use_fg = self.get_parameter('use_feargreed', 0) == 1
        self._fg_symbol = None
        if self._use_fg:
            # FearGreedIndex comes with the AlgorithmImports wildcard; the
            # custom ticker is 'FG' (official dataset docs), coverage from
            # July 2014, daily.
            self._fg_symbol = self.add_data(FearGreedIndex, "FG").symbol
        self._gld_weight = 0.10
        self._equity_weight = 0.80  # Max allocation to SPY or TLT
        self._confirmation_threshold = 0.55

        # Anti-micro-rebalancing threshold
        self._rebalance_threshold = 0.05  # Skip trades when position delta < 5%

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

        self.log(
            f"MarkovRegimeDetection v1.2 initialized: feargreed_overlay="
            f"{'ON' if self._use_fg else 'OFF'}"
        )

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

    def _fg_greedy(self):
        """True when the trailing Fear & Greed regime is its greedy state.

        Mirrors the #19465 filter: MarkovRegression(k_regimes=2) on the
        trailing index history (the article's exact setting), entries gated
        in the greedy regime. The greedy state is the one with the higher
        fitted mean index level, so a regime renumbering across fits cannot
        silently flip the filter.
        """
        if not self._use_fg or self._fg_symbol is None:
            return False
        df = self.history(self._fg_symbol, self._lookback_period + timedelta(7))
        if df is None or df.empty:
            return False
        if isinstance(df.index, pd.MultiIndex):
            series = df.reset_index(level=0, drop=True)["value"]
        else:
            series = df["value"]
        series = series.dropna()
        if len(series) < 100:
            return False
        fitted = MarkovRegression(series, k_regimes=2).fit()
        regime = int(fitted.smoothed_marginal_probabilities.values.argmax(axis=1)[-1])
        means = [float(fitted.params[f"const[{i}]"]) for i in range(2)]
        greedy_regime = 0 if means[0] >= means[1] else 1
        return regime == greedy_regime

    def _trade(self):
        """
        Detect current regime and rebalance portfolio using binary allocation.

        Regime interpretation:
        - regime 0: Low volatility -> bullish environment -> SPY
        - regime 1: High volatility -> bearish environment -> TLT
        """
        if len(self._daily_returns) < 100:
            self.log("Not enough data for regime detection")
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
            max_prob = max(prob_low_vol, 1 - prob_low_vol)
            if max_prob < self._confirmation_threshold:
                self.log(f"Regime uncertain (prob={max_prob:.2%}), holding current allocation")
                return

            # Rebalance only when regime changes
            if regime != self._previous_regime:
                if regime == 0:
                    # Low volatility -> bullish -> SPY
                    regime_name = "LOW_VOL"
                    spy_weight = self._equity_weight
                    tlt_weight = 0.0
                    if self._fg_greedy():
                        # #15534 overlay: the SPY regime asks for risk but
                        # the Fear & Greed regime sits in greed -- halve the
                        # exposure, remainder stays in cash (never TLT: that
                        # would blend the two regime signals).
                        regime_name = "LOW_VOL/FG_GREEDY"
                        spy_weight = self._equity_weight * 0.5
                else:
                    # High volatility -> bearish -> TLT
                    regime_name = "HIGH_VOL"
                    spy_weight = 0.0
                    tlt_weight = self._equity_weight

                self.log(f"Regime: {regime_name}, prob_low_vol={prob_low_vol:.2%}")
                self.log(f"Allocation: SPY={spy_weight:.2%}, TLT={tlt_weight:.2%}, GLD={self._gld_weight:.2%}")

                # Anti-micro-rebalancing: check if position delta exceeds threshold
                current_spy_weight = (
                    self.portfolio[self._spy].holdings_value
                    / self.portfolio.total_portfolio_value
                    if self.portfolio[self._spy].invested else 0.0
                )
                spy_delta = abs(spy_weight - current_spy_weight)
                if spy_delta < self._rebalance_threshold:
                    self.log(f"Skipping micro-rebalance (delta={spy_delta:.2%})")
                    self._previous_regime = regime
                    return

                self.set_holdings([
                    PortfolioTarget(self._spy, spy_weight),
                    PortfolioTarget(self._tlt, tlt_weight),
                    PortfolioTarget(self._gld, self._gld_weight)
                ])

            self._previous_regime = regime

        except Exception as e:
            self.log(f"Model fitting error: {e}")

    def on_end_of_algorithm(self):
        final_value = self.portfolio.total_portfolio_value
        returns = (final_value - 100000) / 100000
        self.log(f"Markov Regime Detection v1.1: Final=${final_value:,.0f}, Return={returns:.2%}")
