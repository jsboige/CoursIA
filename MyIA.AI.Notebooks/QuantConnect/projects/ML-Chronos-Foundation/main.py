#region imports
from AlgorithmImports import *
import numpy as np
# endregion
# Hands-On AI Trading - Ex18: Amazon Chronos Foundation Model
# Uses the Chronos time-series foundation model (chronos-t5-tiny)
# to forecast equity returns and optimize portfolio allocation
# based on predicted Sharpe ratios.
# Source: HandsOnAITradingBook, Section 06, Example 18


class ChronosFoundationAlgorithm(QCAlgorithm):
    """
    Amazon Chronos Foundation Model for Portfolio Allocation.

    This strategy uses the Chronos time-series foundation model
    to forecast future returns of a universe of equities, then
    allocates capital to maximize expected Sharpe ratio.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 18

    How it works:
    1. Select top equities by market cap
    2. Collect trailing daily returns for each equity
    3. Use Chronos model to forecast future returns
    4. Estimate expected return and volatility per asset
    5. Allocate weights proportional to Sharpe ratio
    6. Monthly rebalance

    Parameters:
    - forecast_horizon: Number of days to forecast (default: 20)
    - lookback_days: Historical window for model input (default: 60)
    - universe_size: Number of equities in universe (default: 10)
    """

    def initialize(self):
        self.set_start_date(2019, 1, 1)
        self.set_end_date(2026, 1, 1)
        self.set_cash(100_000)

        # Model parameters
        self._forecast_horizon = self.get_parameter(
            'forecast_horizon', 20
        )
        self._lookback_days = self.get_parameter(
            'lookback_days', 60
        )
        self._universe_size = self.get_parameter(
            'universe_size', 10
        )
        self._min_weight = 0.05
        self._max_weight = 0.25

        # Load Chronos model
        self._pipeline = None
        self._model_loaded = False
        self._load_model()

        # Universe selection
        self.universe_settings.data_normalization_mode = (
            DataNormalizationMode.RAW
        )
        schedule_symbol = Symbol.create(
            "SPY", SecurityType.EQUITY, Market.USA
        )
        date_rule = self.date_rules.month_start(schedule_symbol)
        self.universe_settings.schedule.on(date_rule)
        self._universe = self.add_universe(self._select_assets)

        # Monthly rebalance
        self.schedule.on(
            date_rule,
            self.time_rules.after_market_open(schedule_symbol, 30),
            self._trade
        )

        # Storage
        self._tradable_securities = []

    def _load_model(self):
        """Load Chronos foundation model."""
        try:
            from chronos import ChronosPipeline
            import torch

            self._pipeline = ChronosPipeline.from_pretrained(
                "amazon/chronos-t5-tiny",
                device_map="auto",
                torch_dtype=torch.float32,
            )
            self._model_loaded = True
            self.log("Chronos model loaded successfully")
        except Exception as e:
            self.log(
                f"Chronos model not available: {e}. "
                "Using momentum-based fallback."
            )
            self._model_loaded = False

    def _select_assets(self, fundamental):
        """Select largest equities by market cap."""
        sorted_by_mc = sorted(
            fundamental, key=lambda x: x.market_cap
        )
        return [
            x.symbol for x in sorted_by_mc[-self._universe_size:]
        ]

    def on_securities_changed(self, changes):
        """Track tradable securities."""
        self._tradable_securities = [
            s for s in changes.added_securities
        ]

    def _get_returns(self, symbol):
        """Get trailing daily returns for a symbol."""
        history = self.history(
            symbol, self._lookback_days + 5, Resolution.DAILY,
            data_normalization_mode=DataNormalizationMode.SCALED_RAW
        )
        if history.empty or 'close' not in history:
            return None

        if isinstance(history.index, pd.MultiIndex):
            history = history.loc[symbol]

        closes = history['close'].values
        if len(closes) < self._lookback_days:
            return None

        returns = np.diff(closes) / closes[:-1]
        return returns[-self._lookback_days:]

    def _forecast_chronos(self, returns):
        """
        Forecast future returns using Chronos model.

        Returns (expected_return, expected_volatility).
        """
        if not self._model_loaded or self._pipeline is None:
            return self._forecast_momentum(returns)

        try:
            import torch

            context = torch.tensor(returns, dtype=torch.float32)
            forecast = self._pipeline.predict(
                context,
                prediction_length=self._forecast_horizon
            )

            # Use median forecast for expected return
            median = forecast.median(dim=1).values.numpy()[0]
            expected_return = float(np.mean(median))
            expected_vol = float(np.std(median))

            if expected_vol == 0:
                expected_vol = 1e-6

            return expected_return, expected_vol
        except Exception:
            return self._forecast_momentum(returns)

    def _forecast_momentum(self, returns):
        """
        Momentum-based forecasting fallback.

        Uses trailing returns to estimate future performance.
        """
        if len(returns) < 20:
            return 0.0, 1.0

        # Short-term momentum (last 20 days)
        short_term = float(np.mean(returns[-20:]))
        # Medium-term (last 60 days)
        medium_term = float(np.mean(returns))
        # Volatility estimate
        vol = float(np.std(returns[-20:]))
        if vol == 0:
            vol = 1e-6

        # Blend short and medium-term signals
        expected_return = 0.6 * short_term + 0.4 * medium_term
        return expected_return * 252, vol * np.sqrt(252)

    def _trade(self):
        """Execute trades based on Chronos forecasts."""
        if len(self._tradable_securities) == 0:
            return

        # Get forecasts for all securities
        sharpe_estimates = {}
        for security in self._tradable_securities:
            symbol = security.symbol
            returns = self._get_returns(symbol)
            if returns is None:
                continue

            expected_ret, expected_vol = self._forecast_chronos(
                returns
            )
            if expected_vol > 0:
                sharpe_estimates[symbol] = (
                    expected_ret / expected_vol
                )

        if len(sharpe_estimates) == 0:
            return

        # Filter positive Sharpe estimates
        positive_sharpes = {
            k: v for k, v in sharpe_estimates.items() if v > 0
        }
        if len(positive_sharpes) == 0:
            for holding in self.portfolio.values():
                if holding.invested:
                    self.liquidate(holding.symbol)
            return

        # Normalize weights proportional to Sharpe ratio
        total_sharpe = sum(
            max(s, 0) for s in positive_sharpes.values()
        )
        if total_sharpe == 0:
            return

        targets = []
        for symbol, sharpe in positive_sharpes.items():
            weight = float(max(sharpe, 0) / total_sharpe)
            weight = max(self._min_weight, min(self._max_weight, weight))
            targets.append(PortfolioTarget(symbol, weight))

        # Renormalize if weights exceed 1.0
        total_weight = sum(
            t.quantity for t in targets
        )
        if total_weight > 1.0:
            targets = [
                PortfolioTarget(
                    t.symbol, float(t.quantity / total_weight)
                )
                for t in targets
            ]

        self.set_holdings(targets, True)

        # Plot metrics
        self.plot(
            'Chronos', 'Assets Traded', len(targets)
        )
        if positive_sharpes:
            avg_sharpe = float(np.mean(list(
                positive_sharpes.values()
            )))
            self.plot('Chronos', 'Avg Forecast Sharpe', avg_sharpe)
