#region imports
from AlgorithmImports import *
from QuantConnect.Data.Custom.CBOE import CBOE

from sklearn.linear_model import Lasso
# endregion


class StoplossVolatilityMLAlgorithm(QCAlgorithm):
    """
    ML-Based Stop Loss Using Historical Volatility and Drawdown Recovery.

    This strategy uses a Lasso regression model to determine the optimal
    stop loss level based on market volatility factors.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 08

    How it works:
    1. Track weekly trading cycles (enter Monday, exit Friday)
    2. Collect factors: VIX, ATR, rolling std of returns
    3. Train Lasso to predict weekly low return (label)
    4. Place stop loss below predicted low price
    5. If stop isn't hit, liquidate at next week's open

    Factors:
    - VIX index value (market implied volatility)
    - Average True Range (price volatility)
    - Standard deviation of returns (statistical volatility)

    Label: Return from week-open to weekly-low price

    Parameters:
    - stop_loss_buffer: Dollar buffer below predicted low (default: 0.01)
    - indicator_lookback_months: Months for ATR/std (default: 1)
    - alpha_exponent: Lasso regularization (default: 4, alpha=1e-4)
    """

    def initialize(self):
        self.set_start_date(2018, 12, 31)
        self.set_end_date(2024, 4, 1)
        self.set_cash(100_000)

        self._security = self.add_equity(
            "KO", data_normalization_mode=DataNormalizationMode.RAW
        )
        self._symbol = self._security.symbol

        self._stop_loss_buffer = self.get_parameter(
            'stop_loss_buffer', 0.01
        )

        # DataFrame for ML factors and labels
        self._samples = pd.DataFrame(
            columns=['vix', 'atr', 'std', 'weekly_low_return'],
            dtype=float
        )
        self._samples_lookback = timedelta(3 * 365)

        # Define indicators as factors
        period = 22 * self.get_parameter('indicator_lookback_months', 1)
        self._vix = self.add_data(CBOE, "VIX", Resolution.DAILY).symbol
        self._atr = AverageTrueRange(period, MovingAverageType.SIMPLE)
        self._std = StandardDeviation(period)

        # Warm up VIX history
        vix_history = self.history(
            self._vix, self._samples_lookback, Resolution.DAILY
        )
        if not vix_history.empty:
            if isinstance(vix_history.index, pd.MultiIndex):
                vix_history = vix_history.loc[self._vix]
            self._samples['vix'] = vix_history['value']
        self._warm_up_samples()

        # Schedule weekly trading
        date_rule = self.date_rules.week_start(self._symbol)
        self.schedule.on(
            date_rule,
            self.time_rules.after_market_open(self._symbol, 2),
            self._enter
        )
        self.schedule.on(
            date_rule,
            self.time_rules.after_market_open(self._symbol, -30),
            self.liquidate
        )

        # Lasso model with configurable regularization
        alpha = 10 ** (-self.get_parameter('alpha_exponent', 4))
        self._model = Lasso(alpha=alpha)

    def on_splits(self, splits):
        """Re-warm indicators after stock splits."""
        if splits[self._symbol].type == SplitType.SPLIT_OCCURRED:
            self.subscription_manager.remove_consolidator(
                self._symbol, self._consolidator
            )
            self._warm_up_samples()

    def _warm_up_samples(self):
        """Warm up indicators and populate factor history."""
        self._consolidator = self.consolidate(
            self._symbol, Resolution.DAILY, self._consolidation_handler
        )

        # Reset indicators
        self._atr.reset()
        self._std.reset()

        # Clear factor history
        self._samples[['atr', 'std']] = np.nan
        self._trailing_bars = pd.DataFrame(columns=['open', 'low'])

        # Warm up with historical data
        warm_up_duration = self._samples_lookback + timedelta(
            2 * max(self._atr.warm_up_period, self._std.warm_up_period)
        )
        trade_bars = self.history[TradeBar](
            self._symbol, warm_up_duration, Resolution.DAILY,
            data_normalization_mode=DataNormalizationMode.SCALED_RAW
        )
        for trade_bar in trade_bars:
            self._consolidator.update(trade_bar)

    def _consolidation_handler(self, consolidated_bar):
        """Update indicators and track weekly labels from bar data."""
        t = consolidated_bar.end_time

        # Update indicators and factor history
        self._atr.update(consolidated_bar)
        self._std.update(t, consolidated_bar.close)
        if (self._atr.is_ready and
                self._std.is_ready and
                t in self._samples.index):
            self._samples.loc[t, 'atr'] = self._atr.current.value
            self._samples.loc[t, 'std'] = self._std.current.value
            self._samples = self._samples[
                self._samples.index >= t - self._samples_lookback
            ]

        # Track bars for weekly label calculation
        self._trailing_bars.loc[t, :] = [
            consolidated_bar.open, consolidated_bar.low
        ]
        if len(self._trailing_bars) < 6:
            return
        self._trailing_bars = self._trailing_bars.iloc[1:]

        # Calculate label: return from open to weekly low
        trade_open_time = self._trailing_bars.index[0] - timedelta(1)
        samples_timestamps = self._samples.index[
            self._samples.index <= trade_open_time
        ]
        if len(samples_timestamps) == 0:
            return
        samples_timestamp = samples_timestamps[-1]

        open_price = self._trailing_bars['open'][0]
        low_price = self._trailing_bars['low'].min()
        return_ = (low_price - open_price) / open_price
        self._samples.loc[samples_timestamp, 'weekly_low_return'] = return_

    def on_data(self, data):
        """Capture daily VIX values as factor."""
        if self._vix in data:
            self._samples.loc[data.time, "vix"] = data[self._vix].value

    def _enter(self):
        """Train model, predict weekly low, place stop loss."""
        training_samples = self._samples.dropna()
        if len(training_samples) < 10:
            return

        # Train Lasso on factors -> weekly low return
        self._model.fit(
            training_samples.iloc[:, :-1],
            training_samples.iloc[:, -1]
        )

        # Predict the return to this week's low
        features = self._samples.iloc[:, :-1].dropna()
        if features.empty:
            return
        prediction = self._model.predict([features.iloc[-1]])[0]
        predicted_low_price = self._security.open * (1 + prediction)
        self.plot("Stop Loss", "Distance", 1 + prediction)

        # Enter position
        quantity = self.calculate_order_quantity(self._symbol, 1)
        self.market_order(self._symbol, quantity)

        # Place stop loss slightly below predicted low
        stop_price = round(
            predicted_low_price - self._stop_loss_buffer, 2
        )
        self.stop_market_order(self._symbol, -quantity, stop_price)
