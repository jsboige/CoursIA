#region imports
from AlgorithmImports import *

from keras.saving import load_model
from tensorflow.keras.layers import Input, Conv1D, Dense, Flatten
from tensorflow.keras import Model
from tensorflow.keras.losses import BinaryCrossentropy
# endregion
# Hands-On AI Trading - Ex17: Head and Shoulders Pattern Matching with CNN
# Loads a pre-trained Keras CNN model from the Object Store to detect
# head-and-shoulders patterns in USDCAD Forex prices. Scans trailing
# windows at multiple scales, downsamples to 25 points, and classifies.
# Source: HandsOnAITradingBook, Section 06, Example 17
#
# If `head-and-shoulders-model.keras` is absent from the Object Store,
# the algorithm trains a small CNN on synthetic patterns at startup.
# Run research.ipynb to train a richer model and persist it.


def downsample(values, num_points=25):
    """Downsample a price series to a fixed number of points."""
    if num_points == len(values):
        return values

    adj_values = []
    duplicates = int(2 * len(values) / num_points)
    if duplicates > 0:
        for x in values:
            for _ in range(duplicates):
                adj_values.append(x)
    else:
        adj_values = values

    num_steps = num_points - 2
    step_size = int(len(adj_values) / num_steps)

    smoothed_data = [adj_values[0]]
    for i in range(num_steps):
        start_idx = i * step_size
        if i == num_steps - 1:
            end_idx = len(adj_values) - 1
        else:
            end_idx = (i + 1) * step_size - 1
        segment = np.array(adj_values[start_idx:end_idx + 1])
        avg = sum(segment) / len(segment)
        smoothed_data.append(avg)

    smoothed_data.append(adj_values[-1])
    return np.array(smoothed_data)


class CNNPatternDetectionAlgorithm(QCAlgorithm):
    """
    Head and Shoulders Pattern Detection with CNN.

    This algorithm uses a pre-trained Convolutional Neural Network to
    detect the head-and-shoulders technical trading pattern in Forex
    price data.

    Workflow:
    1. Load pre-trained Keras model from Object Store
    2. Track trailing USDCAD daily prices
    3. Scan multiple window sizes (25 to 100, step 10)
    4. Downsample each window to 25 points and standardize
    5. Classify with CNN (head-and-shoulders or not)
    6. Enter short position when pattern detected with >50% confidence

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 17

    NOTE: Run research.ipynb first to train and save the CNN model.

    Parameters:
    - max_size: Maximum trailing window length (default: 100)
    - step_size: Step between window sizes (default: 10)
    - confidence_threshold: Minimum CNN confidence to trade (default: 0.5)
    - holding_period: Days to hold position after pattern detection (default: 10)
    """

    _min_size = 25

    def initialize(self):
        self.set_start_date(2019, 1, 1)
        self.set_end_date(2024, 1, 1)
        self.set_cash(100_000)

        self._security = self.add_forex("USDCAD", Resolution.DAILY)
        self._symbol = self._security.symbol

        self._max_size = self.get_parameter('max_size', 100)
        self._step_size = self.get_parameter('step_size', 10)
        self._confidence_threshold = self.get_parameter(
            'confidence_threshold', 0.5
        )
        self._holding_period = timedelta(
            self.get_parameter('holding_period', 10)
        )

        model_key = "head-and-shoulders-model.keras"
        if self.object_store.contains_key(model_key):
            self._model = load_model(
                self.object_store.get_file_path(model_key)
            )
        else:
            self.log(
                "Object Store model missing, training synthetic CNN"
            )
            self._model = self._train_synthetic_model()
        self._trailing_prices = pd.Series()
        self._liquidation_quantities = []

        chart = Chart('HS Patterns Detected')
        self.add_chart(chart)
        series = [
            Series('USDCAD Price', SeriesType.LINE, 0),
            Series('End of Pattern Detected', SeriesType.SCATTER, 0),
            Series("Window Length", SeriesType.SCATTER, 1)
        ]
        for s in series:
            chart.add_series(s)

    def on_data(self, data):
        if self._symbol not in data:
            return

        t = self.time
        price = data[self._symbol].close
        self.plot('HS Patterns Detected', 'USDCAD Price', float(price))

        self._trailing_prices.loc[t] = price
        self._trailing_prices = self._trailing_prices.iloc[-self._max_size:]

        quantity = 0
        self._window_lengths_detected = []

        for size in range(
            self._min_size, self._max_size + 1, self._step_size
        ):
            if len(self._trailing_prices) < size:
                continue

            window_trailing_prices = self._trailing_prices.iloc[-size:]
            low_res_window = downsample(window_trailing_prices.values)

            factors = np.array(
                (
                    (low_res_window - low_res_window.mean())
                    / low_res_window.std()
                ).reshape(1, self._min_size, 1)
            )

            prediction = self._model.predict(factors, verbose=0)[0][0]
            if prediction > self._confidence_threshold:
                self.log(
                    f"{t}: Pattern detected between "
                    f"{window_trailing_prices.index[0]} and "
                    f"{window_trailing_prices.index[-1]} with "
                    f"{round(float(prediction) * 100, 1)}% confidence."
                )
                self.plot(
                    "HS Patterns Detected",
                    'End of Pattern Detected', float(price)
                )
                self._window_lengths_detected.append(size)
                quantity -= 10_000

        for i in range(len(self._window_lengths_detected)):
            t_plot = self.time + timedelta(seconds=i)
            self.schedule.on(
                self.date_rules.on(
                    t_plot.year, t_plot.month, t_plot.day
                ),
                self.time_rules.at(t_plot.hour, t_plot.minute, t_plot.second),
                lambda: self.plot(
                    "HS Patterns Detected", "Window Length",
                    self._window_lengths_detected.pop(0)
                )
            )

        if quantity:
            self._cad_before_sell = self.portfolio.cash_book['CAD'].amount
            self.market_order(self._symbol, quantity)
            t_exit = t + self._holding_period
            self.schedule.on(
                self.date_rules.on(
                    t_exit.year, t_exit.month, t_exit.day
                ),
                self.time_rules.at(t_exit.hour, t_exit.minute),
                self._liquidate_position
            )

    def _liquidate_position(self):
        """Close position after holding period."""
        quantity = round(
            self._liquidation_quantities.pop(0) / self._security.ask_price
        )
        if quantity:
            self.market_order(self._symbol, quantity)

    def on_order_event(self, order_event):
        """Track CAD amount traded for correct liquidation."""
        if (order_event.status == OrderStatus.FILLED and
                order_event.direction == OrderDirection.SELL):
            self._liquidation_quantities.append(
                self.portfolio.cash_book['CAD'].amount
                - self._cad_before_sell
            )

    def _train_synthetic_model(self):
        """Train a small CNN on synthetic HS vs random-walk patterns.

        Used when the pre-trained model is not present in Object Store.
        Same architecture and training data generation as research.ipynb.
        """
        n_samples = 2000
        n_points = self._min_size
        np.random.seed(0)

        def gen_hs():
            x = np.linspace(0, 1, n_points)
            pattern = (
                0.3 * np.exp(-((x - 0.2) ** 2) / 0.01)
                + 0.5 * np.exp(-((x - 0.5) ** 2) / 0.015)
                + 0.3 * np.exp(-((x - 0.8) ** 2) / 0.01)
            )
            return pattern + np.random.normal(0, 0.01, n_points)

        def gen_rw():
            return np.cumsum(np.random.normal(0, 0.02, n_points))

        X = []
        y = []
        for _ in range(n_samples // 2):
            hs = gen_hs()
            X.append(((hs - hs.mean()) / hs.std()).reshape(n_points, 1))
            y.append(1)
            rw = gen_rw()
            X.append(((rw - rw.mean()) / rw.std()).reshape(n_points, 1))
            y.append(0)
        X = np.array(X)
        y = np.array(y)

        inputs = Input(shape=(n_points, 1))
        x = Conv1D(16, 3, activation='relu')(inputs)
        x = Conv1D(32, 3, activation='relu')(x)
        x = Flatten()(x)
        x = Dense(32, activation='relu')(x)
        outputs = Dense(1, activation='sigmoid')(x)

        model = Model(inputs=inputs, outputs=outputs)
        model.compile(
            optimizer='adam',
            loss=BinaryCrossentropy(),
            metrics=['accuracy']
        )
        model.fit(X, y, epochs=20, batch_size=32, verbose=0)
        return model
