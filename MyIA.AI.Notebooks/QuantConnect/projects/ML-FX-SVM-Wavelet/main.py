#region imports
from AlgorithmImports import *

import pywt
from sklearn.svm import SVR
from sklearn.model_selection import GridSearchCV
# endregion
# Hands-On AI Trading - Ex05: FX SVM Wavelet Forecasting
# Combines Wavelet decomposition with Support Vector Regression to
# forecast Forex pair prices. Decomposes prices into components,
# denoises via thresholding, forecasts each with SVR, then recombines.
# Source: HandsOnAITradingBook, Section 06, Example 05
#
# Note: SVMWavelet class inlined from svmwavelet.py for QC Cloud
# compatibility (single-file deployment).


class SVMWavelet:
    """
    SVM-Wavelet Forecasting Helper.

    Decomposes price data using Discrete Wavelet Transform (DWT),
    denoises each component via thresholding, forecasts each component
    with Support Vector Regression (SVR), and recombines for the
    aggregate prediction.

    Wavelet: sym10 (Symlets, length 20)
    Minimum data length: 152 points (for 3 decomposition levels)
    """

    def forecast(self, data):
        """
        Forecast 1 time-step ahead using Wavelet decomposition + SVR.

        Args:
            data: 1-D numpy array of prices (min length 152 for sym10)

        Returns:
            float: Aggregate forecast value 1 step into the future
        """
        w = pywt.Wavelet('sym10')
        threshold = 0.5

        coeffs = pywt.wavedec(data, w)

        for i in range(len(coeffs)):
            if i > 0:
                coeffs[i] = pywt.threshold(
                    coeffs[i], threshold * max(coeffs[i])
                )
            forecasted = self._svm_forecast(coeffs[i])
            coeffs[i] = np.roll(coeffs[i], -1)
            coeffs[i][-1] = forecasted

        datarec = pywt.waverec(coeffs, w)
        return datarec[-1]

    def _svm_forecast(self, data, sample_size=10):
        """Fit SVR on partitioned data and predict next value."""
        x, y = self._partition_array(data, size=sample_size)

        gsc = GridSearchCV(
            SVR(),
            {
                'C': [.05, .1, .5, 1, 5, 10],
                'epsilon': [0.001, 0.005, 0.01, 0.05, 0.1]
            },
            scoring='neg_mean_squared_error'
        )

        model = gsc.fit(x, y).best_estimator_
        return model.predict(data[np.newaxis, -sample_size:])[0]

    def _partition_array(self, arr, size=None, splits=None):
        """Partition 1-D array in rolling fashion (by size) or chunks."""
        arrs = []
        values = []

        if not (bool(size is None) ^ bool(splits is None)):
            raise ValueError('Size XOR Splits should not be None')

        if size:
            arrs = [arr[i:i + size] for i in range(len(arr) - size)]
            values = [arr[i] for i in range(size, len(arr))]

        elif splits:
            size = len(arr) // splits
            if len(arr) % size == 0:
                arrs = [
                    arr[i:i + size]
                    for i in range(size - 1, len(arr) - 1, size)
                ]
                values = [
                    arr[i] for i in range(
                        2 * size - 1, len(arr), size
                    )
                ]
            else:
                arrs = [
                    arr[i:i + size]
                    for i in range(
                        len(arr) % size - 1, len(arr) - 1, size
                    )
                ]
                values = [
                    arr[i] for i in range(
                        len(arr) % size + size - 1, len(arr), size
                    )
                ]

        return np.array(arrs), np.array(values)


class SVMWaveletForecastingAlgorithm(QCAlgorithm):
    """
    FX SVM-Wavelet Forecasting Strategy.

    This algorithm combines Support Vector Machines (SVM) and Wavelets
    to forecast the future price of Forex pairs:

    1. Decompose historical closing prices using Wavelet decomposition
    2. Denoise each component using thresholding
    3. Apply SVR to forecast one time-step ahead for each component
    4. Recombine components for the aggregate forecast
    5. Trade based on forecast vs current price deviation

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 05

    Parameters:
    - period: Rolling window size (default: 152, min for sym10 wavelet)
    - leverage: Forex leverage multiplier (default: 20)
    - weight_threshold: Minimum deviation to trigger trade (default: 0.005)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 1, 1)
        self.set_cash(1_000_000)
        self.set_brokerage_model(BrokerageName.OANDA_BROKERAGE, AccountType.MARGIN)

        period = self.get_parameter("period", 152)
        self._leverage = self.get_parameter("leverage", 20)
        self._weight_threshold = self.get_parameter(
            "weight_threshold", 0.005
        )

        self.set_benchmark(
            Symbol.create("EURUSD", SecurityType.FOREX, Market.FXCM)
        )
        self.settings.minimum_order_margin_portfolio_percentage = 0

        for ticker in ["EURJPY", "GBPUSD", "AUDCAD", "NZDCHF"]:
            security = self.add_forex(ticker, leverage=self._leverage)
            security.window = RollingWindow[float](period)

            consolidator = self.consolidate(
                security.symbol, Resolution.DAILY, TickType.QUOTE,
                self._consolidation_handler
            )

            history = self.history[QuoteBar](
                security.symbol, period, Resolution.DAILY
            )
            for bar in history:
                consolidator.update(bar)

        self._wavelet = SVMWavelet()

    def _consolidation_handler(self, bar):
        """Update rolling window and generate trading signals."""
        security = self.securities[bar.symbol]
        security.window.add(bar.close)

        if self.is_warming_up:
            return

        prices = np.array(list(security.window))[::-1]
        forecasted_value = self._wavelet.forecast(prices)
        weight = (forecasted_value / bar.close) - 1

        if abs(weight) > self._weight_threshold:
            self.set_holdings(security.symbol, weight * self._leverage)

        ticker = security.symbol.value
        self.plot(ticker, "Price", float(bar.close))
        self.plot(ticker, "Forecast", float(forecasted_value))

    def on_data(self, data):
        pass
