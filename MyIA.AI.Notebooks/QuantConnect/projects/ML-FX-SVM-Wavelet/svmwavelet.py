#region imports
from AlgorithmImports import *

import pywt
from sklearn.svm import SVR
from sklearn.model_selection import GridSearchCV
# endregion


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
