#region imports
from AlgorithmImports import *

from svmwavelet import SVMWavelet
# endregion
# Hands-On AI Trading - Ex05: FX SVM Wavelet Forecasting
# Combines Wavelet decomposition with Support Vector Regression to
# forecast Forex pair prices. Decomposes prices into components,
# denoises via thresholding, forecasts each with SVR, then recombines.
# Source: HandsOnAITradingBook, Section 06, Example 05


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
