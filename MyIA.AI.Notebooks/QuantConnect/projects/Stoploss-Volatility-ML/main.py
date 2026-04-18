#region imports
from AlgorithmImports import *

from sklearn.linear_model import Lasso
# endregion


class StoplossVolatilityMLAlgorithm(QCAlgorithm):
    """
    ML-Based Stop Loss Using Historical Volatility and Drawdown Recovery.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 08

    Uses Lasso regression with 3 volatility factors to predict the
    weekly low return of KO, placing a stop-market order below the
    predicted low price.

    Factors: SPY realized vol, ATR, StdDev of returns.
    Label: Return from week-open to weekly-low price.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 3, 1)
        self.set_cash(100_000)

        self._security = self.add_equity(
            "KO", data_normalization_mode=DataNormalizationMode.RAW
        )
        self._symbol = self._security.symbol

        self._spy = self.add_equity(
            "SPY", data_normalization_mode=DataNormalizationMode.RAW
        ).symbol

        self._stop_loss_buffer = float(self.get_parameter(
            'stop_loss_buffer', 0.01
        ))

        self._factor_rows = []
        self._max_rows = 800

        period = 22 * int(self.get_parameter('indicator_lookback_months', 1))
        self._atr = AverageTrueRange(period, MovingAverageType.SIMPLE)
        self._std = StandardDeviation(period)
        self._spy_close_window = []
        self._vol_period = period

        self._trailing_bars = []
        self._trailing_max = 6

        self._warm_up()

        date_rule = self.date_rules.week_start(self._symbol)
        self.schedule.on(
            date_rule,
            self.time_rules.after_market_open(self._symbol, 2),
            self._enter
        )
        self.schedule.on(
            self.date_rules.week_end(self._symbol),
            self.time_rules.before_market_close(self._symbol, 5),
            self.liquidate
        )

        alpha = 10 ** (-int(self.get_parameter('alpha_exponent', 4)))
        self._model = Lasso(alpha=alpha)

    def _warm_up(self):
        self._consolidator = self.consolidate(
            self._symbol, Resolution.DAILY, self._consolidation_handler
        )

        warm_up_duration = timedelta(3 * 365) + timedelta(
            2 * max(self._atr.warm_up_period, self._std.warm_up_period)
        )

        spy_history = self.history(
            self._spy, warm_up_duration, Resolution.DAILY,
            data_normalization_mode=DataNormalizationMode.SCALED_RAW
        )
        if not spy_history.empty:
            if isinstance(spy_history.index, pd.MultiIndex):
                spy_history = spy_history.loc[self._spy]
            self._spy_close_window = list(
                spy_history['close'].values[-(self._vol_period + 1):]
            )

        trade_bars = self.history[TradeBar](
            self._symbol, warm_up_duration, Resolution.DAILY,
            data_normalization_mode=DataNormalizationMode.SCALED_RAW
        )
        for trade_bar in trade_bars:
            self._consolidator.update(trade_bar)

    def _compute_spy_vol(self):
        n = min(len(self._spy_close_window), self._vol_period + 1)
        if n < 3:
            return 0.0
        closes = self._spy_close_window[-n:]
        returns = np.diff(closes) / closes[:-1]
        return float(np.std(returns))

    def _consolidation_handler(self, consolidated_bar):
        t = consolidated_bar.end_time

        self._atr.update(consolidated_bar)
        self._std.update(t, consolidated_bar.close)

        spy_sec = self.securities.get(self._spy)
        if spy_sec and spy_sec.has_data:
            self._spy_close_window.append(float(spy_sec.close))
            max_len = self._vol_period + 2
            if len(self._spy_close_window) > max_len:
                self._spy_close_window = self._spy_close_window[-max_len:]

        spy_vol = self._compute_spy_vol()

        if self._atr.is_ready and self._std.is_ready:
            self._factor_rows.append({
                'time': t,
                'spy_vol': spy_vol,
                'atr': float(self._atr.current.value),
                'std': float(self._std.current.value),
            })
            if len(self._factor_rows) > self._max_rows:
                self._factor_rows = self._factor_rows[-self._max_rows:]

        self._trailing_bars.append({
            'time': t,
            'open': consolidated_bar.open,
            'low': consolidated_bar.low,
        })
        if len(self._trailing_bars) > self._trailing_max:
            self._trailing_bars = self._trailing_bars[1:]

        if len(self._trailing_bars) < self._trailing_max:
            return

        trade_open_time = self._trailing_bars[0]['time'] - timedelta(1)
        factor_times = [
            r for r in self._factor_rows
            if r['time'] <= trade_open_time
        ]
        if not factor_times:
            return
        target = factor_times[-1]

        open_price = self._trailing_bars[0]['open']
        low_price = min(b['low'] for b in self._trailing_bars)
        return_ = (low_price - open_price) / open_price
        target['weekly_low_return'] = return_

    def on_data(self, data):
        pass

    def _get_training_data(self):
        rows = [r for r in self._factor_rows if 'weekly_low_return' in r]
        if len(rows) < 10:
            return None, None
        X = np.array([[r['spy_vol'], r['atr'], r['std']] for r in rows])
        y = np.array([r['weekly_low_return'] for r in rows])
        return X, y

    def _enter(self):
        X, y = self._get_training_data()
        if X is None:
            return

        self._model.fit(X, y)

        if not self._factor_rows:
            return
        latest = self._factor_rows[-1]
        features = np.array([
            [latest['spy_vol'], latest['atr'], latest['std']]
        ])
        prediction = self._model.predict(features)[0]
        predicted_low_price = self._security.open * (1 + prediction)
        self.plot("Stop Loss", "Distance", 1 + prediction)

        quantity = self.calculate_order_quantity(self._symbol, 1)
        self.market_order(self._symbol, quantity)

        stop_price = round(
            predicted_low_price - self._stop_loss_buffer, 2
        )
        self.stop_market_order(self._symbol, -quantity, stop_price)
