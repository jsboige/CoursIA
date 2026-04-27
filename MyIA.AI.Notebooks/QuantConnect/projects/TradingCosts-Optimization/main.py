#region imports
from AlgorithmImports import *

from sklearn.tree import DecisionTreeRegressor
# endregion


class TradeCostEstimationAlgorithm(QCAlgorithm):
    """
    Trading Costs Optimization with Decision Tree Regression.

    This strategy demonstrates how to use machine learning to reduce
    trading costs by predicting when execution costs are likely to be
    lower than average.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 12

    How it works:
    1. Buy BTCUSDC at midnight each day
    2. Instead of selling at 1 AM (benchmark), hold until ML predicts
       lower execution costs
    3. Predict costs using DecisionTreeRegressor with market factors
    4. Only exit when predicted cost-per-dollar is below rolling average

    Factors:
    - Absolute order quantity
    - Average True Range (14-day)
    - Average daily volume (10-day)
    - Spread percent (ask - bid) / bid
    - Top of book size in dollars

    Parameters:
    - benchmark: If True, exit at 1 AM without ML (default: False)
    - cost_sma_period: SMA window for cost averaging (default: 10)
    - atr_period: ATR lookback (default: 14)
    - sma_period: Volume SMA lookback (default: 10)
    - lookback_window: Training data window (default: 100)
    """

    def initialize(self):
        self.set_start_date(2023, 1, 1)
        self.set_end_date(2024, 1, 1)
        self.set_cash('USDC', 10_000_000)

        self.settings.minimum_order_margin_portfolio_percentage = 0

        self._benchmark = self.get_parameter('benchmark', False)
        self._scan_for_exit = False

        # Add BTC/USDC pair
        self._security = self.add_crypto(
            "BTCUSDC", market=Market.BYBIT
        )
        self._security.set_slippage_model(SpreadSlippageModel())
        self._symbol = self._security.symbol

        # Schedule daily entry/exit
        date_rule = self.date_rules.every_day()
        self.schedule.on(
            date_rule, self.time_rules.at(0, 0), self._entry
        )
        self.schedule.on(
            date_rule, self.time_rules.at(1, 0), self._exit_schedule
        )

        self._total_costs = 0
        self._quantity = 10
        self._costs = pd.Series(dtype=float)
        self._cost_sma = SimpleMovingAverage(
            self.get_parameter('cost_sma_period', 10)
        )
        self._order_fills = pd.DataFrame(
            columns=['fill_price', 'quantity', 'cost', 'tag']
        )

        if not self._benchmark:
            self._model = None
            self.enable_automatic_indicator_warm_up = True
            self._atr = self.atr(
                self._symbol,
                self.get_parameter('atr_period', 14),
                resolution=Resolution.DAILY
            )
            self._sma = self.sma(
                self._symbol,
                self.get_parameter('sma_period', 10),
                Resolution.DAILY,
                Field.VOLUME
            )
            # Monthly model retraining
            self.train(
                self.date_rules.month_start(),
                self.time_rules.at(0, 0),
                self._train_model
            )
            self._lookback_window = self.get_parameter(
                'lookback_window', 100
            )
            self._factors = pd.DataFrame(
                columns=[
                    'abs_order_quantity', 'atr', 'avg_daily_volume',
                    'spread_pct', 'top_of_book_size'
                ]
            )

    def _entry(self):
        """Buy BTC at midnight, only if not already holding."""
        if self.portfolio[self._symbol].quantity > 0:
            return
        self.market_order(self._symbol, self._quantity)

    def _exit_schedule(self):
        """Handle exit: benchmark mode exits immediately, ML mode scans."""
        if self._benchmark:
            bid = self._security.bid_price
            ask = self._security.ask_price
            self.liquidate(tag=f"Bid: {bid}; Ask: {ask}")
            return
        self._scan_for_exit = True

    def _train_model(self):
        """Retrain DecisionTreeRegressor on accumulated cost data."""
        if self._factors.shape[0] < self._lookback_window:
            return
        if self._model is None:
            self._model = DecisionTreeRegressor(
                max_depth=5, random_state=0
            )
        # Align factors and costs on common indices
        common_idx = self._factors.index.intersection(self._costs.index)
        if len(common_idx) < 20:
            return
        self._model.fit(
            self._factors.loc[common_idx],
            self._costs.loc[common_idx]
        )

    def _trim_samples(self):
        """Keep only recent samples within lookback window."""
        self._factors = self._factors.iloc[-self._lookback_window:]
        self._costs = self._costs.iloc[-self._lookback_window:]

    def on_data(self, data):
        """Scan for optimal exit timing based on ML predictions."""
        if not self._scan_for_exit:
            return

        bid = self._security.bid_price
        ask = self._security.ask_price
        current_factors = [
            abs(self._quantity),
            self._atr.current.value,
            self._sma.current.value,
            (ask - bid) / bid,
            self._security.ask_size * ask
        ]

        tag = "Hit time limit"
        if self._model is None:
            tag = "ML model is not ready"
        elif data.time.time() < time(23, 59):
            # Predict trading cost
            predicted_costs = self._model.predict(
                [current_factors]
            )[0]
            dollar_volume = self._quantity * bid
            predicted_costs_per_dollar = (
                predicted_costs / dollar_volume
            )

            # Wait until predicted costs are below average
            if predicted_costs_per_dollar >= (
                    self._cost_sma.current.value):
                return
            tag = (
                f'Predicted: {predicted_costs_per_dollar}; '
                f'SMA: {self._cost_sma.current.value}'
            )

            # Plot predictions
            self.plot("Costs", "Predicted", predicted_costs)
            self.plot(
                "Costs Per Dollar", "Predicted",
                predicted_costs_per_dollar
            )

        self.plot(
            "Model Readiness", "IsReady",
            int(self._model is not None)
        )

        # Execute exit
        self.market_order(
            self._symbol, -self._quantity, tag=tag
        )
        self._factors.loc[self.time] = current_factors
        self._scan_for_exit = False
        self._trim_samples()

    def on_order_event(self, order_event):
        """Track actual trading costs from fill events."""
        if order_event.status == OrderStatus.FILLED:
            if order_event.quantity > 0:
                return
            t = self.time
            fill_price = order_event.fill_price
            dollar_volume = self._quantity * fill_price
            slippage_per_share = (
                self._security.bid_price - fill_price
            )
            cost = (
                order_event.order_fee.value.amount
                + slippage_per_share * self._quantity
            )
            self._total_costs += cost
            self._cost_sma.update(t, cost / dollar_volume)
            self._costs.loc[t] = cost
            self.plot("Costs", "Actual", cost)
            self.plot("Cumulative Costs", "Actual", self._total_costs)
            self.plot("Samples", "Count", len(self._costs))
            self.plot(
                "Costs Per Dollar", "Actual", cost / dollar_volume
            )
            if self._cost_sma.is_ready:
                self.plot(
                    "Costs Per Dollar", "SMA(Actual)",
                    self._cost_sma.current.value
                )
            self._order_fills.loc[t] = (
                fill_price, order_event.quantity, cost,
                order_event.ticket.tag
            )

    def on_end_of_algorithm(self):
        """Save order fills to object store for analysis."""
        key = (
            "benchmark" if self._benchmark else "candidate"
        ) + "_order_fills"
        self._order_fills.to_csv(
            self.object_store.get_file_path(key)
        )


class SpreadSlippageModel:
    """Simple spread-based slippage model for crypto market orders."""

    def get_slippage_approximation(self, asset, order):
        return (asset.ask_price - asset.bid_price) / 2
