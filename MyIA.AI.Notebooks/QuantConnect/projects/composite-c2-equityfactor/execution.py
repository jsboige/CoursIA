from AlgorithmImports import *


class TWAPExecutionModel(ExecutionModel):
    """
    TWAP Execution Model.

    Time-weighted average price: splits orders into equal slices
    executed at regular time intervals throughout the day.
    """

    def __init__(self, num_slices=6, slice_interval_minutes=10):
        super().__init__()
        self.num_slices = num_slices
        self.slice_interval = timedelta(minutes=slice_interval_minutes)
        self.pending_orders = {}
        self.next_slice_time = {}

    def execute(self, algorithm, targets):
        for target in targets:
            symbol = target.symbol
            holding = algorithm.portfolio.get(symbol, None)

            if holding is None:
                continue

            current_qty = holding.quantity if holding else 0
            target_qty = target.quantity
            delta = target_qty - current_qty

            if abs(delta) < 1:
                self.pending_orders.pop(symbol, None)
                self.next_slice_time.pop(symbol, None)
                continue

            # Execute in slices
            self.pending_orders[symbol] = delta
            if symbol not in self.next_slice_time:
                self.next_slice_time[symbol] = algorithm.time

            slice_size = int(delta / self.num_slices)
            if abs(slice_size) >= 1:
                algorithm.market_order(symbol, slice_size)
                remaining = delta - slice_size
                if abs(remaining) < 1:
                    self.pending_orders.pop(symbol, None)
                    self.next_slice_time.pop(symbol, None)
                else:
                    self.pending_orders[symbol] = remaining
                    self.next_slice_time[symbol] = algorithm.time + self.slice_interval

    def on_order_event(self, algorithm, order_event):
        if order_event.status == OrderStatus.FILLED:
            symbol = order_event.symbol
            if symbol in self.pending_orders:
                remaining = self.pending_orders[symbol]
                if abs(remaining) < 1:
                    self.pending_orders.pop(symbol, None)
                    self.next_slice_time.pop(symbol, None)
