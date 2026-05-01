from AlgorithmImports import *


class VWAPExecutionModel(ExecutionModel):
    """
    VWAP-style Execution Model.

    Splits large orders into smaller chunks distributed throughout the day.
    Uses a simple time-weighted approach: divide the target order into
    num_slices equal parts, executed every slice_interval minutes.
    """

    def __init__(self, num_slices=4, slice_interval_minutes=15):
        super().__init__()
        self.num_slices = num_slices
        self.slice_interval = timedelta(minutes=slice_interval_minutes)
        self.pending_orders = {}
        self.next_slice_time = {}

    def execute(self, algorithm, targets):
        for target in targets:
            symbol = target.symbol
            current_qty = algorithm.portfolio.get(symbol, None)

            if current_qty is None:
                continue

            current_holdings = current_qty.quantity if current_qty else 0
            target_qty = target.quantity

            delta = target_qty - current_holdings
            if abs(delta) < 1:
                # Already at target
                self.pending_orders.pop(symbol, None)
                self.next_slice_time.pop(symbol, None)
                continue

            # Store the target delta for slicing
            self.pending_orders[symbol] = delta
            if symbol not in self.next_slice_time:
                self.next_slice_time[symbol] = algorithm.time

            # Execute first slice immediately
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
