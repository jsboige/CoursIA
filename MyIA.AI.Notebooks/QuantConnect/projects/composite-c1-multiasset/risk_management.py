from AlgorithmImports import *


class DrawdownCapRiskModel(RiskManagementModel):
    """
    Risk Management: Drawdown cap with trailing stop.

    - Closes position if unrealized drawdown exceeds max_drawdown (default 8%).
    - Trailing stop at trail_pct (default 5%) from peak value since entry.
    """

    def __init__(self, max_drawdown=0.08, trail_pct=0.05):
        super().__init__()
        self.max_drawdown = max_drawdown
        self.trail_pct = trail_pct
        self.peak_values = {}

    def manage_risk(self, algorithm, targets):
        risk_orders = []

        for kvp in algorithm.portfolio:
            holding = kvp.value
            if not holding.invested:
                continue

            symbol = kvp.key
            entry_price = holding.average_price
            current_price = holding.price

            # Track peak
            if symbol not in self.peak_values:
                self.peak_values[symbol] = current_price
            self.peak_values[symbol] = max(self.peak_values[symbol], current_price)

            peak = self.peak_values[symbol]

            # Drawdown from peak
            drawdown = (peak - current_price) / peak if holding.is_long else (current_price - peak) / peak

            if drawdown >= self.max_drawdown:
                algorithm.log(f"RISK: Drawdown cap hit for {symbol.value}: "
                             f"{drawdown:.2%} >= {self.max_drawdown:.2%}")
                risk_orders.append(PortfolioTarget(symbol, 0))
                self.peak_values.pop(symbol, None)
                continue

            # Trailing stop
            if holding.is_long:
                trail_level = peak * (1 - self.trail_pct)
                if current_price < trail_level:
                    algorithm.log(f"RISK: Trailing stop hit for {symbol.value}: "
                                 f"price {current_price:.2f} < trail {trail_level:.2f}")
                    risk_orders.append(PortfolioTarget(symbol, 0))
                    self.peak_values.pop(symbol, None)
            elif holding.is_short:
                trail_level = peak * (1 + self.trail_pct)
                if current_price > trail_level:
                    algorithm.log(f"RISK: Trailing stop hit for {symbol.value}: "
                                 f"price {current_price:.2f} > trail {trail_level:.2f}")
                    risk_orders.append(PortfolioTarget(symbol, 0))
                    self.peak_values.pop(symbol, None)

        return risk_orders

    def on_securities_changed(self, algorithm, changes):
        for security in changes.removed_securities:
            self.peak_values.pop(security.symbol, None)
