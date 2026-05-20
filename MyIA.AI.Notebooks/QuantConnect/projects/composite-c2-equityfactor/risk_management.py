from AlgorithmImports import *


class SectorCapRiskModel(RiskManagementModel):
    """
    Risk Management: Portfolio drawdown cap + trailing stops.

    - Portfolio-level drawdown circuit breaker (flatten all at max_dd)
    - Trailing stop per position at trail_pct
    """

    def __init__(self, max_sector_pct=0.30, max_beta=1.1, trail_pct=0.06):
        super().__init__()
        self.max_sector_pct = max_sector_pct
        self.max_beta = max_beta
        self.trail_pct = trail_pct
        self.peak_values = {}
        self.portfolio_peak = 0

    def manage_risk(self, algorithm, targets):
        risk_orders = []

        # Portfolio-level drawdown check
        portfolio_value = algorithm.portfolio.total_portfolio_value
        if portfolio_value > self.portfolio_peak:
            self.portfolio_peak = portfolio_value

        if self.portfolio_peak > 0:
            dd = (self.portfolio_peak - portfolio_value) / self.portfolio_peak
            if dd > 0.18:
                algorithm.log(f"RISK: Portfolio DD {dd:.1%} > 18%, flattening")
                for kvp in algorithm.portfolio:
                    holding = kvp.value
                    if holding.invested:
                        risk_orders.append(PortfolioTarget(kvp.key, 0))
                self.portfolio_peak = portfolio_value
                self.peak_values.clear()
                return risk_orders

        # Trailing stop check
        for kvp in algorithm.portfolio:
            holding = kvp.value
            if not holding.invested:
                continue

            symbol = kvp.key
            current_price = holding.price

            if symbol not in self.peak_values:
                self.peak_values[symbol] = current_price
            self.peak_values[symbol] = max(self.peak_values[symbol], current_price)
            peak = self.peak_values[symbol]

            if holding.is_long:
                trail = peak * (1 - self.trail_pct)
                if current_price < trail:
                    risk_orders.append(PortfolioTarget(symbol, 0))
                    self.peak_values.pop(symbol, None)
            elif holding.is_short:
                trail = peak * (1 + self.trail_pct)
                if current_price > trail:
                    risk_orders.append(PortfolioTarget(symbol, 0))
                    self.peak_values.pop(symbol, None)

        return risk_orders

    def on_securities_changed(self, algorithm, changes):
        for security in changes.removed_securities:
            self.peak_values.pop(security.symbol, None)
