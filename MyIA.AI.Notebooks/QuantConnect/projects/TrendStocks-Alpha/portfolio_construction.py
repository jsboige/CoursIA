# region imports
from AlgorithmImports import *
# endregion


class MultiStrategyPCM(PortfolioConstructionModel):
    """Multi-Strategy Portfolio Construction Model.

    Equal weight allocation among all active insights.

    Parameters:
    - rebalance: Rebalance frequency (Time.DAILY or Time.WEEKLY)
    - max_active_insights: Maximum number of active insights to consider (default 100)
    """

    def __init__(self, max_active_insights=100):
        super().__init__()
        self.max_active_insights = max_active_insights

    def create_targets(self, algorithm, insights):
        """Create portfolio targets from insights."""
        targets = []

        # Filter active insights
        active_insights = [i for i in insights if i.is_active and i.direction != InsightDirection.FLAT]

        if not active_insights:
            # Liquidate all if no active insights
            for portfolio_target in algorithm.portfolio.values():
                if portfolio_target.invested:
                    targets.append(PortfolioTarget(portfolio_target.symbol, 0))
            return targets

        # Equal weight allocation
        count = min(len(active_insights), self.max_active_insights)
        weight = 0.95 / count  # Use 95% of capital, keep 5% cash

        for insight in active_insights[:count]:
            # Calculate quantity from portfolio value and weight
            symbol = insight.symbol
            security = algorithm.securities[symbol]
            if security.price > 0:
                target_value = algorithm.portfolio.total_portfolio_value * weight
                quantity = target_value / security.price
                targets.append(PortfolioTarget(symbol, quantity))

        return targets

    def should_rebalance(self, algorithm, insights):
        """Determine if rebalancing is needed."""
        return True
