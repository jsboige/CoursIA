from AlgorithmImports import *


class RiskParityPCM(PortfolioConstructionModel):
    """
    Equal-Weight PCM with exposure cap.

    Distributes max_exposure equally across all UP insights.
    """

    def __init__(self, rebalance=timedelta(days=7), max_exposure=0.80, sector_cap=0.35):
        super().__init__()
        self.max_exposure = max_exposure
        self.sector_cap = sector_cap
        self.set_rebalancing_func(lambda dt: dt + rebalance)

    def determine_target_percent(self, active_insights):
        if not active_insights:
            return {}

        active = [i for i in active_insights if i.direction != InsightDirection.FLAT]
        flat = [i for i in active_insights if i.direction == InsightDirection.FLAT]

        result = {}
        for insight in flat:
            result[insight] = 0

        if not active:
            return result

        per_weight = min(
            self.max_exposure / len(active),
            self.sector_cap
        )
        for insight in active:
            result[insight] = insight.direction * per_weight

        return result
