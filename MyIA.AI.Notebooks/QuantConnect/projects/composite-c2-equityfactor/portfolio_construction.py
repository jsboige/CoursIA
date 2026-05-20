from AlgorithmImports import *


class MeanVariancePCM(PortfolioConstructionModel):
    """
    Score-Weighted PCM with position cap and total exposure scaling.

    Uses insight magnitudes for weighting, capped per position.
    Scales total exposure by max_exposure to keep cash buffer.
    """

    def __init__(self, sector_cap=0.25, rebalance=timedelta(days=7), max_exposure=0.60):
        super().__init__()
        self.sector_cap = sector_cap
        self.max_exposure = max_exposure
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

        # Score-weighted allocation
        scores = {}
        for insight in active:
            mag = abs(insight.magnitude) if insight.magnitude else 1.0
            scores[insight] = max(mag, 0.01)

        total_score = sum(scores.values())
        if total_score <= 0:
            per_weight = self.max_exposure / len(active)
            for insight in active:
                result[insight] = insight.direction * per_weight
            return result

        for insight in active:
            weight = scores[insight] / total_score
            weight = min(weight, self.sector_cap)
            result[insight] = insight.direction * weight

        # Renormalize to max_exposure
        total = sum(abs(v) for v in result.values())
        if total > 0:
            scale = min(1.0, self.max_exposure / total)
            for insight in result:
                result[insight] = result[insight] * scale

        return result
