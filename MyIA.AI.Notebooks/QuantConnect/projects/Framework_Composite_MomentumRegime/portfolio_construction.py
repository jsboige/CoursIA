from AlgorithmImports import *


class MultiStrategyPCM(PortfolioConstructionModel):
    """
    Custom Portfolio Construction Model for multi-strategy framework.

    Groups insights by source_model (alpha name), allocates a capital slice
    per strategy, then aggregates overlapping tickers additively.

    Example: If SectorMomentum (60% slice) and RegimeSwitching (40% slice)
    both emit UP for SPY, the final target is the sum of both allocations.
    """

    def __init__(self, alpha_allocations, rebalance=timedelta(days=31)):
        super().__init__()
        self.alpha_allocations = alpha_allocations
        # Set rebalancing schedule (monthly)
        self.set_rebalancing_func(lambda dt: dt + rebalance)

    def determine_target_percent(self, active_insights):
        """
        Group insights by source alpha, compute per-strategy weights,
        then combine additively with capital slice scaling.
        """
        result = {}

        if not active_insights:
            return result

        # Group insights by source alpha model
        by_alpha = {}
        for insight in active_insights:
            source = insight.source_model or "Unknown"
            if source not in by_alpha:
                by_alpha[source] = []
            by_alpha[source].append(insight)

        for alpha_name, insights in by_alpha.items():
            capital_slice = self.alpha_allocations.get(alpha_name, 0)
            if capital_slice <= 0:
                for insight in insights:
                    result[insight] = 0
                continue

            # Separate active (UP/DOWN) from flat
            active = [i for i in insights if i.direction != InsightDirection.FLAT]
            flat = [i for i in insights if i.direction == InsightDirection.FLAT]

            # Flat insights -> 0% target
            for insight in flat:
                result[insight] = 0

            if not active:
                continue

            # Check if insights have explicit weight hints
            has_weights = all(
                i.weight is not None and i.weight > 0 for i in active
            )

            if has_weights:
                # Use weight hints (e.g., RegimeSwitching SPY=0.70, QQQ=0.30)
                # Scale by capital slice
                for insight in active:
                    result[insight] = insight.direction * insight.weight * capital_slice
            else:
                # Equal weight within this alpha's slice (e.g., SectorMomentum single asset)
                per_symbol = capital_slice / len(active)
                for insight in active:
                    result[insight] = insight.direction * per_symbol

        return result
