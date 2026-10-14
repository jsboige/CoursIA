from AlgorithmImports import *


class MultiStrategyPCM(PortfolioConstructionModel):
    """
    Custom Portfolio Construction Model for multi-strategy framework.

    Groups insights by source_model (alpha name), allocates a capital slice
    per strategy, then aggregates overlapping tickers additively.

    Example: If SectorMomentum (60% slice) and RegimeSwitching (40% slice)
    both emit UP for SPY, the final target is the sum of both allocations.

    Caveat (#19740): before determine_target_percent runs, Lean's
    PortfolioConstructionModel.GetTargetInsights keeps only the most recent
    active insight per symbol. With additive=False (the code before #19740),
    the sleeves are therefore not added on shared tickers: the last alpha to
    emit wins. With additive=True, the targets are rebuilt from the most
    recent active insight per (symbol, source_model), then summed per symbol.
    """

    def __init__(self, alpha_allocations, rebalance=timedelta(days=31),
                 additive=False, algorithm=None):
        super().__init__()
        self.alpha_allocations = alpha_allocations
        self.additive = additive
        self._algorithm = algorithm
        # Diagnostics for #19740 (read by main.py at the end of the backtest)
        self.calls = 0
        self.calls_with_sm = 0
        self.sm_up_seen = 0
        # Set rebalancing schedule (monthly)
        self.set_rebalancing_func(lambda dt: dt + rebalance)

    def determine_target_percent(self, active_insights):
        """
        Group insights by source alpha, compute per-strategy weights,
        then combine additively with capital slice scaling.
        """
        if not active_insights:
            return {}

        self.calls += 1
        sm = [i for i in active_insights if i.source_model == "SectorMomentum"]
        if sm:
            self.calls_with_sm += 1
            self.sm_up_seen += sum(1 for i in sm if i.direction == InsightDirection.UP)

        if not self.additive or self._algorithm is None:
            return self._weights_by_source(active_insights)

        # One insight per (symbol, source_model), the most recent one.
        latest = {}
        for insight in self._algorithm.insights.get_active_insights(self._algorithm.utc_time):
            key = (insight.symbol, insight.source_model or "Unknown")
            previous = latest.get(key)
            if previous is None or insight.generated_time_utc >= previous.generated_time_utc:
                latest[key] = insight
        totals = {}
        for insight, weight in self._weights_by_source(list(latest.values())).items():
            totals[insight.symbol] = totals.get(insight.symbol, 0.0) + weight
        # active_insights holds one insight per symbol: it carries the sum.
        return {insight: totals.get(insight.symbol, 0.0) for insight in active_insights}

    def _weights_by_source(self, insights_list):
        result = {}

        # Group insights by source alpha model
        by_alpha = {}
        for insight in insights_list:
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
