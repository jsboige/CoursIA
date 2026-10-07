from AlgorithmImports import *


class MultiStrategyPCM(PortfolioConstructionModel):
    """
    Custom Portfolio Construction Model for multi-strategy framework.

    Groups insights by source_model (alpha name), allocates a capital slice
    per strategy, then aggregates overlapping tickers additively.

    Caveat (#19759, same mechanism as #19740): before determine_target_percent
    runs, Lean's PortfolioConstructionModel.GetTargetInsights keeps only the
    most recent active insight per symbol. With additive=False (the code
    before #19759), the slices are therefore not added on shared tickers: the
    last alpha to emit wins. With additive=True, the targets are rebuilt from
    the most recent active insight per (symbol, source_model), then summed
    per symbol.
    """

    def __init__(self, alpha_allocations, rebalance=timedelta(days=31),
                 additive=False, algorithm=None, watch_source=None, watch_tickers=()):
        super().__init__()
        self.alpha_allocations = alpha_allocations
        self.additive = additive
        self._algorithm = algorithm
        # Diagnostics for #19759 (read by main.py at the end of the backtest):
        # calls where an insight of watch_source on one of watch_tickers
        # reaches determine_target_percent.
        self._watch_source = watch_source
        self._watch_tickers = set(watch_tickers)
        self.calls = 0
        self.calls_with_watch = 0
        self.set_rebalancing_func(lambda dt: dt + rebalance)

    def determine_target_percent(self, active_insights):
        if not active_insights:
            return {}

        self.calls += 1
        if any(i.source_model == self._watch_source and i.symbol.value in self._watch_tickers
               for i in active_insights):
            self.calls_with_watch += 1

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

            active = [i for i in insights if i.direction != InsightDirection.FLAT]
            flat = [i for i in insights if i.direction == InsightDirection.FLAT]

            for insight in flat:
                result[insight] = 0

            if not active:
                continue

            has_weights = all(
                i.weight is not None and i.weight > 0 for i in active
            )

            if has_weights:
                for insight in active:
                    result[insight] = insight.direction * insight.weight * capital_slice
            else:
                per_symbol = capital_slice / len(active)
                for insight in active:
                    result[insight] = insight.direction * per_symbol

        return result
