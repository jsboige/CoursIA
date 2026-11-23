from AlgorithmImports import *


class MeanVariancePCM(PortfolioConstructionModel):
    """
    Score-Weighted PCM with position cap and total exposure scaling.

    Uses insight magnitudes for weighting, capped per position.
    Scales total exposure by max_exposure to keep cash buffer.

    Caveat (#21137, same mechanism as #19740): before determine_target_percent
    runs, Lean's PortfolioConstructionModel.GetTargetInsights keeps only the
    most recent active insight per symbol. The four factor alphas of this
    composite score the same stocks in the same slice, so with
    by_sleeve=False (the code before #21137) the last alpha of the
    CompositeAlphaModel overwrites the others on every stock it scores.
    With by_sleeve=True, the targets are rebuilt from the most recent active
    insight per (symbol, source_model): scores are normalized inside each
    alpha's sleeve, each sleeve with an active insight gets an equal share,
    and the shares are summed per symbol before the cap and the exposure
    scaling.
    """

    def __init__(self, sector_cap=0.25, rebalance=timedelta(days=7), max_exposure=0.60,
                 by_sleeve=False, algorithm=None):
        super().__init__()
        self.sector_cap = sector_cap
        self.max_exposure = max_exposure
        self.by_sleeve = by_sleeve
        self._algorithm = algorithm
        # Diagnostics for #21137 (read by main.py at the end of the backtest):
        # insights reaching determine_target_percent, per source_model.
        self.calls = 0
        self.reached = {}
        self.reached_active = {}
        self.set_rebalancing_func(lambda dt: dt + rebalance)

    def determine_target_percent(self, active_insights):
        if not active_insights:
            return {}

        self.calls += 1
        for insight in active_insights:
            source = insight.source_model or "Unknown"
            self.reached[source] = self.reached.get(source, 0) + 1
            if insight.direction != InsightDirection.FLAT:
                self.reached_active[source] = self.reached_active.get(source, 0) + 1

        if not self.by_sleeve or self._algorithm is None:
            return self._score_weights(active_insights, scale_to_exposure=True)

        # One insight per (symbol, source_model), the most recent one.
        latest = {}
        for insight in self._algorithm.insights.get_active_insights(self._algorithm.utc_time):
            key = (insight.symbol, insight.source_model or "Unknown")
            previous = latest.get(key)
            if previous is None or insight.generated_time_utc >= previous.generated_time_utc:
                latest[key] = insight

        by_source = {}
        for insight in latest.values():
            by_source.setdefault(insight.source_model or "Unknown", []).append(insight)
        sleeves = [source for source, insights in by_source.items()
                   if any(i.direction != InsightDirection.FLAT for i in insights)]

        totals = {}
        if sleeves:
            share = 1.0 / len(sleeves)
            for source in sleeves:
                weights = self._score_weights(by_source[source], scale_to_exposure=False, cap=False)
                for insight, weight in weights.items():
                    totals[insight.symbol] = totals.get(insight.symbol, 0.0) + share * weight

        for symbol in totals:
            totals[symbol] = max(-self.sector_cap, min(self.sector_cap, totals[symbol]))
        total = sum(abs(v) for v in totals.values())
        scale = min(1.0, self.max_exposure / total) if total > 0 else 0.0

        # active_insights holds one insight per symbol: it carries the sum.
        return {insight: totals.get(insight.symbol, 0.0) * scale for insight in active_insights}

    def _score_weights(self, insights, scale_to_exposure, cap=True):
        active = [i for i in insights if i.direction != InsightDirection.FLAT]
        flat = [i for i in insights if i.direction == InsightDirection.FLAT]

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
            if cap:
                weight = min(weight, self.sector_cap)
            result[insight] = insight.direction * weight

        if not scale_to_exposure:
            return result

        # Renormalize to max_exposure
        total = sum(abs(v) for v in result.values())
        if total > 0:
            scale = min(1.0, self.max_exposure / total)
            for insight in result:
                result[insight] = result[insight] * scale

        return result
