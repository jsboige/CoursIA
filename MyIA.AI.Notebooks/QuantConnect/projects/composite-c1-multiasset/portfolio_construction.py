from AlgorithmImports import *
from SharedPCM.pouches_pcm import MultiStrategyPouchesPCM


def count_sources(counts, counts_active, insights):
    """Compte les insights par alpha (recus / actifs) dans deux dictionnaires."""
    for insight in insights:
        source = insight.source_model or "Unknown"
        counts[source] = counts.get(source, 0) + 1
        if insight.direction != InsightDirection.FLAT:
            counts_active[source] = counts_active.get(source, 0) + 1


class RiskParityPCM(PortfolioConstructionModel):
    """
    Equal-Weight PCM with exposure cap.

    Distributes max_exposure equally across all UP insights.
    """

    def __init__(self, rebalance=timedelta(days=7), max_exposure=0.80, sector_cap=0.35):
        super().__init__()
        self.max_exposure = max_exposure
        self.sector_cap = sector_cap
        self.calls = 0
        self.reached = {}
        self.reached_active = {}
        self.set_rebalancing_func(lambda dt: dt + rebalance)

    def determine_target_percent(self, active_insights):
        if not active_insights:
            return {}
        self.calls += 1
        count_sources(self.reached, self.reached_active, active_insights)

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


class CappedPouchesPCM(MultiStrategyPouchesPCM):
    """
    PCM par poches canonique (SharedPCM, #21134) avec le plafond par ligne
    de RiskParityPCM.

    Lean ne transmet au PCM que le dernier insight actif par symbole : avec
    trois alphas sur les memes ETF, RiskParityPCM ne voyait qu'un alpha par
    ligne (#21147, mecanisme #19740). Le module canonique reconstruit une
    poche par alpha ; ce sous-classement garde seulement le plafond par
    ligne de la version d'avant.
    """

    def __init__(self, alpha_allocations, line_cap, **kwargs):
        super().__init__(alpha_allocations, **kwargs)
        self.line_cap = line_cap
        self.reached = {}
        self.reached_active = {}
        self.pouch_seen = {}
        self.pouch_seen_active = {}

    def determine_target_percent(self, active_insights):
        if not active_insights:
            return {}
        # self.calls est compte par la classe canonique.
        count_sources(self.reached, self.reached_active, active_insights)
        # Diagnostic : ce que la reconstruction par (symbole, alpha) voit.
        latest = {}
        for insight in self._algorithm.insights.get_active_insights(self._algorithm.utc_time):
            key = (insight.symbol, insight.source_model or "Unknown")
            if key not in latest or insight.generated_time_utc >= latest[key].generated_time_utc:
                latest[key] = insight
        count_sources(self.pouch_seen, self.pouch_seen_active, latest.values())
        targets = super().determine_target_percent(active_insights)
        cap = self.line_cap
        return {insight: max(-cap, min(cap, weight)) for insight, weight in targets.items()}
