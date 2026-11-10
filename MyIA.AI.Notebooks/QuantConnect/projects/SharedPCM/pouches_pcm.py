from AlgorithmImports import *


class MultiStrategyPouchesPCM(PortfolioConstructionModel):
    """
    PCM par poches : module canonique des composites multi-alpha.

    Chaque alpha (source_model) recoit une poche de capital fixee par
    alpha_allocations (ex. {"EMACross": 0.7, "TrendStocks": 0.3}). Dans
    chaque poche, les insights actifs sont ponderes par leur weight hint
    quand tous en ont un, sinon equiponderes. Les poches sont ensuite
    ADDITIONNEES par symbole quand plusieurs alphas emettent sur le meme
    ticker : sans levier, chaque poche plafonne a sa tranche et la somme
    par symbole ne depasse pas la somme des tranches.

    Mode intent (additive=True, defaut) : avant determine_target_percent,
    le PCM de base de Lean (GetTargetInsights) ne garde qu'un insight
    actif par symbole — sur un ticker partage, le dernier alpha a emettre
    gagne et les autres poches sont perdues. Pour additionner les poches
    comme annonce, les cibles sont reconstruites depuis le dernier
    insight actif par couple (symbole, source_model), puis sommees par
    symbole (#19740, #19759). Le mode "base" historique reste disponible
    via additive=False pour les comparaisons A/B.

    Ce fichier est la seule copie du module : les projets composites
    l'importent comme bibliotheque de projet QC (voir README.md du
    dossier). Sur QC Cloud, attacher ce projet en bibliotheque du
    consommateur, puis :

        from SharedPCM.pouches_pcm import MultiStrategyPouchesPCM
    """

    def __init__(self, alpha_allocations, rebalance=timedelta(days=31),
                 additive=True, algorithm=None, watch_source=None, watch_tickers=None):
        super().__init__()
        if additive and algorithm is None:
            raise ValueError(
                "additive=True exige algorithm : le reconstructeur du mode "
                "intent lit les insights actifs a travers l'algorithme "
                "(passez algorithm=self)")
        self.alpha_allocations = alpha_allocations
        self.additive = additive
        self._algorithm = algorithm
        # Diagnostics lus en fin de backtest (runtime statistics) : appels
        # de determine_target_percent, dont ceux ou un insight de
        # watch_source atteint le PCM. watch_tickers=None compte sans filtre
        # de symbole (comportement des copies d'origine) ; un itérable de
        # tickers restreint aux seuls symboles listés.
        self._watch_source = watch_source
        self._watch_tickers = set(watch_tickers) if watch_tickers is not None else None
        self.calls = 0
        self.calls_with_watch = 0
        self.watch_up_seen = 0
        self.set_rebalancing_func(lambda dt: dt + rebalance)

    def determine_target_percent(self, active_insights):
        if not active_insights:
            return {}

        self.calls += 1
        watched = [i for i in active_insights
                   if i.source_model == self._watch_source
                   and (self._watch_tickers is None
                        or i.symbol.value in self._watch_tickers)]
        if watched:
            self.calls_with_watch += 1
            self.watch_up_seen += sum(
                1 for i in watched if i.direction == InsightDirection.UP)

        if not self.additive or self._algorithm is None:
            return self._weights_by_source(active_insights)

        # Un insight par couple (symbole, source_model), le plus recent.
        latest = {}
        for insight in self._algorithm.insights.get_active_insights(self._algorithm.utc_time):
            key = (insight.symbol, insight.source_model or "Unknown")
            previous = latest.get(key)
            if previous is None or insight.generated_time_utc >= previous.generated_time_utc:
                latest[key] = insight
        totals = {}
        for insight, weight in self._weights_by_source(list(latest.values())).items():
            totals[insight.symbol] = totals.get(insight.symbol, 0.0) + weight
        # active_insights ne porte qu'un insight par symbole : il porte la somme.
        return {insight: totals.get(insight.symbol, 0.0) for insight in active_insights}

    def _weights_by_source(self, insights_list):
        """Poids par insight : direction * poids * tranche, poche par poche."""
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
                # Weight hints (ex. RegimeSwitching SPY=0.70, QQQ=0.30) :
                # chaque insight pese sa part de la poche.
                for insight in active:
                    result[insight] = insight.direction * insight.weight * capital_slice
            else:
                # Pas de hint : equipartition de la poche entre actifs actifs.
                per_symbol = capital_slice / len(active)
                for insight in active:
                    result[insight] = insight.direction * per_symbol

        return result
