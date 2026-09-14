# region imports
from AlgorithmImports import *
# endregion

# qc-research #20966 : Filing language stability as a selection signal (long leg).
# Classe les 100 actions US les plus liquides par similarite du langage des
# risk-factors des filings 10-K/10-Q (Brain Language Metrics), tient le top 25
# en poids max-Sharpe (fenetre 12 mois), rebalancement mensuel. Long-only :
# jambe longue de l'anomalie Lazy Prices (Cohen-Malloy-Nguyen, JF 2020).
# Verdict attendu honnete : edge marginal (article : Sharpe 0.558 vs SPY 0.533,
# 9/25 combinaisons du sweep battent le benchmark, resultat attribue par
# l'auteur a la fenetre de l'optimiseur plutot qu'au signal).


class SharpePortfolioOptimizerWrapper:
    """Poids max-Sharpe sur fenetre glissante de rendements quotidiens."""

    def __init__(self, lower: float, upper: float, period_days: int) -> None:
        self._optimizer = MaximumSharpeRatioPortfolioOptimizer(lower, upper)
        self._period = period_days

    def get_weights(self, algorithm: QCAlgorithm, symbols) -> list:
        if not symbols:
            return []
        history = algorithm.history(
            [s.id for s in symbols], self._period + 1, Resolution.DAILY)
        returns = history["close"].unstack(0).pct_change().dropna()
        if returns.empty or len(returns) < 2:
            return [0.0] * len(symbols)
        return list(self._optimizer.optimize(returns))


class FilingLanguageStabilityAlgorithm(QCAlgorithm):

    def initialize(self) -> None:
        self.set_start_date(2020, 1, 1)
        self.set_end_date(2026, 6, 30)
        self.set_cash(100_000)
        self.set_benchmark("SPY")

        self.universe_settings.resolution = Resolution.DAILY
        self.universe_settings.leverage = 1.0

        self._lookback_months = 12
        self._fundamental_size = 100
        self._universe_size = 25

        self._weight_optimizer = SharpePortfolioOptimizerWrapper(
            0.0, 1.0, self._lookback_months * 21)

        self._fundamental = self.add_universe(self._fundamental_filter)
        self._universe = self.add_universe(
            BrainCompanyFilingLanguageMetricsUniverseAll, self._select_assets)

        self.schedule.on(
            self.date_rules.month_start(),
            self.time_rules.at(8, 0),
            self._rebalance)

    def _fundamental_filter(self, fundamentals) -> list:
        # 100 actions US les plus liquides par dollar volume (donnees
        # fondamentales requises -- filtre coarse de l'article).
        by_dollar_volume = sorted(
            fundamentals, key=lambda f: f.dollar_volume)
        return [f.symbol for f in by_dollar_volume[-self._fundamental_size:]]

    def _select_assets(self, filings) -> list:
        # Score de similarite : risk-factors d'abord (section la plus
        # informative selon le papier source), sinon rapport complet.
        liquid = set(self._fundamental.selected) if self._fundamental.selected else set()
        if not liquid:
            return Universe.UNCHANGED

        latest = {}
        for filing in filings:
            if filing.symbol not in liquid:
                continue
            current = latest.get(filing.symbol)
            if current is None or filing.end_time > current.end_time:
                latest[filing.symbol] = filing

        scored = []
        for symbol, filing in latest.items():
            score = self._similarity(filing, "risk_factors_statement_sentiment")
            if score is None:
                score = self._similarity(filing, "report_sentiment")
            if score is not None:
                scored.append((symbol, score))

        scored.sort(key=lambda item: item[1], reverse=True)
        return [symbol for symbol, _ in scored[:self._universe_size]]

    def _similarity(self, filing, section):
        section_data = getattr(filing, section, None)
        similarity = getattr(section_data, "similarity", None) if section_data is not None else None
        if similarity is None:
            return None
        value = getattr(similarity, "all", None)
        if value is None:
            return None
        try:
            return float(value)
        except (TypeError, ValueError):
            return None

    def _rebalance(self) -> None:
        selected = list(self._universe.selected)
        if not selected:
            return
        weights = self._weight_optimizer.get_weights(self, selected)
        total = sum(w for w in weights if w is not None and w > 0)
        if total <= 0:
            self.liquidate()
            return
        targets = [
            PortfolioTarget(symbol, float(w) / total)
            for symbol, w in zip(selected, weights)
            if w is not None and w > 0
        ]
        if targets:
            self.set_holdings(targets, True)
