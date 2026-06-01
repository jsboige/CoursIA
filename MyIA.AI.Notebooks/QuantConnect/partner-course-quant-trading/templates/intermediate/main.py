# region imports
from AlgorithmImports import *
# endregion


class MomentumAlphaModel(AlphaModel):
    """
    Modele Alpha base sur le momentum a 90 jours.
    Emet des Insights haussiers pour les titres dont le momentum est positif.
    """

    def __init__(self, lookback=90):
        super().__init__()
        self.lookback = lookback
        # Stocke l'indicateur MomentumPercent par symbole
        self.indicators = {}

    def update(self, algorithm, data):
        """Genere des Insights a chaque appel (filtre par momentum positif)."""
        insights = []
        for symbol, indicator in self.indicators.items():
            if symbol not in data.bars:
                continue
            if not indicator.is_ready:
                continue
            # Emettre un signal haussier si le momentum est positif
            if indicator.current.value > 0:
                insights.append(
                    Insight.price(symbol, Expiry.END_OF_MONTH, InsightDirection.UP)
                )
        return insights

    def on_securities_changed(self, algorithm, changes):
        """Enregistre ou retire l'indicateur lors de changements d'univers."""
        for security in changes.removed_securities:
            sym = security.symbol
            if sym in self.indicators:
                del self.indicators[sym]

        for security in changes.added_securities:
            sym = security.symbol
            if sym not in self.indicators:
                self.indicators[sym] = algorithm.MOMP(sym, self.lookback, Resolution.DAILY)


class IntermediateMomentumAlgorithm(QCAlgorithm):
    """
    Strategie de momentum sur les actions du SPY (top 100 par volume).
    Utilise l'Alpha Framework de QuantConnect :
      - AlphaModel    : signaux bases sur MomentumPercent(90)
      - PCM           : ponderation egale (EqualWeighting)
      - RiskManagement: trailing stop a 5 %
      - Execution     : execution immediate par defaut
    Rebalancement mensuel via ScheduledEvent.
    """

    def initialize(self):
        # -- Parametres de backtest -----------------------------------------
        self.set_start_date(2021, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)

        # -- Modele de courtage Interactive Brokers (marge) -----------------
        self.set_brokerage_model(
            BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN
        )

        # -- Univers : composants SPY, top 100 par volume en dollars -------
        self.universe_settings.resolution = Resolution.DAILY
        self.add_universe(
            self.universe.etf("SPY", self.universe_settings, self.filter_universe)
        )
        self.set_benchmark("SPY")

        # -- Alpha Framework -----------------------------------------------
        # 1) Modele Alpha : momentum sur 90 jours
        self.set_alpha(MomentumAlphaModel(lookback=90))

        # 2) Construction de portefeuille : ponderation egale
        self.set_portfolio_construction(
            EqualWeightingPortfolioConstructionModel(self.date_rules.month_start())
        )

        # 3) Gestion du risque : trailing stop a 5 %
        self.add_risk_management(TrailingStopRiskManagementModel(0.05))

        # 4) Execution : modele immediat par defaut (ImmediateExecutionModel)
        self.set_execution(ImmediateExecutionModel())

        # -- Rebalancement mensuel via evenement planifie -------------------
        self.rebalance_flag = False
        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.trigger_rebalance,
        )

        # -- Periode de chauffe pour que les indicateurs soient prets ------
        self.set_warm_up(timedelta(days=100))

    def filter_universe(self, constituents):
        """Filtre l'univers SPY : top 100 composants par volume en dollars."""
        selected = [c for c in constituents if c.weight is not None and c.weight > 0]
        selected = sorted(selected, key=lambda c: c.weight, reverse=True)[:100]
        return [c.symbol for c in selected]

    def trigger_rebalance(self):
        """Marque le debut du mois pour declencher le rebalancement."""
        self.rebalance_flag = True

    def on_data(self, data):
        """Logique principale : le framework Alpha gere les ordres."""
        # Rien a faire ici ; tout est gere par le pipeline Alpha.
        # On peut ajouter du logging si besoin :
        if self.rebalance_flag:
            self.rebalance_flag = False
            invested = [s.key for s in self.portfolio if s.value.invested]
            self.debug(f"Rebalancement mensuel - {len(invested)} positions actives")
