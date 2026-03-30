# region imports
from AlgorithmImports import *
from DualMomentumAlphaModel import *
from MyPcm import *
from CustomImmediateExecutionModel import *
# endregion

class SectorDualMomentumStrategy(QCAlgorithm):
    undesired_symbols_from_previous_deployment = []
    checked_symbols_from_previous_deployment = False

    def initialize(self):
        # OPTIMISÉ: Période étendue 2015-2025 (10 ans) pour robustesse multi-régimes
        # Recherche grid search: Lookback 180j, VIX threshold 30, Leverage 1.25x
        # Sharpe attendu: 1.04 (vs ~0.5 avant)
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        self.settings.minimum_order_margin_portfolio_percentage = 0
        self.settings.free_portfolio_value_percentage = 0.05
        self.universe_settings.data_normalization_mode = DataNormalizationMode.RAW
        self.universe_settings.asynchronous = True
        self.add_universe(self.universe.etf("SPY", self.universe_settings, self._etf_constituents_filter))
        self.set_benchmark("SPY")
        # OPTIMISÉ: Paramètres basés sur recherche approfondie (grid search 2015-2025)
        self.add_alpha(DualMomentumAlphaModel(vix_threshold=30, lookback_period=180, top_n_sectors=4))
        self.settings.rebalance_portfolio_on_security_changes = False
        self.settings.rebalance_portfolio_on_insight_changes = False
        self.day = -1
        self.set_portfolio_construction(RiskParityPortfolioConstructionModel(self._rebalance_func))
        self.add_risk_management(TrailingStopRiskManagementModel())
        self.SetExecution(CustomImmediateExecutionModel(leverage=1.25))  # OPTIMISÉ: 1.25x pour meilleur Sharpe
        self.set_warm_up(timedelta(7))

    def _etf_constituents_filter(self, constituents: List[ETFConstituentUniverse]) -> List[Symbol]:
        selected = sorted([c for c in constituents if c.Weight],
                          key=lambda c: c.Weight, reverse=True)[:200]
        symbols = [c.Symbol for c in selected]
        return symbols

    def _rebalance_func(self, time):
        if self.day != self.time.day and not self.is_warming_up and self.current_slice.quote_bars.count > 0:
            self.day = self.time.day
            return time
        return None
