# region imports
from AlgorithmImports import *
from universe import PiotroskiScoreUniverseSelectionModel
# endregion
# https://www.quantconnect.com/strategies/343
# High Book-to-Market High F-Score Quality Value by Louis Szeto
# OOS 1Y Sharpe 2.09, 5Y CAGR 18.44%, 5Y Drawdown 24.20%, 62% Win Rate
# Systematic equity long-only value + quality screen using Piotroski F-Score anomaly
# Top 20% book-to-market stocks filtered by F-Score >= 8, equal-weighted, monthly rebalance
# Source: QC Strategy Library #343, cloned 2026-04-05, QC Project ID: 29687591


class PiotroskiScoreAlgorithm(QCAlgorithm):

    def initialize(self):
        self.set_cash(10_000_000)
        self.set_start_date(self.end_date - timedelta(12*365))
        # Configure settings to rebalance monthly.
        rebalance_date = self.date_rules.month_start('SPY')
        # Define the universe settings.
        self.universe_settings.schedule.on(rebalance_date)
        self.universe_settings.resolution = Resolution.HOUR
        self.settings.rebalance_portfolio_on_insight_changes = False
        self.add_universe_selection(PiotroskiScoreUniverseSelectionModel(
            self,
            self.get_parameter('score_threshold', 8),
            self.get_parameter('max_universe_size', 100)
        ))
        # Long all stocks in the universe.
        self.add_alpha(ConstantAlphaModel(InsightType.PRICE, InsightDirection.UP, timedelta(30)))
        # Weight assets equally.
        self.set_portfolio_construction(EqualWeightingPortfolioConstructionModel(rebalance_date))
        # Avoid illiquid assets. Maximum 1% spread allowed before execution.
        self.set_execution(SpreadExecutionModel(0.01))
        # Add a warm-up period to warm-up the fundamental factors we need.
        self.set_warm_up(timedelta(3*365))
