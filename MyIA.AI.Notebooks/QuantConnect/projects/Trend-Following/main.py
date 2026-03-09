# region imports
from datetime import datetime
from AlgorithmImports import *
from alpha import custom_alpha

# endregion


class CompetitionAlgorithm(QCAlgorithm):

    def Initialize(self):
        self.SetStartDate(2019, 1, 1)
        self.SetCash(1000000)
        self.SetWarmUp(10)
        self.spy = self.AddEquity("SPY", Resolution.Hour).Symbol
        self.SetBenchmark(self.spy)
        # v2: reduced from 600 to 200 stocks to reduce noise
        self.final_universe_size = 200
        self.rebalanceTime = self.time
        self.universe_type = "equity"
        if self.universe_type == "equity":
            self.AddUniverse(self.CoarseFilter, self.FineFilter)
        self.UniverseSettings.Resolution = Resolution.Hour
        # v3b: SPY SMA200 removed - per-stock EMA50/200 filter sufficient (regime filter degraded results)
        # v2: removed 1.85x leverage multiplier PCM, use standard model
        self.set_portfolio_construction(InsightWeightingPortfolioConstructionModel())
        self.set_alpha(custom_alpha(self))
        self.set_execution(VolumeWeightedAveragePriceExecutionModel())
        # v3: keep 10% per-security drawdown (same as v2) + SPY SMA200 regime filter as main protection
        self.add_risk_management(MaximumDrawdownPercentPerSecurity(0.10))
        self.SetBrokerageModel(BrokerageName.InteractiveBrokersBrokerage, AccountType.Margin)

    def CoarseFilter(self, coarse):
        if self.Time <= self.rebalanceTime:
            return self.Universe.Unchanged
        self.rebalanceTime = self.Time + timedelta(days=300)
        sortedByDollarVolume = sorted(coarse, key=lambda x: x.DollarVolume, reverse=True)
        return [x.Symbol for x in sortedByDollarVolume if x.HasFundamentalData][:1000]

    def FineFilter(self, fine):
        sortedbyVolume = sorted(fine, key=lambda x: x.DollarVolume, reverse=True)
        fine_output = [x.Symbol for x in sortedbyVolume if x.price > 10 and x.MarketCap > 2000000000][:self.final_universe_size]
        return fine_output
