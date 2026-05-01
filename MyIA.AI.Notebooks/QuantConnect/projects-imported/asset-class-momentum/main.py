#region imports
from AlgorithmImports import *
#endregion
# Asset Class Momentum (Dual Momentum)
# Source: https://www.quantconnect.com/learning/articles/investment-strategy-library/asset-class-trend-following
# Reference: Quantpedia Strategy #2 - Asset Class Momentum
# Concept: Use 5 ETFs (SPY - US stocks, EFA - foreign stocks, BND - bonds, VNQ - REITs, GSG - commodities).
# Pick 3 ETFs with strongest 12-month (252 days) momentum into portfolio and weight them equally.
# Hold for 1 month and then rebalance.
# Imported from QC Cloud Project ID: 29687233


class AssetClassMomentumAlgorithm(QCAlgorithm):

    def initialize(self):
        self.set_start_date(2007, 1, 1)
        self.set_cash(100000)
        self.settings.automatic_indicator_warm_up = True

        for ticker in ["SPY", "EFA", "BND", "VNQ", "GSG"]:
            equity = self.add_equity(ticker, Resolution.DAILY)
            equity.momp = self.momp(equity.symbol, 252, Resolution.DAILY)

    def on_data(self, slice):
        if self.is_warming_up:
            return
        # Pick 3 ETFs with strongest momentum and weight them equally.
        to_long = [x.symbol for x in sorted(self.securities.values(), key=lambda s: s.momp)[-3:]]
        targets = [PortfolioTarget(symbol, 1 / 3) for symbol in to_long]
        self.set_holdings(targets, liquidate_existing_holdings=True)
