#region imports
from AlgorithmImports import *

import pandas as pd
from datetime import datetime
#endregion
# https://quantpedia.com/Screener/Details/2
# Use 5 ETFs (SPY - US stocks, EFA - foreign stocks, BND - bonds, VNQ - REITs, GSG - commodities).
# Pick 3 ETFs with strongest 12 month (252 days) momentum into your portfolio and weight them equally.
# Hold for 1 month and then rebalance.

class AssetClassMomentumAlgorithm(QCAlgorithm):

    def initialize(self):
        # Aligned baseline period 2018-2025 (#1630). Original lookback was 17y
        # (end - 17*365); standardized to 2018-01-01 for cross-strategy comparison.
        self.set_start_date(2018, 1, 1)
        self.set_end_date(2025, 1, 1)  # Fixed end date for reproducibility
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        self.settings.automatic_indicator_warm_up = True

        for ticker in ["SPY", "EFA", "BND", "VNQ", "GSG"]:
            equity = self.add_equity(ticker, Resolution.DAILY)
            equity.momp = self.momp(equity.symbol, 252, Resolution.DAILY)

    def on_data(self, slice):
        # Pick 3 ETFs with strongest momentum and weight them equally.
        to_long = [x.symbol for x in sorted(self.securities.values(), key=lambda s: s.momp)[-3:]]
        targets = [PortfolioTarget(symbol, 1/3) for symbol in to_long]
        self.set_holdings(targets, liquidate_existing_holdings=True)
