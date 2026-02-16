# region imports
from AlgorithmImports import *
from universe import SectorETFUniverseSelectionModel
from portfolio import CointegratedVectorPortfolioConstructionModel
from risk import TrailingStopRiskManagementModel
from alpha import FilteredPairsAlphaModel
# endregion

class ETFPairsTrading(QCAlgorithm):

    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetEndDate(2024, 3, 1)
        self.SetCash(1000000)
        self.resolution = Resolution.Hour
        self.Settings.FillForwardDataEnabled = True
        self.SetBenchmark("SPY")
        self.UniverseSettings.Resolution = self.resolution
        self.UniverseSettings.DataNormalizationMode = DataNormalizationMode.Adjusted

        lookback_param = self.GetParameter("lookback") or "20"
        threshold_param = self.GetParameter("threshold") or "1.5"
        self.lookback = int(lookback_param)
        self.zscore_threshold = float(threshold_param)

        self.SetBrokerageModel(BrokerageName.InteractiveBrokersBrokerage, AccountType.Margin)
        self.SetSecurityInitializer(lambda s: s.SetMarginModel(PatternDayTradingMarginModel()))

        self.SetUniverseSelection(SectorETFUniverseSelectionModel(self.UniverseSettings))

        self.filteredAlpha = FilteredPairsAlphaModel(
            lookback=self.lookback,
            resolution=self.resolution,
            threshold=self.zscore_threshold,
            pairs=[],
            cooldown_days=2
        )
        self.AddAlpha(self.filteredAlpha)

        self.pcm = CointegratedVectorPortfolioConstructionModel(
            algorithm=self,
            lookback=120,
            resolution=self.resolution,
            rebalance=Expiry.EndOfWeek,
            max_position_size=0.20
        )
        self.pcm.rebalance_portfolio_on_security_changes = False
        self.SetPortfolioConstruction(self.pcm)

        self.AddRiskManagement(TrailingStopRiskManagementModel(stop_loss_percentage=0.08))

        self.SetWarmUp(14, self.resolution)

        # Decouvrir les paires co-integrees chaque lundi matin
        self.Schedule.On(
            self.DateRules.Every(DayOfWeek.Monday),
            self.TimeRules.AfterMarketOpen("SPY", 30),
            Action(self.RebalancePairs)
        )

        self.Schedule.On(
            self.DateRules.Every(DayOfWeek.Friday),
            self.TimeRules.AfterMarketClose("USA", 0),
            Action(self.WeeklySummaryLog)
        )

    def OnData(self, slice):
        if self.IsWarmingUp:
            return
        if slice.Splits or slice.Dividends:
            self.pcm.handle_corporate_actions(self, slice)

    def RebalancePairs(self):
        symbols = [s.Symbol for s in self.ActiveSecurities.Values]
        if len(symbols) < 2:
            self.Log("Not enough active securities for pair analysis.")
            return
        history = self.History(symbols, 1638, self.resolution)
        if history.empty:
            self.Log("No historical data available for these symbols.")
            return
        prices = history.close.unstack(level=0)
        results = []
        from itertools import combinations
        from statsmodels.tsa.stattools import coint
        for etf1, etf2 in combinations(symbols, 2):
            etf1_prices = prices[etf1].dropna()
            etf2_prices = prices[etf2].dropna()
            common_idx = etf1_prices.index.intersection(etf2_prices.index)
            etf1_prices = etf1_prices.loc[common_idx]
            etf2_prices = etf2_prices.loc[common_idx]
            if len(etf1_prices) > 50:
                t_stat, pvalue, crit = coint(etf1_prices, etf2_prices)
                corr = etf1_prices.corr(etf2_prices)
                vol = etf1_prices.std() + etf2_prices.std()
                if pvalue < 0.05 and vol > 0.01:
                    results.append((etf1, etf2, pvalue, corr, vol))
        if not results:
            self.Log("No valid cointegrated pairs found.")
            return
        results.sort(key=lambda x: x[2])
        top_pairs = [(etf1, etf2) for etf1, etf2, _, _, _ in results[:3]]
        for etf1, etf2 in top_pairs:
            if etf1 not in self.Securities:
                self.Log(f"Forcing AddEquity for {etf1.Value}")
                self.AddEquity(etf1.Value, self.resolution)
            if etf2 not in self.Securities:
                self.Log(f"Forcing AddEquity for {etf2.Value}")
                self.AddEquity(etf2.Value, self.resolution)
        self.filteredAlpha.update_pairs(top_pairs)
        self.Log(f"Top pairs discovered and forced add: {[f'{etf1.Value}-{etf2.Value}' for etf1, etf2 in top_pairs]}")

    def WeeklySummaryLog(self):
        equity = self.Portfolio.TotalPortfolioValue
        invested_symbols = [kvp.Key.Value for kvp in self.Portfolio if kvp.Value.Invested]
        self.Log(f"[Weekly Summary] {self.Time} | Equity: {equity:0.2f} | Invested: {invested_symbols}")
