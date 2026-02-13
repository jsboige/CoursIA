#region imports
from AlgorithmImports import *
#endregion
class DualMomentumAlphaModel(AlphaModel):

    def __init__(self):
        self.sectors = {}
        self.securities_list = []
        self.day = -1

    def update(self, algorithm, data):
        insights = []
        for symbol in set(data.splits.keys() + data.dividends.keys()):
            security = algorithm.securities[symbol]
            if security in self.securities_list:
                security.indicator.reset()
                algorithm.subscription_manager.remove_consolidator(security.symbol, security.consolidator)
                self._register_indicator(algorithm, security)
                history = algorithm.history[TradeBar](security.symbol, 7,
                                                      Resolution.DAILY,
                                                      data_normalization_mode=DataNormalizationMode.SCALED_RAW)
                for bar in history:
                    security.consolidator.update(bar)
        if data.quote_bars.count == 0:
            return []
        if self.day == algorithm.time.day:
            return []
        self.day = algorithm.time.day
        momentum_by_sector = {}
        security_momentum = {}
        for sector in self.sectors:
            securities = self.sectors[sector]
            security_momentum[sector] = {security: security.indicator.current.value
                              for security in securities if
                              security.symbol in data.quote_bars and security.indicator.is_ready}
            momentum_by_sector[sector] = sum(list(security_momentum[sector].values()))
        target_sectors = [sector for sector in self.sectors if momentum_by_sector[sector] > 0]
        target_securities = []
        for sector in target_sectors:
            for security in security_momentum[sector]:
                if security_momentum[sector][security] > 0:
                    security.SetLeverage(2)
                    target_securities.append(security)
        target_securities = sorted(target_securities, key = lambda x: algorithm.securities[x.symbol].Fundamentals.MarketCap, reverse=True)[:10]
        for security in target_securities:
            insights.append(Insight.price(security.symbol, Expiry.END_OF_DAY, InsightDirection.UP))
        return insights

    def on_securities_changed(self, algorithm, changes):
        security_by_symbol = {}
        for security in changes.RemovedSecurities:
            if security in self.securities_list:
                algorithm.subscription_manager.remove_consolidator(security.symbol, security.consolidator)
                self.securities_list.remove(security)
            for sector in self.sectors:
                if security in self.sectors[sector]:
                    self.sectors[sector].remove(security)
        for security in changes.AddedSecurities:
            sector = security.Fundamentals.AssetClassification.MorningstarSectorCode
            security_by_symbol[security.symbol] = security
            security.indicator = MomentumPercent(1)
            self._register_indicator(algorithm, security)
            self.securities_list.append(security)
            if sector not in self.sectors:
                self.sectors[sector] = set()
            self.sectors[sector].add(security)
            if security_by_symbol:
                history = algorithm.history[TradeBar](list(security_by_symbol.keys()), 7,
                                                  Resolution.DAILY,
                                                  data_normalization_mode=DataNormalizationMode.SCALED_RAW)
                for trade_bars in history:
                    for bar in trade_bars.values():
                        security_by_symbol[bar.symbol].consolidator.update(bar)

    def _register_indicator(self, algorithm, security):
        security.consolidator = TradeBarConsolidator(Calendar.WEEKLY)
        algorithm.subscription_manager.add_consolidator(security.symbol, security.consolidator)
        algorithm.register_indicator(security.symbol, security.indicator, security.consolidator)
