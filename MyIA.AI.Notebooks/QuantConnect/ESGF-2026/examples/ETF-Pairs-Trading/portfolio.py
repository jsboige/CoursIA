#region imports
from AlgorithmImports import *
from Portfolio.EqualWeightingPortfolioConstructionModel import EqualWeightingPortfolioConstructionModel
from arch.unitroot.cointegration import engle_granger
from utils import reset_and_warm_up
#endregion

class CointegratedVectorPortfolioConstructionModel(EqualWeightingPortfolioConstructionModel):
    def __init__(self, algorithm, lookback=120, resolution=Resolution.Hour, rebalance=Expiry.EndOfWeek, max_position_size=0.20):
        super().__init__(rebalance, PortfolioBias.LongShort)
        self.algorithm = algorithm
        self.lookback = lookback
        self.resolution = resolution
        self.security_data = {}
        self.max_position_size = max_position_size
        self.rebalance_portfolio_on_security_changes = True

    def OnSecuritiesChanged(self, algorithm, changes):
        super().OnSecuritiesChanged(algorithm, changes)
        for added in changes.AddedSecurities:
            self.init_security_data(algorithm, added)
        for removed in changes.RemovedSecurities:
            self.dispose_security_data(algorithm, removed)

    def init_security_data(self, algorithm, sec_obj):
        data = {
            "symbol": sec_obj.Symbol,
            "logr": LogReturn(1),
            "window": RollingWindow[IndicatorDataPoint](self.lookback),
            "consolidator": TradeBarConsolidator(timedelta(hours=1))
        }
        data["logr"].Updated += lambda _, updated: data["window"].Add(
            IndicatorDataPoint(updated.EndTime, updated.Value)
        )
        algorithm.RegisterIndicator(sec_obj.Symbol, data["logr"], data["consolidator"])
        algorithm.SubscriptionManager.AddConsolidator(sec_obj.Symbol, data["consolidator"])
        self.security_data[sec_obj.Symbol] = data
        self.warm_up_indicator(data)

    def warm_up_indicator(self, data_dict):
        reset_and_warm_up(self.algorithm, data_dict, self.resolution, self.lookback)

    def dispose_security_data(self, algorithm, security):
        symbol = security.Symbol
        if symbol in self.security_data:
            data_dict = self.security_data.pop(symbol)
            self.reset(data_dict)
            algorithm.SubscriptionManager.RemoveConsolidator(symbol, data_dict["consolidator"])

    def reset(self, data_dict):
        data_dict["logr"].Reset()
        data_dict["window"].Reset()

    def handle_corporate_actions(self, algorithm, slice):
        symbols = set(slice.Dividends.keys()).union(slice.Splits.keys())
        for symbol in symbols:
            if symbol in self.security_data:
                self.warm_up_indicator(self.security_data[symbol])

    def DetermineTargetPercent(self, activeInsights: List[Insight]) -> Dict[Insight, float]:
        if len(activeInsights) < 2:
            return {insight: 0 for insight in activeInsights}
        data_map = {}
        symbols_in_insights = [i.Symbol for i in activeInsights]
        for sym in symbols_in_insights:
            if sym in self.security_data:
                data_map[sym] = self.returns(self.security_data[sym])
            else:
                data_map[sym] = pd.Series(dtype=float)
        df = pd.DataFrame(data_map).replace([np.inf, -np.inf], np.nan).dropna(how='any')
        if df.shape[1] < 2 or df.empty:
            self.live_log(self.algorithm, "Not enough columns or data => zero allocation.")
            return {insight: 0 for insight in activeInsights}
        model = engle_granger(df.iloc[:, 0], df.iloc[:, 1:], trend='n', lags=0)
        if model.pvalue > 0.10:
            return {insight: 0 for insight in activeInsights}
        coint_vector = model.cointegrating_vector
        total_weight = sum(abs(coint_vector))
        result = {}
        for insight, weight in zip(activeInsights, coint_vector):
            raw_target = abs(weight) / total_weight * insight.Direction
            capped_target = max(min(raw_target, self.max_position_size), -self.max_position_size)
            result[insight] = capped_target
        return result

    def returns(self, data_dict: dict) -> pd.Series:
        if "window" not in data_dict:
            return pd.Series(dtype=float)
        arr = [x.Value for x in data_dict["window"]]
        idx = [x.EndTime for x in data_dict["window"]]
        tmp = {}
        for t, val in zip(idx, arr):
            tmp[t] = val
        ser = pd.Series(tmp).sort_index()
        return ser.iloc[::-1]

    def live_log(self, algorithm, msg: str):
        algorithm.Log(msg)
