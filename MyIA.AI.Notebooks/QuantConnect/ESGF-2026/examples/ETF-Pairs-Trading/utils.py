#region imports
from AlgorithmImports import *
#endregion

def reset_and_warm_up(algorithm, data_dict, resolution, lookback=None):
    indicator = data_dict["logr"]
    consolidator = data_dict["consolidator"]
    symbol = data_dict["symbol"]
    if not lookback:
        lookback = indicator.WarmUpPeriod
    bars = list(algorithm.History[TradeBar](
        symbol,
        lookback,
        resolution,
        dataNormalizationMode=DataNormalizationMode.Raw
    ))
    if len(bars) == 0:
        algorithm.Log(f"No history for {symbol}.")
        return consolidator
    indicator.Reset()
    algorithm.SubscriptionManager.RemoveConsolidator(symbol, consolidator)
    new_cons = TradeBarConsolidator(timedelta(hours=1))
    algorithm.RegisterIndicator(symbol, indicator, new_cons)
    for bar in bars:
        new_cons.Update(bar)
    data_dict["consolidator"] = new_cons
    return new_cons
