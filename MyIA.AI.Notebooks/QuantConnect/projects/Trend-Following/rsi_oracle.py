#region imports
from AlgorithmImports import *
#endregion

def get_rsi_buy_short(price_trend, rsi_trend):
    if price_trend > 0:
        if rsi_trend > 0:
            return 1
    elif price_trend < 0:
        if rsi_trend < 0:
            return 2
    return 0

def get_rsi_sell_cover(price_trend, rsi_trend):
    if price_trend > 0:
        if rsi_trend < 0:
            return 1
    elif price_trend < 0:
        if rsi_trend > 0:
            return 2
    return 0
