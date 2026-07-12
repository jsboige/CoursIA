#region imports
from AlgorithmImports import *
from tqdm import tqdm
import pandas as pd
#endregion

def get_macd_score(macd_rolling, trend, macd_params):
    hists = [x.hist for x in macd_rolling][:macd_params['cross_check_length']]
    macds = [x.macd for x in macd_rolling][:macd_params['macd_above_below_length']]
    cross = 0
    current = hists[0]
    if current >= 0:
        if any(x < 0 for x in hists):
            cross = 1
    elif current <= 0:
        if any(x > 0 for x in hists):
            cross = -1
    score = 0
    if trend > 0:
        if all(x > macd_params['long_macd_threshold'] for x in macds) and macds[0] > macd_params['long_macd_threshold']:
            score = 1
    elif trend < 0:
        if all(x > macd_params['short_macd_threshold'] for x in macds) and macds[0] > macd_params['short_macd_threshold']:
            score = 2
    return score
