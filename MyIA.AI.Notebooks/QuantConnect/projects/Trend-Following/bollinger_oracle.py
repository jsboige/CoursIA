#region imports
from AlgorithmImports import *
#endregion


def get_bollinger_buy_and_short(QCalgo, bollinger_rolling_window,trend, bollinger_params):
    score = 0
    lowers = [x.lower for x in bollinger_rolling_window]
    middles = [x.middle for x in bollinger_rolling_window]
    uppers = [x.upper for x in bollinger_rolling_window]
    prices = [x.price for x in bollinger_rolling_window]
    lowers.reverse()
    middles.reverse()
    uppers.reverse()
    prices.reverse()
    above_upper = 0
    middle_upper = 0
    lower_middle = 0
    below_lower = 0
    amount_above = 0
    amount_below = .0001
    for i in range(len(lowers)):
        low = lowers[i]
        middle = middles[i]
        high = uppers[i]
        price = prices[i]
        if price >= high:
            above_upper += 1
        elif price >= middle:
            middle_upper += 1
        elif price >= low:
            lower_middle += 1
        else:
            below_lower += 1
        if price >= middle and amount_below == .0001:
            amount_above += (price-middle)
        elif price < middle:
            amount_below += (middle-price)
    most_recent = prices[0]
    current_location = None
    if most_recent >= uppers[0]:
        current_location = "above_upper"
    elif most_recent >= middles[0]:
        current_location = "middle_upper"
    elif most_recent >= lowers[0]:
        current_location = "lower_middle"
    else:
        current_location = "below_lower"
    if trend > 0:
        if current_location == "above_upper" or current_location == "middle_upper":
            if amount_above/amount_below >= bollinger_params['long_threshold']:
                score = 1
            else:
                return .5
    elif trend < 0:
        if current_location == "lower_middle" or current_location == "below_lower":
            if (lower_middle + below_lower) / len(prices) >= bollinger_params['short_threshold']:
                score = 2
    return score
