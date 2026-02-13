from AlgorithmImports import *
from datetime import timedelta
from collections import deque
import numpy as np

from trendCalculator import get_trend

from macd_oracle import get_macd_score
from bollinger_oracle import get_bollinger_buy_and_short
from rsi_oracle import get_rsi_buy_short

class custom_alpha(AlphaModel):
    # contain bollinger band information
    class bollinger_holder:
        def __init__(self, lower, middle, upper, price):
            self.lower = lower
            self.middle = middle
            self.upper = upper
            self.price = price

    # contain macd information
    class macd_holder:
        def __init__(self, fast, slow, signal, macd, hist):
            self.fast = fast
            self.slow = slow
            self.signal = signal
            self.macd = macd
            self.hist = hist

    def __init__(self, algo):
        self.algo = algo
        self.plotting = False


        # MACD Parameters
        self.macd_params = {'cross_check_length': 35, 'macd_above_below_length': 28, 'long_macd_threshold': 0.25,
                            'short_macd_threshold': -0.25}
        self.macd_candles_history_size = 35

        # Bollinger Band Parameters
        self.Bollinger_window_size = 140
        self.long_threshold = 1
        self.bollinger_params = {'long_threshold': self.long_threshold, 'short_threshold': self.long_threshold}

        # EMA parameters
        self.ema_rolling_window_length = 250
        self.derivative_threshold = .005

        # RSI Parameters
        self.price_rolling_window_length = 90
        self.RSIS_rolling_window_length = 90

        # ADX parameters
        self.adx_rolling_window_length = 35
        self.adx_threshold = 20

        # OBV parameters
        self.obv_rolling_window_length = 250
        self.obv_threshold = .5 # maybe change around

        # ATR parameters
        self.atr_stop_multiplier = 2

        # Trend Parameters
        self.trend_order = 5
        self.K_order = 2
        self.trend_history_size = 210 # 2.5 month

        self.rsi_trend_order = 5
        self.rsi_K_order = 2

        self.obv_trend_order = 2
        self.obv_K_order = 2

        # Portfolio Management Parameters
        self.look_for_entries = {}
        self.entry_scores = {}
        self.hold_length = {}
        self.max_position_size = .15
        self.activeStocks = set()
        self.insight_expiry = 14
        self.insight_expiry_sell = 6
        self.port_bias = 1000

        # Indicators
        self.trend_rolling_windows = {}
        self.MACDS = {}
        self.macd_consolidators = {}
        self.MACDS_rolling_windows = {}
        self.Bollingers = {}
        self.bollinger_consolidators = {}
        self.Bollingers_rolling_windows = {}
        self.RSIS = {}
        self.RSIS_trend = {}
        self.RSIS_rolling_windows = {}
        self.rsi_consolidators = {}
        self.EMAS = {}
        self.EMAS_rolling_windows = {}
        self.ema_consolidators = {}
        self.EMAS50 = {}
        self.EMAS50_rolling_windows = {}
        self.ema50_consolidators = {}
        self.ADX = {}
        self.adx_consolidators = {}
        self.adx_rolling = {}
        self.obvs = {}
        self.obvs_rolling = {}
        self.ATRS = {}
        self.atr_consolidators = {}
        self.peak_prices = {}

        self.universe_type = "equity"
        if self.universe_type != "equity":
            self.universe_equity = algo.AddEquity(self.universe_type, Resolution.Hour).Symbol

        self.symbols_invested_in_last_iteration = set()
        self.symbols_invested_in_last_iteration.add(algo.AddEquity("TYL", Resolution.Hour).Symbol)

    def Update(self, algo, data):
        self.nobuyreasons = []
        insights = []
        if self.symbols_invested_in_last_iteration != None:
            for symbol in self.symbols_invested_in_last_iteration:
                self.activeStocks.add(symbol)
                insight = Insight.price(symbol, timedelta(days=self.insight_expiry), InsightDirection.Up, weight = .75)
                insights.append(insight)
                algo.Log("added initial insight: " + str(symbol))
        self.symbols_invested_in_last_iteration = None


        if self.universe_type != "equity" and self.universe_equity not in self.activeStocks:
            self.activeStocks.add(self.universe_equity)

        for symbol in self.activeStocks:

            # region update indicators

            if not data.ContainsKey(symbol) or data[symbol] is None:
                self.nobuyreasons.append("no data")
                continue

            if not self.MACDS[symbol].IsReady:
                self.nobuyreasons.append("macd not ready")
                continue


            self.trend_rolling_windows[symbol].Add(data[symbol].Close)
            self.Bollingers_rolling_windows[symbol].append(self.bollinger_holder(self.Bollingers[symbol].LowerBand.Current.Value, self.Bollingers[symbol].MiddleBand.Current.Value, self.Bollingers[symbol].UpperBand.Current.Value, data[symbol].price))
            self.MACDS_rolling_windows[symbol].append(self.macd_holder(self.MACDS[symbol].Fast.Current.Value, self.MACDS[symbol].Slow.Current.Value, self.MACDS[symbol].Signal.Current.Value, self.MACDS[symbol].Current.Value, self.MACDS[symbol].histogram.Current.Value))
            self.RSIS_rolling_windows[symbol].Add(self.RSIS_trend[symbol].Current.Value)
            self.EMAS_rolling_windows[symbol].Add(self.EMAS[symbol].Current.Value)
            self.EMAS50_rolling_windows[symbol].Add(self.EMAS50[symbol].Current.Value)
            self.obvs_rolling[symbol].Add(self.obvs[symbol].Current.Value)

            # endregion


            price_trend = get_trend(self.trend_rolling_windows[symbol], self.trend_order, self.K_order)/data[symbol].price
            rsi_trend = get_trend(self.RSIS_rolling_windows[symbol], self.rsi_trend_order, self.rsi_K_order)/self.RSIS[symbol].Current.Value
            obv_trend = get_trend(self.obvs_rolling[symbol], self.obv_trend_order, self.obv_K_order)/self.obvs[symbol].Current.Value


            # if 50 ema has been above 200 ema for a while, trend is up
            ema_trend = 0
            ema50s = [x for x in self.EMAS50_rolling_windows[symbol]]
            ema200s = [x for x in self.EMAS_rolling_windows[symbol]]

            for i in range(len(ema50s)):
                if ema50s[i] > ema200s[i]:
                    ema_trend += 1

            bollinger_score_buy_short = get_bollinger_buy_and_short(algo, self.Bollingers_rolling_windows[symbol], 1, self.bollinger_params)
            macd_score = get_macd_score(self.MACDS_rolling_windows[symbol], 1, self.macd_params)
            rsi_score = get_rsi_buy_short(price_trend, rsi_trend)

            prices = [x for x in self.EMAS50_rolling_windows[symbol]]
            prices.reverse()
            derivative = np.gradient(prices)/self.EMAS50_rolling_windows[symbol][0]

            # buy signal
            if ema_trend >= 210:
                # if in ema uptrend, buy if price between midle and upper bollinger
                if bollinger_score_buy_short == 1:
                    if macd_score == 1:
                        if rsi_score == 1:
                            if derivative[-1] > self.derivative_threshold:
                                if self.ADX[symbol].Current.Value > self.adx_threshold:
                                    max_adx = max(self.adx_rolling[symbol])
                                    current_adx = self.ADX[symbol].Current.Value
                                    if current_adx >= max_adx * .95:
                                        if obv_trend > self.obv_threshold:
                                            open_orders = algo.Transactions.GetOpenOrders(symbol)
                                            if not algo.Portfolio[symbol].Invested and len(open_orders) == 0:
                                                if symbol not in self.look_for_entries or self.look_for_entries[symbol] == 0:
                                                    self.look_for_entries[symbol] = 1
                                                    self.entry_scores[symbol] = abs(int(derivative[-1] * self.ADX[symbol].Current.Value * max(price_trend, 1) * max(rsi_trend, 1) * max(obv_trend, 1) * 100 + self.port_bias))
                                        else:
                                            self.nobuyreasons.append("obv trend too low")
                                    else:
                                        self.nobuyreasons.append("adx not at max")
                                else:
                                    self.nobuyreasons.append("adx below threshold")
                            else:
                                self.nobuyreasons.append("not in derivative uptrend")
                        else:
                            self.nobuyreasons.append("not in rsi uptrend")
                    else:
                        self.nobuyreasons.append("not in macd uptrend")
                else:
                    self.nobuyreasons.append("not in bollinger uptrend")
            else:
                self.nobuyreasons.append("not in ema uptrend")
                if bollinger_score_buy_short == 2:
                    if macd_score == 2:
                        if rsi_score == 2:
                            if derivative[-1] < -self.derivative_threshold:
                                if self.ADX[symbol].Current.Value > self.adx_threshold:
                                    min_adx = min(self.adx_rolling[symbol])
                                    current_adx = self.ADX[symbol].Current.Value
                                    if current_adx <= min_adx * 1.05:
                                        if obv_trend < -self.obv_threshold:
                                            open_orders = algo.Transactions.GetOpenOrders(symbol)
                                            if not algo.Portfolio[symbol].Invested and len(open_orders) == 0:
                                                self.look_for_entries[symbol] = -1
                                                self.entry_scores[symbol] = abs(int(derivative[-1] * self.ADX[symbol].Current.Value * max(price_trend, 1) * max(rsi_trend, 1) * max(obv_trend, 1) * 100 + self.port_bias))

            # generate sell signal
            #if self.RSIS[symbol].Current.Value < 50:
            ###    if algo.Portfolio[symbol].Invested and algo.Portfolio[symbol].IsLong:
            #        insight = Insight.price(symbol, timedelta(days=self.insight_expiry_sell), InsightDirection.Flat, weight = 1)
            #        insights.append(insight)
            #if self.RSIS[symbol].Current.Value > 50:
            #    if algo.Portfolio[symbol].Invested and algo.Portfolio[symbol].IsShort:
            #        insight = Insight.price(symbol, timedelta(days=self.insight_expiry_sell), InsightDirection.Flat, weight = 1)
            #        insights.append(insight)

            if self.plotting:
                if symbol in self.peak_prices and self.peak_prices[symbol] != None:
                    algo.Plot("price", "atr trail", self.peak_prices[symbol] - self.atr_stop_multiplier * self.ATRS[symbol].Current.Value)
                    algo.Plot("price", "peak", self.peak_prices[symbol])
                algo.Plot("atr", "atr", self.ATRS[symbol].Current.Value)
                algo.Plot("macd", "macd", self.MACDS[symbol].Current.Value)
                algo.Plot("adx", "adx", self.ADX[symbol].Current.Value)
                algo.Plot("obv trend", "obv trend", obv_trend)
                algo.Plot("obv", "obv", self.obvs[symbol].Current.Value)
                algo.Plot("trend", "price_trend", price_trend)
                algo.Plot("trend", "rsi_trend", rsi_trend)
                algo.Plot("rsi", "rsi", self.RSIS[symbol].Current.Value)

                algo.Plot("price", "ema50", self.EMAS50[symbol].Current.Value)
                algo.Plot("price", "ema200", self.EMAS[symbol].Current.Value)

                algo.Plot("bollinger_score", "bollinger_score", bollinger_score_buy_short)
                algo.Plot("macd_score", "macd_score", macd_score)
                algo.Plot("rsi_score", "rsi_score", rsi_score)

                algo.Plot("derivative", "derivative", derivative[-1])

                algo.Plot("ema_trend: ", "ema_trend", ema_trend)
                algo.Plot("price", "price", data[symbol].Close)
                algo.Plot("price", "bollinger_middle", self.Bollingers[symbol].MiddleBand.Current.Value)
                algo.Plot("price", "bollinger_upper", self.Bollingers[symbol].UpperBand.Current.Value)
                algo.Plot("trend", "price_trend", price_trend)

        # print out by order of most the nobuyreasons and their number of occurences
        for reason in sorted(set(self.nobuyreasons), key = lambda x: self.nobuyreasons.count(x), reverse = True):
            algo.Log(reason + ": " + str(self.nobuyreasons.count(reason)))



        if len(self.look_for_entries.keys()) > 0:
            for key in self.look_for_entries:
                if self.look_for_entries[key] > 0:
                    self.look_for_entries[key] += 1
                    if self.look_for_entries[key] > 70:
                        self.look_for_entries[key] = 0
                        self.hold_length[key] = None
                    else:
                        #self.Log("Looking for entry for: " + str(key))
                        if data[key].price > self.Bollingers[key].MiddleBand.Current.Value:
                            #insight = Insight(key, timedelta(days=2), InsightType.PRICE, InsightDirection.Down, self.entry_scores[key])
                            insight = Insight.price(key, timedelta(days=self.insight_expiry), InsightDirection.Up, weight = self.entry_scores[key])
                            self.peak_prices[key] = data[key].price
                            self.hold_length[key] = 1
                            insights.append(insight)
                            self.look_for_entries[key] = 0
                elif self.look_for_entries[key] < 0:
                    self.look_for_entries[key] -= 1
                    if self.look_for_entries[key] < -70:
                        self.look_for_entries[key] = 0
                        self.hold_length[key] = None
                    else:
                        #self.Log("Looking for entry for: " + str(key))
                        if data[key].price < self.Bollingers[key].MiddleBand.Current.Value:
                            #insight = Insight(key, timedelta(days=2), InsightType.PRICE, InsightDirection.Down, self.entry_scores[key])
                            insight = Insight.price(key, timedelta(days=self.insight_expiry), InsightDirection.Down, weight = self.entry_scores[key])
                            insights.append(insight)
                            self.peak_prices[key] = data[key].price
                            self.hold_length[key] = -1
                            self.look_for_entries[key] = 0
            # endregion

        added_insights = self.atr_trail_stop_loss(algo, data)
        for insight in added_insights:
            insights.append(insight)
        return insights

    def atr_trail_stop_loss(self, algo, data):
        added_insights = []
        for key in algo.Portfolio.Keys:
            if key in self.peak_prices and self.peak_prices[key] != None and key in self.hold_length:
                if self.hold_length[key] != None:
                    self.hold_length[key] += 1
                if algo.Portfolio[key].IsLong:
                    if key in data and data[key] != None:
                        price = data[key].price
                    else:
                        price = self.trend_rolling_windows[key][0]
                    if price > self.peak_prices[key]:
                        self.peak_prices[key] = price
                    if price < self.peak_prices[key] - self.atr_stop_multiplier * self.ATRS[key].Current.Value:
                        added_insights.append(Insight.price(key, timedelta(days=7), InsightDirection.Flat, weight = 1))
                        algo.Liquidate(key)
                        self.hold_length[key] = None
                        self.peak_prices[key] = None
                else:
                    if key in data and data[key] != None:
                        price = data[key].price
                    else:
                        price = self.trend_rolling_windows[key][0]
                    if price < self.peak_prices[key]:
                        self.peak_prices[key] = price
                    if price > self.peak_prices[key] + self.atr_stop_multiplier * self.ATRS[key].Current.Value:
                        added_insights.append(Insight.price(key, timedelta(days=7), InsightDirection.Flat, weight = 1))
                        algo.Liquidate(key)
                        self.hold_length[key] = None
                        self.peak_prices[key] = None
        return added_insights

    def OnSecuritiesChanged(self, algo, changes):
        # region removed securities
        for x in changes.RemovedSecurities:
            self.activeStocks.remove(x.Symbol)

        # can't open positions here since data might not be added correctly yet
        for x in changes.AddedSecurities:
            self.activeStocks.add(x.Symbol)

            self.trend_rolling_windows[x.Symbol] = RollingWindow[float](self.price_rolling_window_length)

            self.MACDS[x.Symbol] = MovingAverageConvergenceDivergence(12, 26, 9, MovingAverageType.Exponential)
            self.macd_consolidators[x.Symbol] = TradeBarConsolidator(timedelta(days=1))
            algo.register_indicator(x.Symbol, self.MACDS[x.Symbol], self.macd_consolidators[x.Symbol])
            self.MACDS_rolling_windows[x.Symbol] = deque(maxlen=self.macd_candles_history_size)

            self.Bollingers[x.Symbol] = BollingerBands(20, 2, MovingAverageType.Simple)
            self.bollinger_consolidators[x.Symbol] = TradeBarConsolidator(timedelta(days=1))
            algo.register_indicator(x.Symbol, self.Bollingers[x.Symbol], self.bollinger_consolidators[x.Symbol])
            self.Bollingers_rolling_windows[x.Symbol] = deque(maxlen=self.Bollinger_window_size)

            self.RSIS_trend[x.Symbol] = algo.rsi(x.Symbol, 14, Resolution.Hour)
            self.RSIS[x.Symbol] = RelativeStrengthIndex(14)
            self.rsi_consolidators[x.Symbol] = TradeBarConsolidator(timedelta(days=1))
            algo.register_indicator(x.Symbol, self.RSIS[x.Symbol], self.rsi_consolidators[x.Symbol])
            self.RSIS_rolling_windows[x.Symbol] = RollingWindow[float](self.RSIS_rolling_window_length)

            self.EMAS[x.Symbol] = ExponentialMovingAverage(200)
            self.ema_consolidators[x.Symbol] = TradeBarConsolidator(timedelta(days=1))
            algo.register_indicator(x.Symbol, self.EMAS[x.Symbol], self.ema_consolidators[x.Symbol])
            self.EMAS_rolling_windows[x.Symbol] = RollingWindow[float](self.ema_rolling_window_length)

            self.EMAS50[x.Symbol] = ExponentialMovingAverage(50)
            self.ema50_consolidators[x.Symbol] = TradeBarConsolidator(timedelta(days=1))
            algo.register_indicator(x.Symbol, self.EMAS50[x.Symbol], self.ema50_consolidators[x.Symbol])
            self.EMAS50_rolling_windows[x.Symbol] = RollingWindow[float](self.ema_rolling_window_length)

            self.ADX[x.Symbol] = AverageDirectionalIndex(14)
            self.adx_consolidators[x.Symbol] = TradeBarConsolidator(timedelta(days=1))
            algo.register_indicator(x.Symbol, self.ADX[x.Symbol], self.adx_consolidators[x.Symbol])
            self.adx_rolling[x.Symbol] = RollingWindow[float](self.adx_rolling_window_length)

            self.obvs[x.Symbol] = algo.obv(x.Symbol)
            self.obvs_rolling[x.Symbol] = RollingWindow[float](self.obv_rolling_window_length)

            self.ATRS[x.Symbol] = AverageTrueRange(14)
            self.atr_consolidators[x.Symbol] = TradeBarConsolidator(timedelta(days=1))
            algo.register_indicator(x.Symbol, self.ATRS[x.Symbol], self.atr_consolidators[x.Symbol])

            history = algo.History[TradeBar](x.Symbol,self.ema_rolling_window_length*3, Resolution.Hour)
            history2 = algo.History[TradeBar](x.Symbol,self.ema_rolling_window_length*3, Resolution.Daily)
            for bar in history:
                self.RSIS_trend[x.Symbol].Update(bar.EndTime, bar.Close)
                self.RSIS_rolling_windows[x.Symbol].Add(self.RSIS_trend[x.Symbol].Current.Value)

            for bar in history2:
                self.trend_rolling_windows[x.Symbol].Add(bar.Close)

                self.MACDS[x.Symbol].Update(bar.EndTime, bar.Close)
                new_macd = self.macd_holder(self.MACDS[x.Symbol].Fast.Current.Value, self.MACDS[x.Symbol].Slow.Current.Value, self.MACDS[x.Symbol].Signal.Current.Value, self.MACDS[x.Symbol].Current.Value, self.MACDS[x.Symbol].histogram.Current.Value)
                self.MACDS_rolling_windows[x.Symbol].append(new_macd)

                self.Bollingers[x.Symbol].Update(bar.EndTime, bar.Close)
                new_bol = self.bollinger_holder(self.Bollingers[x.Symbol].LowerBand.Current.Value, self.Bollingers[x.Symbol].MiddleBand.Current.Value, self.Bollingers[x.Symbol].UpperBand.Current.Value, bar.Close)
                self.Bollingers_rolling_windows[x.Symbol].append(new_bol)

                self.RSIS[x.Symbol].Update(bar.EndTime, bar.Close)

                self.EMAS[x.Symbol].Update(bar.EndTime, bar.Close)
                self.EMAS_rolling_windows[x.Symbol].Add(self.EMAS[x.Symbol].Current.Value)
                self.EMAS50[x.Symbol].Update(bar.EndTime, bar.Close)
                self.EMAS50_rolling_windows[x.Symbol].Add(self.EMAS50[x.Symbol].Current.Value)

                self.ADX[x.Symbol].Update(bar)
                self.adx_rolling[x.Symbol].Add(self.ADX[x.Symbol].Current.Value)

                self.obvs[x.Symbol].Update(bar)
                self.obvs_rolling[x.Symbol].Add(self.obvs[x.Symbol].Current.Value)

                self.ATRS[x.Symbol].Update(bar)
