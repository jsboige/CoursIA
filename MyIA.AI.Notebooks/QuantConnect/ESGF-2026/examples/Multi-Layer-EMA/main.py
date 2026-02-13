from AlgorithmImports import *

class OptimizedCryptoAlgorithm(QCAlgorithm):
    def Initialize(self):
        self.SetStartDate(2022, 1, 1)
        self.SetEndDate(2024, 1, 1)
        self.SetCash(100000)
        self.symbols = [
            self.AddCrypto("BTCUSD", Resolution.HOUR).Symbol,
            self.AddCrypto("ETHUSD", Resolution.HOUR).Symbol,
            self.AddCrypto("LTCUSD", Resolution.HOUR).Symbol
        ]
        self.SetBenchmark("BTCUSD")
        self.fastPeriod = self.GetParameter("fastPeriod", 10)
        self.slowPeriod = self.GetParameter("slowPeriod", 50)
        self.indicators = {}
        for symbol in self.symbols:
            self.indicators[symbol] = {
                "ema10": self.EMA(symbol, self.fastPeriod, Resolution.HOUR),
                "ema50": self.EMA(symbol, self.slowPeriod, Resolution.HOUR),
                "rsi": self.RSI(symbol, 14, MovingAverageType.Wilders, Resolution.HOUR),
                "bollinger": self.BB(symbol, 20, 2, MovingAverageType.Simple, Resolution.HOUR),
                "entry_price": None,
                "stop_loss": None
            }
        self.max_positions = 3
        self.trailing_stop_pct = 0.92
        self.fixed_stop_pct = 0.85
        self.take_profit_pct = 1.3

    def OnData(self, data):
        active_positions = sum(1 for symbol in self.symbols if self.Portfolio[symbol].Invested)
        for symbol in self.symbols:
            if not data.ContainsKey(symbol):
                continue
            price = data[symbol].Close
            indicators = self.indicators[symbol]
            if (active_positions < self.max_positions and
                indicators["rsi"].Current.Value > 30 and
                indicators["ema10"].Current.Value > indicators["ema50"].Current.Value):
                if not self.Portfolio[symbol].Invested:
                    allocation = 0.7 / self.max_positions
                    self.SetHoldings(symbol, allocation)
                    indicators["entry_price"] = price
                    indicators["stop_loss"] = price * self.fixed_stop_pct
                    self.Debug(f"Buy signal triggered for {symbol}. Entry price: {price}")
            if self.Portfolio[symbol].Invested:
                trailing_stop = max(indicators["stop_loss"], price * self.trailing_stop_pct)
                indicators["stop_loss"] = trailing_stop
                if price < trailing_stop:
                    self.Liquidate(symbol)
                    indicators["entry_price"] = None
                    indicators["stop_loss"] = None
                    self.Debug(f"Trailing stop-loss triggered for {symbol}. Liquidated at {price}.")
                elif price > indicators["entry_price"] * self.take_profit_pct:
                    self.Liquidate(symbol)
                    indicators["entry_price"] = None
                    indicators["stop_loss"] = None
                    self.Debug(f"Take profit triggered for {symbol}. Liquidated at {price}.")
