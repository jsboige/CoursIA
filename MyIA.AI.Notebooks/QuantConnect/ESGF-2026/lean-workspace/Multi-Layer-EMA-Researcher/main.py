from AlgorithmImports import *

class OptimizedCryptoAlgorithm(QCAlgorithm):
    def Initialize(self):
        # Extended: covers COVID crash (Mar 2020), bull 2020-2021, bear 2022, recovery 2023-2025
        self.SetStartDate(2020, 1, 1)
        self.SetCash(100000)
        self.symbols = [
            self.AddCrypto("BTCUSD", Resolution.HOUR).Symbol,
            self.AddCrypto("ETHUSD", Resolution.HOUR).Symbol,
            self.AddCrypto("LTCUSD", Resolution.HOUR).Symbol
        ]
        self.SetBenchmark("BTCUSD")
        self.fastPeriod = self.GetParameter("fastPeriod", 10)
        self.slowPeriod = self.GetParameter("slowPeriod", 50)

        # Volatility filter (60% threshold = optimal Sharpe based on research)
        self.volatility_threshold = 0.60
        self.btc_atr = self.ATR(self.symbols[0], 14, MovingAverageType.Simple, Resolution.HOUR)

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
        self.trailing_stop_pct = 0.92  # Optimized from 0.90
        self.fixed_stop_pct = 0.88     # Optimized from 0.85
        self.take_profit_pct = 1.25    # Optimized from 1.30
        self.transaction_fee = 0.001   # 0.1% transaction fee

    def OnData(self, data):
        # Volatility filter: skip trading if BTC volatility > 60%
        if self.btc_atr.IsReady:
            btc_price = data[self.symbols[0]].Close if data.ContainsKey(self.symbols[0]) else None
            if btc_price and btc_price > 0:
                current_vol = (self.btc_atr.Current.Value / btc_price) * (365 * 24) ** 0.5  # Annualized hourly
                if current_vol > self.volatility_threshold:
                    return  # Skip all trading during high volatility

        active_positions = sum(1 for symbol in self.symbols if self.Portfolio[symbol].Invested)
        for symbol in self.symbols:
            if not data.ContainsKey(symbol):
                continue
            price = data[symbol].Close
            indicators = self.indicators[symbol]
            if not indicators["ema10"].IsReady or not indicators["ema50"].IsReady:
                continue
            rsi_val = indicators["rsi"].Current.Value
            ema_fast = indicators["ema10"].Current.Value
            ema_slow = indicators["ema50"].Current.Value
            bb_lower = indicators["bollinger"].LowerBand.Current.Value
            bb_upper = indicators["bollinger"].UpperBand.Current.Value
            if (active_positions < self.max_positions and
                ema_fast > ema_slow and
                30 < rsi_val < 75 and  # Widened from 35-70
                price < bb_upper):
                if not self.Portfolio[symbol].Invested:
                    allocation = 0.7 / self.max_positions
                    self.SetHoldings(symbol, allocation)
                    indicators["entry_price"] = price
                    indicators["stop_loss"] = price * self.fixed_stop_pct
                    self.Debug(f"BUY {symbol} @ {price:.2f} | RSI={rsi_val:.1f} EMA10={ema_fast:.2f} EMA50={ema_slow:.2f}")
            if self.Portfolio[symbol].Invested:
                trailing_stop = max(indicators["stop_loss"], price * self.trailing_stop_pct)
                indicators["stop_loss"] = trailing_stop
                if price < trailing_stop:
                    self.Liquidate(symbol)
                    indicators["entry_price"] = None
                    indicators["stop_loss"] = None
                    self.Debug(f"STOP {symbol} @ {price:.2f}")
                elif price > indicators["entry_price"] * self.take_profit_pct:
                    self.Liquidate(symbol)
                    indicators["entry_price"] = None
                    indicators["stop_loss"] = None
                    self.Debug(f"TP {symbol} @ {price:.2f}")
                elif ema_fast < ema_slow and rsi_val > 75:
                    self.Liquidate(symbol)
                    indicators["entry_price"] = None
                    indicators["stop_loss"] = None
                    self.Debug(f"DEATH CROSS {symbol} @ {price:.2f} | RSI={rsi_val:.1f}")
