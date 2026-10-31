from AlgorithmImports import *

class OptimizedCryptoAlgorithm(QCAlgorithm):
    def Initialize(self):
        # Extended: covers COVID crash (Mar 2020), bull 2020-2021, bear 2022, recovery 2023-2025
        # Start date 2018: Binance BTCUSDT data available on QC Cloud from ~2017
        # Protocole #23460 : `start_date` / `end_date` choisissent la fenetre
        # (defaut : celle du README).
        start = self.GetParameter("start_date", "2018-01-01")
        end = self.GetParameter("end_date", "2024-12-31")
        self.SetStartDate(*[int(x) for x in start.split("-")])
        self.SetEndDate(*[int(x) for x in end.split("-")])
        self.SetCash(100000)
        self.SetAccountCurrency("USDT")
        self.SetBrokerageModel(BrokerageName.Binance, AccountType.Cash)
        self.symbols = [
            self.AddCrypto("BTCUSDT", Resolution.DAILY, Market.BINANCE).Symbol,
            self.AddCrypto("ETHUSDT", Resolution.DAILY, Market.BINANCE).Symbol,
            self.AddCrypto("LTCUSDT", Resolution.DAILY, Market.BINANCE).Symbol
        ]
        self.SetBenchmark("BTCUSDT")
        self.fastPeriod = self.GetParameter("fastPeriod", 10)
        self.slowPeriod = self.GetParameter("slowPeriod", 50)

        # `gate` : portee du filtre de volatilite (#23460).
        #   entries (defaut) : le filtre bloque les nouvelles entrees ; stops,
        #     prise de benefice et sortie sur croisement sont evalues chaque jour.
        #   legacy : comportement d'origine, le filtre saute tout OnData, sorties
        #     comprises (les stops sont suspendus tant qu'il est actif).
        self.gate = self.GetParameter("gate", "entries").lower()
        if self.gate not in ("entries", "legacy"):
            raise ValueError(f"unknown gate parameter: {self.gate} (expected entries or legacy)")
        # `mode` : strategy (defaut) ou reference detenue achetee le premier jour
        #   btc  : BTC seul ; ew70 : BTC, ETH, LTC a 0,7/3 chacun (exposition
        #   maximale de la strategie).
        self.mode = self.GetParameter("mode", "strategy").lower()
        if self.mode not in ("strategy", "btc", "ew70"):
            raise ValueError(f"unknown mode parameter: {self.mode} (expected strategy, btc or ew70)")
        self.reference_bought = False

        # Volatility filter (60% threshold = optimal Sharpe based on research)
        self.volatility_threshold = 0.60
        self.btc_atr = self.ATR(self.symbols[0], 14, MovingAverageType.Simple, Resolution.DAILY)

        self.indicators = {}
        for symbol in self.symbols:
            self.indicators[symbol] = {
                "ema10": self.EMA(symbol, self.fastPeriod, Resolution.DAILY),
                "ema50": self.EMA(symbol, self.slowPeriod, Resolution.DAILY),
                "rsi": self.RSI(symbol, 14, MovingAverageType.Wilders, Resolution.DAILY),
                "bollinger": self.BB(symbol, 20, 2, MovingAverageType.Simple, Resolution.DAILY),
                "entry_price": None,
                "stop_loss": None
            }
        self.max_positions = 3
        self.trailing_stop_pct = 0.92  # Optimized from 0.90
        self.fixed_stop_pct = 0.88     # Optimized from 0.85
        self.take_profit_pct = 1.25    # Optimized from 1.30

        # Mesures #23460 (statistiques d'execution, sans effet sur la decision).
        self.gate_days = 0             # jours ou le filtre est actif
        self.gate_days_invested = 0    # dont jours avec une ligne detenue
        self.suspended_breaches = 0    # legacy : cloture sous le stop, sans sortie
        self.gate_stop_exits = 0       # entries : stops declenches un jour de filtre
        self.stop_exits = 0
        self.max_stop_overshoot = 0.0  # (stop - cloture) / stop au declenchement

        # Trace `shadow` (#18923) : valeur du portefeuille une fois par barre
        # journaliere, dans e0..e4.
        self.trace_count = 0

    def _trace(self):
        self.Plot("shadow", f"e{self.trace_count % 5}", self.Portfolio.TotalPortfolioValue)
        self.trace_count += 1

    def _buy_reference(self, data):
        if self.reference_bought:
            return
        if not all(data.ContainsKey(s) for s in self.symbols):
            return
        if self.mode == "btc":
            # 0.98 : marge pour les frais d'un compte cash.
            self.SetHoldings(self.symbols[0], 0.98)
        else:
            for symbol in self.symbols:
                self.SetHoldings(symbol, 0.7 / 3)
        self.reference_bought = True

    def _gate_active(self, data):
        if not self.btc_atr.IsReady:
            return False
        btc_price = data[self.symbols[0]].Close if data.ContainsKey(self.symbols[0]) else None
        if not btc_price or btc_price <= 0:
            return False
        current_vol = (self.btc_atr.Current.Value / btc_price) * (252) ** 0.5  # Annualized daily
        return current_vol > self.volatility_threshold

    def OnData(self, data):
        if self.mode != "strategy":
            self._buy_reference(data)
            self._trace()
            return
        self._trace()

        # Volatility filter: skip trading if BTC volatility > 60%
        gate_on = self._gate_active(data)
        if gate_on:
            self.gate_days += 1
            if any(self.Portfolio[s].Invested for s in self.symbols):
                self.gate_days_invested += 1
            if self.gate == "legacy":
                for symbol in self.symbols:
                    stop = self.indicators[symbol]["stop_loss"]
                    if (self.Portfolio[symbol].Invested and stop is not None
                            and data.ContainsKey(symbol) and data[symbol].Close < stop):
                        self.suspended_breaches += 1
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
            if (not gate_on and
                active_positions < self.max_positions and
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
                previous_stop = indicators["stop_loss"]
                trailing_stop = max(indicators["stop_loss"], price * self.trailing_stop_pct)
                indicators["stop_loss"] = trailing_stop
                if price < trailing_stop:
                    self.stop_exits += 1
                    if gate_on:
                        self.gate_stop_exits += 1
                    self.max_stop_overshoot = max(self.max_stop_overshoot,
                                                  (previous_stop - price) / previous_stop)
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

    def OnEndOfAlgorithm(self):
        self.SetRuntimeStatistic("gate_days", str(self.gate_days))
        self.SetRuntimeStatistic("gate_days_invested", str(self.gate_days_invested))
        self.SetRuntimeStatistic("suspended_breaches", str(self.suspended_breaches))
        self.SetRuntimeStatistic("stop_exits", str(self.stop_exits))
        self.SetRuntimeStatistic("gate_stop_exits", str(self.gate_stop_exits))
        self.SetRuntimeStatistic("max_stop_overshoot", f"{self.max_stop_overshoot:.4f}")
