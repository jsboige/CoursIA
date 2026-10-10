#region imports
from AlgorithmImports import *
from datetime import datetime
#endregion
# https://www.quantconnect.com/strategies/60
# Leveraged ETF Momentum Allocator by Grant Forman
# OOS 1Y Sharpe 1.80, 5Y CAGR 101.03%, 5Y Drawdown 47.50%, 54% Win Rate
# Conditional sector rotation using leveraged ETFs with RSI + SMA regime detection
# Source: QC Strategy Library #60, cloned 2026-04-04, QC Project ID: 29687520
#
# Instrumentation de mesure (#19587) : parametres start/end (defauts = dates du code
# d'origine), mode (base = regle d'origine ; sma200 = controle : TQQQ quand SPY est
# au-dessus de sa SMA, BSV sinon, sans aucun seuil RSI ; tqqq, spy, qqq = l'ETF detenu
# a 100 %), fee_mult (1 = frais inchanges). Valeur du portefeuille a chaque cloture dans
# le graphique "shadow" (contrat de rejeu en ombre, #18923). Le prechauffage couvre la
# plus longue periode d'indicateur (200 avec les defauts, comme a l'origine).
# prices = adjusted (defaut, comme a l'origine) ou raw ; signal = indicators (defaut) ou
# history (memes RSI de Wilder et SMA, recalcules chaque jour sur l'historique ajuste).
# En prix ajustes, une part d'UVXY ou de TECS vaut des centaines de milliers de dollars en
# debut de periode : l'ordre arrondit a zero part et la branche reste en liquide. Le couple
# raw + history execute la regle avec des nombres de parts realistes (#19587).


class _ScaledFeeModel(FeeModel):
    """Frais du courtier (modele par defaut de Lean), mis a l'echelle (identite a 1.0)."""

    def __init__(self, multiplier):
        self._multiplier = multiplier
        self._base = InteractiveBrokersFeeModel()

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None or self._multiplier == 1.0:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))


HOLD_MODES = {"tqqq": "TQQQ", "spy": "SPY", "qqq": "QQQ"}


class ConditionalSectorRotation(QCAlgorithm):

    def Initialize(self):
        # 1. Set Strategy Settings
        start = datetime.strptime(self.GetParameter("start") or "2015-01-01", "%Y-%m-%d")
        end = datetime.strptime(self.GetParameter("end") or "2024-12-31", "%Y-%m-%d")
        self.SetStartDate(start.year, start.month, start.day)
        self.set_end_date(end.year, end.month, end.day)  # Extended for robustness (UVXY from Oct 2011)
        self.SetCash(100000)  # Set your starting capital
        self.SetBrokerageModel(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self.mode = self.GetParameter("mode") or "base"
        if self.mode not in ("base", "sma200") and self.mode not in HOLD_MODES:
            raise ValueError(f"mode inconnu : {self.mode}")
        self.prices = self.GetParameter("prices") or "adjusted"
        self.signal = self.GetParameter("signal") or "indicators"
        if self.prices not in ("adjusted", "raw") or self.signal not in ("indicators", "history"):
            raise ValueError(f"prices/signal inconnus : {self.prices}/{self.signal}")
        if self.prices == "raw" and self.signal != "history":
            raise ValueError("prix bruts : signal history obligatoire (indicateurs sur prix bruts faux aux splits)")
        self.fee_mult = float(self.GetParameter("fee_mult") or 1)
        if self.fee_mult != 1.0:
            self.SetSecurityInitializer(
                lambda security: security.SetFeeModel(_ScaledFeeModel(self.fee_mult)))
        rsi_period_str = self.get_parameter("rsi_period", 10)
        self.rsi_period = int(rsi_period_str)


        spy_sma_period_str = self.get_parameter("spy_sma_period", 200)
        self.spy_sma_period = int(spy_sma_period_str)

        qqq_sma_period_str = self.get_parameter("qqq_sma_period", 20)
        self.qqq_sma_period = int(qqq_sma_period_str)

        tqqq_sma_period_str = self.get_parameter("tqqq_sma_period", 20)
        self.tqqq_sma_period = int(tqqq_sma_period_str)

        # 2. Define the Universe of Tickers
        self.tickers = [
            "SPY", "QQQ", "TQQQ", "UVXY",
            "TECL", "SPXL", "SQQQ", "TECS", "BSV"
        ]

        self.symbols = {}
        self.indicators = {}

        # 3. Initialize Assets and Indicators
        for ticker in self.tickers:
            # Add Equity with Daily resolution for standard MA/RSI calculation
            symbol = self.AddEquity(ticker, Resolution.Daily).Symbol
            if self.prices == "raw":
                self.Securities[symbol].SetDataNormalizationMode(DataNormalizationMode.Raw)
            self.symbols[ticker] = symbol

            # Initialize RSI for all assets (Standard 14 period)

            self.indicators[f"{ticker}_RSI_{self.rsi_period}_day"] = self.RSI(symbol, self.rsi_period, MovingAverageType.Wilders, Resolution.Daily)

        # 4. Initialize Specific Moving Averages required by logic
        self.indicators["SPY_SMA200"] = self.SMA(self.symbols["SPY"], self.spy_sma_period, Resolution.Daily)
        self.indicators["QQQ_SMA20"] = self.SMA(self.symbols["QQQ"], self.qqq_sma_period, Resolution.Daily)
        self.indicators["TQQQ_SMA20"] = self.SMA(self.symbols["TQQQ"], self.tqqq_sma_period, Resolution.Daily)

        # 5. Warm Up Period
        self.SetWarmUp(max(200, self.rsi_period, self.spy_sma_period,
                           self.qqq_sma_period, self.tqqq_sma_period))

        # Comptes du graphique shadow (contrat #18923) et jours de detention par ETF
        self.start_value = 100000.0
        self.closes = 0
        self.traded = 0.0
        self.days_on = {}

    def OnOrderEvent(self, event):
        if event.Status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            self.traded += (abs(event.FillQuantity * event.FillPrice) / self.Portfolio.TotalPortfolioValue)

    def OnEndOfAlgorithm(self):
        for ticker, days in sorted(self.days_on.items()):
            self.SetRuntimeStatistic(f"days_{ticker}", str(days))

    def OnData(self, data):
        # Ensure data is ready before running logic
        if self.IsWarmingUp: return

        if data.Bars.ContainsKey(self.symbols["SPY"]):
            self.Plot("shadow", f"e{self.closes % 5}", self.Portfolio.TotalPortfolioValue)
            self.Plot("shadow", "fees", self.Portfolio.TotalFees / self.start_value)
            self.Plot("shadow", "turnover", self.traded)
            self.closes += 1

        if self.mode != "base":
            self.TradeControl()
            return

        # -------------------------------------------------------------
        # RETRIEVE CURRENT VALUES
        # -------------------------------------------------------------

        # Prices
        price_spy = self.Securities[self.symbols["SPY"]].Price
        price_qqq = self.Securities[self.symbols["QQQ"]].Price
        price_tqqq = self.Securities[self.symbols["TQQQ"]].Price

        # Indicators (Values)
        rsi_10_day_qqq = self.indicators[f"QQQ_RSI_{self.rsi_period}_day"].Current.Value
        rsi_10_day_spy = self.indicators[f"SPY_RSI_{self.rsi_period}_day"].Current.Value

        rsi_10_day_tqqq = self.indicators[f"TQQQ_RSI_{self.rsi_period}_day"].Current.Value
        rsi_10_day_sqqq = self.indicators[f"SQQQ_RSI_{self.rsi_period}_day"].Current.Value
        rsi_10_day_uvxy = self.indicators[f"UVXY_RSI_{self.rsi_period}_day"].Current.Value

        sma_spy_200 = self.indicators["SPY_SMA200"].Current.Value
        sma_qqq_20 = self.indicators["QQQ_SMA20"].Current.Value
        sma_tqqq_20 = self.indicators["TQQQ_SMA20"].Current.Value

        rsi_override = None
        if self.signal == "history":
            sig = self.HistorySignals()
            if sig is None:
                return
            rsi_override, price_spy, price_qqq, price_tqqq, sma_spy_200, sma_qqq_20, sma_tqqq_20 = sig
            rsi_10_day_qqq = rsi_override["QQQ"]
            rsi_10_day_spy = rsi_override["SPY"]
            rsi_10_day_tqqq = rsi_override["TQQQ"]
            rsi_10_day_sqqq = rsi_override["SQQQ"]
            rsi_10_day_uvxy = rsi_override["UVXY"]

        target_ticker = None

        # -------------------------------------------------------------
        # EXECUTE LOGIC TREE
        # -------------------------------------------------------------

        # ROOT CHECK: SPY Price vs 200 SMA
        if price_spy > sma_spy_200:
            # Bull Market Logic
            if rsi_10_day_qqq > 81:
                target_ticker = "UVXY"
            elif rsi_10_day_spy > 80:
                target_ticker = "UVXY"
            else:
                target_ticker = "TQQQ"

        else:
            # Bear/Volatile Market Logic (SPY <= 200 SMA)
            if rsi_10_day_tqqq < 30:
                target_ticker = "TECL"
            elif rsi_10_day_spy < 30:
                target_ticker = "SPXL"
            elif rsi_10_day_uvxy > 74:
                # High Volatility Branch
                if rsi_10_day_uvxy > 84:
                    if price_qqq > sma_qqq_20:
                        if rsi_10_day_sqqq < 31:
                            target_ticker = "TECS"
                        else:
                            target_ticker = "TECL"
                    else:
                        # Select top RSI from TECS and BSV
                        target_ticker = self.GetMaxRsiAsset(["TECS", "BSV"], self.rsi_period, rsi_override)
                else:
                    # UVXY is > 74 but <= 84
                    target_ticker = "UVXY"
            else:
                # Final "Otherwise" Branch (UVXY <= 74)
                if price_tqqq > sma_tqqq_20:
                    if rsi_10_day_sqqq < 34:
                        target_ticker = "TECS"
                    else:
                        target_ticker = "TECL"
                else:
                    # Select top RSI from TECS and BSV
                    target_ticker = self.GetMaxRsiAsset(["TECS", "BSV"], self.rsi_period, rsi_override)

        # -------------------------------------------------------------
        # EXECUTE TRADE
        # -------------------------------------------------------------
        if target_ticker:
            # liquidates all other holdings and puts 100% into target
            self.SetHoldings(self.symbols[target_ticker], 1.0, liquidateExistingHoldings=True)
            self.days_on[target_ticker] = self.days_on.get(target_ticker, 0) + 1

    def TradeControl(self):
        """Controles et references (#19587) : meme univers, memes frais, meme cadence."""
        if self.mode == "sma200":
            price_spy = self.Securities[self.symbols["SPY"]].Price
            sma_spy = self.indicators["SPY_SMA200"].Current.Value
            if self.signal == "history":
                sig = self.HistorySignals()
                if sig is None:
                    return
                price_spy, sma_spy = sig[1], sig[4]
            target_ticker = "TQQQ" if price_spy > sma_spy else "BSV"
        else:
            target_ticker = HOLD_MODES[self.mode]
        self.SetHoldings(self.symbols[target_ticker], 1.0, liquidateExistingHoldings=True)
        self.days_on[target_ticker] = self.days_on.get(target_ticker, 0) + 1

    def HistorySignals(self):
        """RSI de Wilder et SMA sur l'historique ajuste (signal=history, #19587).

        Meme definition que les indicateurs de Lean : moyenne simple des `period` premiers
        ecarts, puis lissage de Wilder ; 400 seances, soit un ecart de depart negligeable.
        """
        symbols = [self.symbols[t] for t in self.tickers]
        hist = self.History(symbols, 400, Resolution.Daily,
                            dataNormalizationMode=DataNormalizationMode.Adjusted)
        if hist.empty:
            return None
        closes = {}
        for t in self.tickers:
            try:
                closes[t] = hist.loc[self.symbols[t]]["close"].values.astype(float)
            except KeyError:
                return None
        rsi = {t: self._wilder_rsi(closes[t], self.rsi_period) for t in self.tickers}
        if any(v is None for v in rsi.values()):
            return None
        def sma(t, n):
            c = closes[t]
            return float(c[-n:].mean()) if len(c) >= n else None
        smas = (sma("SPY", self.spy_sma_period), sma("QQQ", self.qqq_sma_period),
                sma("TQQQ", self.tqqq_sma_period))
        if any(v is None for v in smas):
            return None
        return (rsi, closes["SPY"][-1], closes["QQQ"][-1], closes["TQQQ"][-1], *smas)

    @staticmethod
    def _wilder_rsi(values, period):
        if len(values) <= period:
            return None
        gain = loss = 0.0
        for i in range(1, len(values)):
            change = values[i] - values[i - 1]
            g, l = max(change, 0.0), max(-change, 0.0)
            if i <= period:
                gain += (g - gain) / i
                loss += (l - loss) / i
            else:
                gain = (gain * (period - 1) + g) / period
                loss = (loss * (period - 1) + l) / period
        if loss == 0.0:
            return 100.0 if gain > 0.0 else 50.0
        return 100.0 - 100.0 / (1.0 + gain / loss)

    def GetMaxRsiAsset(self, ticker_list, rsi_days, rsi_override=None):
        """Helper to compare RSIs and return the ticker with the highest value"""
        best_ticker = None
        highest_rsi = -1

        for ticker in ticker_list:
            if rsi_override is not None:
                rsi_val = rsi_override[ticker]
            else:
                rsi_val = self.indicators[f"{ticker}_RSI_{rsi_days}_day"].Current.Value
            if rsi_val > highest_rsi:
                highest_rsi = rsi_val
                best_ticker = ticker

        return best_ticker
