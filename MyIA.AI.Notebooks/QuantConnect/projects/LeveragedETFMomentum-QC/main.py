#region imports
from AlgorithmImports import *
#endregion
# https://www.quantconnect.com/strategies/60
# Leveraged ETF Momentum Allocator by Grant Forman
# OOS 1Y Sharpe 1.80, 5Y CAGR 101.03%, 5Y Drawdown 47.50%, 54% Win Rate
# Conditional sector rotation using leveraged ETFs with RSI + SMA regime detection
# Source: QC Strategy Library #60, cloned 2026-04-04, QC Project ID: 29687520


class ConditionalSectorRotation(QCAlgorithm):

    def Initialize(self):
        # 1. Set Strategy Settings
        self.SetStartDate(2011, 1, 1)  # Extended for robustness (UVXY from Oct 2011)
        self.SetCash(100000)  # Set your starting capital
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
            self.symbols[ticker] = symbol

            # Initialize RSI for all assets (Standard 14 period)

            self.indicators[f"{ticker}_RSI_{self.rsi_period}_day"] = self.RSI(symbol, self.rsi_period, MovingAverageType.Wilders, Resolution.Daily)

        # 4. Initialize Specific Moving Averages required by logic
        self.indicators["SPY_SMA200"] = self.SMA(self.symbols["SPY"], self.spy_sma_period, Resolution.Daily)
        self.indicators["QQQ_SMA20"] = self.SMA(self.symbols["QQQ"], self.qqq_sma_period, Resolution.Daily)
        self.indicators["TQQQ_SMA20"] = self.SMA(self.symbols["TQQQ"], self.tqqq_sma_period, Resolution.Daily)

        # 5. Warm Up Period
        self.SetWarmUp(200)

    def OnData(self, data):
        # Ensure data is ready before running logic
        if self.IsWarmingUp: return

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
                        target_ticker = self.GetMaxRsiAsset(["TECS", "BSV"], self.rsi_period)
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
                    target_ticker = self.GetMaxRsiAsset(["TECS", "BSV"], self.rsi_period)

        # -------------------------------------------------------------
        # EXECUTE TRADE
        # -------------------------------------------------------------
        if target_ticker:
            # liquidates all other holdings and puts 100% into target
            self.SetHoldings(self.symbols[target_ticker], 1.0, liquidateExistingHoldings=True)

    def GetMaxRsiAsset(self, ticker_list, rsi_days):
        """Helper to compare RSIs and return the ticker with the highest value"""
        best_ticker = None
        highest_rsi = -1

        for ticker in ticker_list:
            rsi_val = self.indicators[f"{ticker}_RSI_{rsi_days}_day"].Current.Value
            if rsi_val > highest_rsi:
                highest_rsi = rsi_val
                best_ticker = ticker

        return best_ticker
