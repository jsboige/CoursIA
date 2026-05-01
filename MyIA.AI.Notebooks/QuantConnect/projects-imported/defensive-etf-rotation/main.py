#region imports
from AlgorithmImports import *
#endregion
# Defensive ETF Rotation (Conditional Sector Rotation)
# Source: QC Strategy Library
# Concept: RSI-based conditional rotation among equity, leveraged, and inverse ETFs.
# Uses SPY 200-SMA regime filter with nested RSI conditions for target selection.
# 100% concentrated single-position, configurable parameters.
# Imported from QC Cloud Project ID: 29687520


class ConditionalSectorRotation(QCAlgorithm):

    def initialize(self):
        self.set_start_date(2011, 1, 1)
        self.set_cash(100000)

        rsi_period_str = self.get_parameter("rsi_period", 10)
        self.rsi_period = int(rsi_period_str)
        spy_sma_period_str = self.get_parameter("spy_sma_period", 200)
        self.spy_sma_period = int(spy_sma_period_str)
        qqq_sma_period_str = self.get_parameter("qqq_sma_period", 20)
        self.qqq_sma_period = int(qqq_sma_period_str)
        tqqq_sma_period_str = self.get_parameter("tqqq_sma_period", 20)
        self.tqqq_sma_period = int(tqqq_sma_period_str)

        self.tickers = [
            "SPY", "QQQ", "TQQQ", "UVXY", "TECL",
            "SPXL", "SQQQ", "TECS", "BSV",
        ]
        self.symbols = {}
        self.indicators = {}

        for ticker in self.tickers:
            symbol = self.add_equity(ticker, Resolution.DAILY).symbol
            self.symbols[ticker] = symbol
            self.indicators[f"{ticker}_RSI_{self.rsi_period}_day"] = self.RSI(
                symbol, self.rsi_period, MovingAverageType.Wilders,
                Resolution.DAILY,
            )

        self.indicators["SPY_SMA200"] = self.SMA(
            self.symbols["SPY"], self.spy_sma_period, Resolution.DAILY,
        )
        self.indicators["QQQ_SMA20"] = self.SMA(
            self.symbols["QQQ"], self.qqq_sma_period, Resolution.DAILY,
        )
        self.indicators["TQQQ_SMA20"] = self.SMA(
            self.symbols["TQQQ"], self.tqqq_sma_period, Resolution.DAILY,
        )

        self.set_warm_up(200)

    def on_data(self, data):
        if self.is_warming_up:
            return

        price_spy = self.securities[self.symbols["SPY"]].price
        price_qqq = self.securities[self.symbols["QQQ"]].price
        price_tqqq = self.securities[self.symbols["TQQQ"]].price

        rsi_qqq = self.indicators[f"QQQ_RSI_{self.rsi_period}_day"].current.value
        rsi_spy = self.indicators[f"SPY_RSI_{self.rsi_period}_day"].current.value
        rsi_tqqq = self.indicators[f"TQQQ_RSI_{self.rsi_period}_day"].current.value
        rsi_sqqq = self.indicators[f"SQQQ_RSI_{self.rsi_period}_day"].current.value
        rsi_uvxy = self.indicators[f"UVXY_RSI_{self.rsi_period}_day"].current.value

        sma_spy_200 = self.indicators["SPY_SMA200"].current.value
        sma_qqq_20 = self.indicators["QQQ_SMA20"].current.value
        sma_tqqq_20 = self.indicators["TQQQ_SMA20"].current.value

        target_ticker = None

        # Bull regime: SPY above 200-SMA
        if price_spy > sma_spy_200:
            if rsi_qqq > 81:
                target_ticker = "UVXY"
            elif rsi_spy > 80:
                target_ticker = "UVXY"
            else:
                target_ticker = "TQQQ"
        else:
            # Bear regime: SPY below 200-SMA
            if rsi_tqqq < 30:
                target_ticker = "TECL"
            elif rsi_spy < 30:
                target_ticker = "SPXL"
            elif rsi_uvxy > 74:
                if rsi_uvxy > 84:
                    if price_qqq > sma_qqq_20:
                        if rsi_sqqq < 31:
                            target_ticker = "TECS"
                        else:
                            target_ticker = "TECL"
                    else:
                        target_ticker = self.get_max_rsi_asset(
                            ["TECS", "BSV"], self.rsi_period,
                        )
                else:
                    target_ticker = "UVXY"
            else:
                if price_tqqq > sma_tqqq_20:
                    if rsi_sqqq < 34:
                        target_ticker = "TECS"
                    else:
                        target_ticker = "TECL"
                else:
                    target_ticker = self.get_max_rsi_asset(
                        ["TECS", "BSV"], self.rsi_period,
                    )

        if target_ticker:
            self.set_holdings(
                self.symbols[target_ticker], 1.0,
                liquidate_existing_holdings=True,
            )

    def get_max_rsi_asset(self, ticker_list, rsi_days):
        best_ticker = None
        highest_rsi = -1
        for ticker in ticker_list:
            rsi_val = (
                self.indicators[f"{ticker}_RSI_{rsi_days}_day"]
                .current.value
            )
            if rsi_val > highest_rsi:
                highest_rsi = rsi_val
                best_ticker = ticker
        return best_ticker
