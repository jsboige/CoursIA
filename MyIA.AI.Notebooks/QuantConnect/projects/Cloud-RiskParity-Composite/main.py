# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class RiskParityComposite(QCAlgorithm):
    """
    Risk Parity Composite v4 — Cloud-native QuantBook

    Multi-asset tactical rotation using SMA200 + 6m momentum dual filter.
    Equal weight among trend-positive assets, monthly rebalance.
    Based on AQR Trend-Following methodology (Hurst, Ooi, Pedersen 2014).
    """

    def initialize(self):
        self.set_start_date(2014, 1, 1)
        self.set_end_date(2025, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(
            BrokerageName.INTERACTIVE_BROKERS_BROKERAGE,
            AccountType.MARGIN
        )

        self.tickers = ["SPY", "TLT", "GLD", "EFA", "EEM", "DBC"]
        self.symbols = {}
        self.sma200 = {}
        for ticker in self.tickers:
            sec = self.add_equity(ticker, Resolution.DAILY)
            sec.set_leverage(2.0)
            self.symbols[ticker] = sec.symbol
            self.sma200[ticker] = self.SMA(sec.symbol, 200, Resolution.DAILY)

        self.rebalance_days = int(self.get_parameter("rebalance_days", 30))
        self.last_rebalance = self.time

        self.set_benchmark("SPY")
        self.set_warm_up(252, Resolution.DAILY)

    def on_data(self, data):
        if self.is_warming_up:
            return

        if (self.time - self.last_rebalance).days < self.rebalance_days:
            return

        # Dual filter: SMA200 + 6m momentum
        long_set = set()
        for ticker in self.tickers:
            symbol = self.symbols[ticker]
            sma = self.sma200[ticker]
            if not sma.is_ready:
                continue

            price = self.securities[symbol].price
            if price <= sma.current.value:
                continue

            # 6m momentum check
            try:
                history = self.history(symbol, 126, Resolution.DAILY)
                if len(history) < 30:
                    continue
                closes = history['close']
                mom_6m = (closes.iloc[-1] / closes.iloc[0]) - 1
                if mom_6m > 0:
                    long_set.add(ticker)
            except Exception:
                continue

        if not long_set:
            # All cash if no asset qualifies
            for ticker in self.tickers:
                self.set_holdings(self.symbols[ticker], 0)
            self.last_rebalance = self.time
            return

        # Equal weight allocation
        weight = 1.0 / len(long_set)
        for ticker in self.tickers:
            symbol = self.symbols[ticker]
            if ticker in long_set:
                self.set_holdings(symbol, weight)
            else:
                self.set_holdings(symbol, 0)

        self.last_rebalance = self.time

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"RISK PARITY v4: Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
