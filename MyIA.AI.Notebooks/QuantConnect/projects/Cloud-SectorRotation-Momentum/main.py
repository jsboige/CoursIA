# region imports
from AlgorithmImports import *
# endregion


class SectorRotationMomentum(QCAlgorithm):
    """
    v4 — Momentum-Weighted Multi-Asset Trend Following.

    Universe: 5 diversified ETFs (QQQ, SPY, EFA, GLD, IWM).
    Signal: Price > SMA200 AND 6-month momentum > 0 (dual filter).
    Allocation: Momentum-weighted (proportional to ROC score).
    Defensive: If no asset qualifies, hold SHY.
    Rebalance: Monthly (21 trading days).
    """

    def initialize(self):
        self.set_start_date(2014, 1, 1)
        self.set_end_date(2025, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(
            BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN
        )

        # Universe: equity growth, broad, intl, gold, small cap
        self.tickers = ["QQQ", "SPY", "EFA", "GLD", "IWM"]
        self.sma_dict = {}

        for ticker in self.tickers:
            symbol = self.add_equity(ticker, Resolution.DAILY).symbol
            self.sma_dict[ticker] = self.sma(symbol, 200, Resolution.DAILY)

        self.shy = self.add_equity("SHY", Resolution.DAILY).symbol

        self.momentum_lookback = 126
        self.rebalance_days = 21
        self.days_since_rebalance = 0

        self.set_benchmark("SPY")
        self.set_warm_up(200, Resolution.DAILY)

    def on_data(self, data):
        if self.is_warming_up:
            return

        self.days_since_rebalance += 1
        if self.days_since_rebalance < self.rebalance_days:
            return
        self.days_since_rebalance = 0

        qualified = {}
        for ticker in self.tickers:
            symbol = Symbol.create(ticker, SecurityType.EQUITY, Market.USA)
            if symbol not in data or data[symbol] is None:
                continue

            price = self.securities[symbol].price
            sma_val = self.sma_dict[ticker].current.value

            if price <= sma_val:
                continue

            history = self.history([symbol], self.momentum_lookback, Resolution.DAILY)
            if history is None or history.empty:
                continue
            try:
                closes = history.loc[symbol, "close"]
            except KeyError:
                continue
            if len(closes) < self.momentum_lookback:
                continue
            momentum = (closes.iloc[-1] / closes.iloc[0]) - 1.0
            if momentum > 0:
                qualified[ticker] = momentum

        if not qualified:
            self._go_defensive()
            return

        # Momentum-weighted allocation
        total_momentum = sum(qualified.values())
        weights = {t: m / total_momentum for t, m in qualified.items()}

        for ticker in self.tickers:
            symbol = Symbol.create(ticker, SecurityType.EQUITY, Market.USA)
            if symbol in self.portfolio and self.portfolio[symbol].invested:
                if ticker not in weights:
                    self.liquidate(symbol)

        if self.shy in self.portfolio and self.portfolio[self.shy].invested:
            self.liquidate(self.shy)

        for ticker, weight in weights.items():
            symbol = Symbol.create(ticker, SecurityType.EQUITY, Market.USA)
            self.set_holdings(symbol, weight)

        top = max(weights, key=weights.get)
        self.log(
            f"REBALANCE: {len(qualified)} assets | "
            f"Top: {top} ({weights[top]:.1%}) | "
            f"Total mom: {total_momentum:.2%}"
        )

    def _go_defensive(self):
        for ticker in self.tickers:
            symbol = Symbol.create(ticker, SecurityType.EQUITY, Market.USA)
            if symbol in self.portfolio and self.portfolio[symbol].invested:
                self.liquidate(symbol)
        if self.shy in self.portfolio and not self.portfolio[self.shy].invested:
            self.set_holdings(self.shy, 1.0)
        self.log("REBALANCE: No trend -> SHY")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(
            f"MOM-WEIGHTED TREND v4: Final=${final:,.2f}, "
            f"Return={(final - 100000) / 100000:.2%}"
        )
