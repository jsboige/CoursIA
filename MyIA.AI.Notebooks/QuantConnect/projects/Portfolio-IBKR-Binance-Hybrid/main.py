# region imports
from AlgorithmImports import *
# endregion

class PortfolioHybridIBKRBinance(QCAlgorithm):
    """Portfolio Hybride IBKR (50%) + Binance (50%).

    Phase 1 skeleton — signal aggregation from sub-strategies.
    Phase 2 will implement full backtest with walk-forward.
    """

    def initialize(self):
        self.set_start_date(2020, 1, 1)
        self.set_end_date(2025, 6, 1)
        self.set_cash(100000)

        # Rebalancing
        self.rebalance_freq = 30  # monthly
        self.days_since_rebalance = 0

        # IBKR sleeve (equities)
        self.ibkr_tickers = ["SPY", "IEF", "GLD", "XLP", "XLK", "XLF", "XLE"]
        self.ibkr_symbols = {}
        for ticker in self.ibkr_tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            self.ibkr_symbols[ticker] = equity.symbol

        # Binance sleeve (crypto)
        self.crypto_tickers = ["BTCUSDT", "ETHUSDT"]
        self.crypto_symbols = {}
        for ticker in self.crypto_tickers:
            crypto = self.add_crypto(ticker, Resolution.DAILY, Market.BINANCE)
            self.crypto_symbols[ticker] = crypto.symbol

        # Schedule rebalancing
        self.schedule.on(
            self.date_rules.month_start(),
            self.time_rules.at(9, 31),
            self.rebalance
        )

    def rebalance(self):
        # Placeholder for Phase 2 — equal weight within sleeves
        ibkr_weight = 0.50 / len(self.ibkr_symbols)
        for ticker, symbol in self.ibkr_symbols.items():
            self.set_holdings(symbol, ibkr_weight)

        crypto_weight = 0.50 / len(self.crypto_symbols)
        for ticker, symbol in self.crypto_symbols.items():
            self.set_holdings(symbol, crypto_weight)

    def on_data(self, data):
        pass
